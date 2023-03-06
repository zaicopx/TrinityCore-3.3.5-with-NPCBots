#include "bot_ai.h"
#include "botdatamgr.h"
#include "botmgr.h"
#include "botspell.h"
#include "Containers.h"
#include "Creature.h"
#include "DatabaseEnv.h"
#include "GroupMgr.h"
#include "Item.h"
#include "Log.h"
#include "Map.h"
#include "MapManager.h"
#include "ObjectMgr.h"
#include "StringConvert.h"
#include "WorldDatabase.h"
/*
Npc Bot Data Manager by Trickerer (onlysuffering@gmail.com)
NpcBots DB Data management
%Complete: ???
*/

typedef std::unordered_map<uint32 /*entry*/, NpcBotData*> NpcBotDataMap;
typedef std::unordered_map<uint32 /*entry*/, NpcBotAppearanceData*> NpcBotAppearanceDataMap;
typedef std::unordered_map<uint32 /*entry*/, NpcBotExtras*> NpcBotExtrasMap;
typedef std::unordered_map<uint32 /*entry*/, NpcBotTransmogData*> NpcBotTransmogDataMap;
NpcBotDataMap _botsData;
NpcBotAppearanceDataMap _botsAppearanceData;
NpcBotExtrasMap _botsExtras;
NpcBotTransmogDataMap _botsTransmogData;
NpcBotRegistry _existingBots;

CreatureTemplateContainer _botsWanderCreatureTemplates;
std::unordered_map<uint32, EquipmentInfo const*> _botsWanderCreatureEquipmentTemplates;

bool allBotsLoaded = false;

class BotTravelGraph
{
public:
    ~BotTravelGraph() {
        //order
        Tops.clear();
        Nodes.clear();
    }

    struct BotTravelNode : public WorldLocation
    {
        BotTravelNode(uint32 _mapId = MAPID_INVALID, float x = 0.f, float y = 0.f, float z = 0.f, float o = 0.f,
            uint32 _id = 0, uint32 _zoneId = 0, uint8 _minlevel = 0, uint8 _maxlevel = 0, std::string const& _name = "unknown") :
            WorldLocation(_mapId, x, y, z, o), id(_id), zoneId(_zoneId), minlevel(_minlevel), maxlevel(_maxlevel), name(_name) {}
        BotTravelNode(uint32 _mapId, Position const& pos, uint32 _id, uint32 _zoneId, uint8 _minlevel, uint8 _maxlevel, std::string const& _name) :
            WorldLocation(_mapId, pos), id(_id), zoneId(_zoneId), minlevel(_minlevel), maxlevel(_maxlevel), name(_name) {}

        uint32 id;
        uint32 zoneId;
        uint8 minlevel;
        uint8 maxlevel;
        std::string name;

        std::vector<BotTravelNode*> connections;
    };

    std::unordered_map<uint32 /*mapId*/, std::unordered_map<uint32, BotTravelNode>> Nodes;
    std::vector<BotTravelNode*> Tops; // single connection nodes

    // debug
    static constexpr size_t sizeofNode = sizeof(BotTravelNode);
} static WanderMap;

void FillWanderMap()
{
    using NodeType = BotTravelGraph::BotTravelNode;

    const float NODE_CONNECTION_DIST_MAX = 1400.f;

    const std::array wanderMapIds{ 0u, 1u };

    TC_LOG_INFO("server.loading", "Generating bot wander map...");

    uint32 botoldMSTime = getMSTime();

    QueryResult wres = WorldDatabase.Query("SELECT id, mapid, zoneid, x, y, z, o, name FROM creature_wander_nodes");
    if (!wres)
    {
        TC_LOG_FATAL("server.loading", "Failed to load wander points: table `creature_wander_nodes` is empty!");
        ASSERT(false);
    }

    do
    {
        Field* fields = wres->Fetch();
        uint32 index = 0;

        uint32 id             = fields[  index].GetUInt32();
        uint32 mapid          = fields[++index].GetUInt16();

        if (std::find(std::cbegin(wanderMapIds), std::cend(wanderMapIds), mapid) == wanderMapIds.cend())
            continue;

        uint32 zoneId         = fields[++index].GetUInt32();

        auto [lvlmin, lvlmax] = BotDataMgr::GetZoneLevels(zoneId);
        if (lvlmin == 0 || lvlmax == 0)
            continue;

        float x          = fields[++index].GetFloat();
        float y          = fields[++index].GetFloat();
        float z          = fields[++index].GetFloat();
        float o          = fields[++index].GetFloat();
        std::string name = fields[++index].GetString();

        WanderMap.Nodes[mapid][id] = NodeType(mapid, x, y, z, o, id, zoneId, lvlmin, lvlmax, name);

    } while (wres->NextRow());

    uint32 total_connections = 0;
    float mindist = 50000.f;
    float maxdist = 0.f;
    for (decltype(WanderMap.Nodes)::value_type& mapNodes1 : WanderMap.Nodes)
    {
        for (decltype(mapNodes1.second)::iterator it = mapNodes1.second.begin(); it != mapNodes1.second.end();)
        {
            for (auto& nodepair2 : WanderMap.Nodes.at(it->second.m_mapId))
            {
                if (it->first == nodepair2.first)
                    continue;

                float dist2d = it->second.GetExactDist2d(nodepair2.second);
                if (dist2d < NODE_CONNECTION_DIST_MAX)
                {
                    if (dist2d < mindist)
                        mindist = dist2d;
                    if (dist2d > maxdist)
                        maxdist = dist2d;

                    it->second.connections.push_back(&nodepair2.second);
                    if (nodepair2.second.connections.empty() ||
                        std::find(std::cbegin(nodepair2.second.connections), std::cend(nodepair2.second.connections), &it->second) == nodepair2.second.connections.cend())
                        ++total_connections;
                }
            }

            if (it->second.connections.empty())
                it = mapNodes1.second.erase(it);
            else
            {
                if (it->second.connections.size() == 1u)
                {
                    WanderMap.Tops.push_back(&it->second);
                    if (it->second.connections.front()->connections.size() == 1)
                        TC_LOG_INFO("server.loading", "Node pair %u-%u is isolated!", it->second.id, it->second.connections.front()->id);
                }
                ++it;
            }
        }
    }

    uint32 total_nodes = 0;
    for (auto const& vt : WanderMap.Nodes)
    {
        total_nodes += vt.second.size();
        if (vt.second.empty())
        {
            TC_LOG_FATAL("server.loading", "Failed to load wander points: no game_tele points added to map %u!", vt.first);
            ASSERT(false);
        }
    }

    TC_LOG_INFO("server.loading", ">> Generated %u bot wander nodes on %u maps (total %u ribs, %u tops) in %u ms",
        total_nodes, uint32(WanderMap.Nodes.size()), total_connections, uint32(WanderMap.Tops.size()), GetMSTimeDiffToNow(botoldMSTime));
    TC_LOG_INFO("server.loading", "Nodes distances: min = %.3f, max = %.3f", mindist, maxdist);
}

std::shared_mutex* BotDataMgr::GetLock()
{
    static std::shared_mutex _lock;
    return &_lock;
}

bool BotDataMgr::AllBotsLoaded()
{
    return allBotsLoaded;
}

void BotDataMgr::LoadNpcBots(bool spawn)
{
    if (allBotsLoaded)
        return;

    TC_LOG_INFO("server.loading", "Starting NpcBot system...");

    GenerateBotCustomSpells();
    FillWanderMap();

    uint32 botoldMSTime = getMSTime();

    Field* field;
    uint8 index;

    //                                                      1       2     3     4     5          6
    QueryResult result = WorldDatabase.Query("SELECT entry, gender, skin, face, hair, haircolor, features FROM creature_template_npcbot_appearance");
    if (result)
    {
        do
        {
            field = result->Fetch();
            index = 0;
            uint32 entry = field[  index].GetUInt32();

            NpcBotAppearanceData* appearanceData = new NpcBotAppearanceData();
            appearanceData->gender =    field[++index].GetUInt8();
            appearanceData->skin =      field[++index].GetUInt8();
            appearanceData->face =      field[++index].GetUInt8();
            appearanceData->hair =      field[++index].GetUInt8();
            appearanceData->haircolor = field[++index].GetUInt8();
            appearanceData->features =  field[++index].GetUInt8();

            _botsAppearanceData[entry] = appearanceData;

        } while (result->NextRow());

        TC_LOG_INFO("server.loading", ">> Bot appearance data loaded");
    }
    else
        TC_LOG_INFO("server.loading", ">> Bots appearance data is not loaded. Table `creature_template_npcbot_appearance` is empty!");

    //                                          1      2
    result = WorldDatabase.Query("SELECT entry, class, race FROM creature_template_npcbot_extras");
    if (result)
    {
        do
        {
            field = result->Fetch();
            index = 0;
            uint32 entry =      field[  index].GetUInt32();

            NpcBotExtras* extras = new NpcBotExtras();
            extras->bclass =    field[++index].GetUInt8();
            extras->race =      field[++index].GetUInt8();

            _botsExtras[entry] = extras;

        } while (result->NextRow());

        TC_LOG_INFO("server.loading", ">> Bot race data loaded");
    }
    else
        TC_LOG_INFO("server.loading", ">> Bots race data is not loaded. Table `creature_template_npcbot_extras` is empty!");

    //                                              1     2        3
    result = CharacterDatabase.Query("SELECT entry, slot, item_id, fake_id FROM characters_npcbot_transmog");
    if (result)
    {
        do
        {
            field = result->Fetch();
            index = 0;
            uint32 entry =          field[  index].GetUInt32();

            if (_botsTransmogData.count(entry) == 0)
                _botsTransmogData[entry] = new NpcBotTransmogData();

            //load data
            uint8 slot =            field[++index].GetUInt8();
            uint32 item_id =        field[++index].GetUInt32();
            uint32 fake_id =        field[++index].GetUInt32();

            _botsTransmogData[entry]->transmogs[slot] = { item_id, fake_id };

        } while (result->NextRow());

        TC_LOG_INFO("server.loading", ">> Bot transmog data loaded");
    }
    else
        TC_LOG_INFO("server.loading", ">> Bots transmog data is not loaded. Table `characters_npcbot_transmog` is empty!");

    //                                       0      1      2      3     4        5          6          7          8          9               10          11          12         13
    result = CharacterDatabase.Query("SELECT entry, owner, roles, spec, faction, equipMhEx, equipOhEx, equipRhEx, equipHead, equipShoulders, equipChest, equipWaist, equipLegs, equipFeet,"
    //   14          15          16         17         18            19            20             21             22         23
        "equipWrist, equipHands, equipBack, equipBody, equipFinger1, equipFinger2, equipTrinket1, equipTrinket2, equipNeck, spells_disabled FROM characters_npcbot");

    if (!result)
    {
        TC_LOG_INFO("server.loading", ">> Loaded 0 npcbots. Table `characters_npcbot` is empty!");
        allBotsLoaded = true;
        return;
    }

    uint32 botcounter = 0;
    uint32 datacounter = 0;
    std::set<uint32> botgrids;
    QueryResult infores;
    CreatureTemplate const* proto;
    NpcBotData* botData;
    std::list<uint32> entryList;

    do
    {
        field = result->Fetch();
        index = 0;
        uint32 entry =          field[  index].GetUInt32();

        //load data
        botData = new NpcBotData(0, 0);
        botData->owner =        field[++index].GetUInt32();
        botData->roles =        field[++index].GetUInt32();
        botData->spec =         field[++index].GetUInt8();
        botData->faction =      field[++index].GetUInt32();

        for (uint8 i = BOT_SLOT_MAINHAND; i != BOT_INVENTORY_SIZE; ++i)
            botData->equips[i] = field[++index].GetUInt32();

        if (char const* disabled_spells_str = field[++index].GetCString())
        {
            std::vector<std::string_view> tok = Trinity::Tokenize(disabled_spells_str, ' ', false);
            for (std::vector<std::string_view>::size_type i = 0; i != tok.size(); ++i)
                botData->disabled_spells.insert(*(Trinity::StringTo<uint32>(tok[i])));
        }

        entryList.push_back(entry);
        _botsData[entry] = botData;
        ++datacounter;

    } while (result->NextRow());

    TC_LOG_INFO("server.loading", ">> Loaded %u bot data entries", datacounter);

    if (!spawn)
    {
        allBotsLoaded = true;
        return;
    }

    for (std::list<uint32>::const_iterator itr = entryList.begin(); itr != entryList.end(); ++itr)
    {
        uint32 entry = *itr;
        proto = sObjectMgr->GetCreatureTemplate(entry);
        if (!proto)
        {
            TC_LOG_ERROR("server.loading", "Cannot find creature_template entry for npcbot (id: %u)!", entry);
            continue;
        }
        //                                     1     2    3           4            5           6
        infores = WorldDatabase.PQuery("SELECT guid, map, position_x, position_y"/*, position_z, orientation*/" FROM creature WHERE id = %u", entry);
        if (!infores)
        {
            TC_LOG_ERROR("server.loading", "Cannot spawn npcbot %s (id: %u), not found in `creature` table!", proto->Name.c_str(), entry);
            continue;
        }

        field = infores->Fetch();
        uint32 tableGuid = field[0].GetUInt32();
        uint32 mapId = uint32(field[1].GetUInt16());
        float pos_x = field[2].GetFloat();
        float pos_y = field[3].GetFloat();
        //float pos_z = field[4].GetFloat();
        //float ori = field[5].GetFloat();

        CellCoord c = Trinity::ComputeCellCoord(pos_x, pos_y);
        GridCoord g = Trinity::ComputeGridCoord(pos_x, pos_y);
        ASSERT(c.IsCoordValid(), "Invalid Cell coord!");
        ASSERT(g.IsCoordValid(), "Invalid Grid coord!");
        Map* map = sMapMgr->CreateBaseMap(mapId);
        map->LoadGrid(pos_x, pos_y);

        ObjectGuid Guid(HighGuid::Unit, entry, tableGuid);
        TC_LOG_DEBUG("server.loading", "bot %u: spawnId %u, full %s", entry, tableGuid, Guid.ToString().c_str());
        Creature* bot = map->GetCreature(Guid);
        if (!bot) //not in map, use storage
        {
            //TC_LOG_DEBUG("server.loading", "bot %u: spawnId %u, is not in map on load", entry, tableGuid);
            typedef Map::CreatureBySpawnIdContainer::const_iterator SpawnIter;
            std::pair<SpawnIter, SpawnIter> creBounds = map->GetCreatureBySpawnIdStore().equal_range(tableGuid);
            if (creBounds.first == creBounds.second)
            {
                TC_LOG_ERROR("server.loading", "bot %u is not in spawns list, consider re-spawning it!", entry);
                continue;
            }
            bot = creBounds.first->second;
        }
        ASSERT(bot);
        if (!bot->FindMap())
            TC_LOG_ERROR("server.loading", "bot %u is not in map!", entry);
        if (!bot->IsInWorld())
            TC_LOG_ERROR("server.loading", "bot %u is not in world!", entry);
        if (!bot->IsAlive())
        {
            TC_LOG_ERROR("server.loading", "bot %u is dead, respawning!", entry);
            bot->Respawn();
        }

        TC_LOG_DEBUG("server.loading", ">> Spawned npcbot %s (id: %u, map: %u, grid: %u, cell: %u)", proto->Name.c_str(), entry, mapId, g.GetId(), c.GetId());
        botgrids.insert(g.GetId());
        ++botcounter;
    }

    TC_LOG_INFO("server.loading", ">> Spawned %u npcbot(s) within %u grid(s) in %u ms", botcounter, uint32(botgrids.size()), GetMSTimeDiffToNow(botoldMSTime));

    allBotsLoaded = true;

    GenerateWanderingBots();
}

void BotDataMgr::LoadNpcBotGroupData()
{
    TC_LOG_INFO("server.loading", "Loading NPCBot Group members...");

    uint32 oldMSTime = getMSTime();

    CharacterDatabase.DirectExecute("DELETE FROM characters_npcbot_group_member WHERE guid NOT IN (SELECT guid FROM `groups`)");
    CharacterDatabase.DirectExecute("DELETE FROM characters_npcbot_group_member WHERE entry NOT IN (SELECT entry FROM characters_npcbot)");

    //                                                   0     1      2            3         4
    QueryResult result = CharacterDatabase.Query("SELECT guid, entry, memberFlags, subgroup, roles FROM characters_npcbot_group_member ORDER BY guid");
    if (!result)
    {
        TC_LOG_INFO("server.loading", ">> Loaded 0 NPCBot group members. DB table `characters_npcbot_group_member` is empty!");
        return;
    }

    uint32 count = 0;
    do
    {
        Field* fields = result->Fetch();

        uint32 creature_id = fields[1].GetUInt32();
        if (!SelectNpcBotExtras(creature_id))
        {
            TC_LOG_WARN("server.loading", "Table `characters_npcbot_group_member` contains non-NPCBot creature %u which will not be loaded!", creature_id);
            continue;
        }

        if (Group* group = sGroupMgr->GetGroupByDbStoreId(fields[0].GetUInt32()))
            group->LoadCreatureMemberFromDB(creature_id, fields[2].GetUInt8(), fields[3].GetUInt8(), fields[4].GetUInt8());
        else
            TC_LOG_ERROR("misc", "BotDataMgr::LoadNpcBotGroupData: Consistency failed, can't find group (storage id: %u)", fields[0].GetUInt32());

        ++count;

    } while (result->NextRow());

    TC_LOG_INFO("server.loading", ">> Loaded %u NPCBot group members in %u ms", count, GetMSTimeDiffToNow(oldMSTime));
}

void BotDataMgr::GenerateWanderingBots()
{
    const uint32 WANDERING_BOTS_COUNT = 3;

    TC_LOG_INFO("server.loading", "Spawning wandering bots...");

    uint32 oldMSTime = getMSTime();

    if (int32(_botsExtras.size() - _existingBots.size()) < int32(WANDERING_BOTS_COUNT))
    {
        TC_LOG_FATAL("server.loading", "Trying to generate %u bots but only %i out of %u bots aren't spawned. Aborting!",
            WANDERING_BOTS_COUNT, int32(_botsExtras.size() - _existingBots.size()), uint32(_botsExtras.size()));
        ASSERT(false);
    }

    std::vector<uint8> allowed_classes;
    allowed_classes.reserve(BOT_CLASS_END);
    for (uint8 c = BOT_CLASS_WARRIOR; c < BOT_CLASS_END; ++c)
        if (BotMgr::IsClassEnabled(c))
            allowed_classes.push_back(c);

    uint32 bot_id = BOT_ENTRY_CREATE_BEGIN - 1;
    QueryResult result = CharacterDatabase.PQuery("SELECT value FROM worldstates WHERE entry = %u", uint32(BOT_GIVER_ENTRY));
    if (!result)
    {
        TC_LOG_WARN("server.loading", "Next bot id for autogeneration is not found! Resetting! (client cache may interfere with names)");
        for (uint32 bot_cid : GetExistingNPCBotIds())
            if (bot_cid > bot_id)
                bot_id = bot_cid;
        CharacterDatabase.DirectPExecute("INSERT INTO worldstates (entry, value, comment) VALUES (%u, %u, '%s')",
            uint32(BOT_GIVER_ENTRY), bot_id, "NPCBOTS MOD - last autogenerated bot entry");
    }
    else
        bot_id = result->Fetch()[0].GetUInt32();

    decltype(bot_id) bot_id_start = bot_id;
    ASSERT(bot_id_start > BOT_ENTRY_BEGIN);

    CreatureTemplateContainer const& all_templates = sObjectMgr->GetCreatureTemplates();
    std::vector<uint32> clonedIds;
    clonedIds.reserve(WANDERING_BOTS_COUNT);

    auto find_bot_creature_template_by_botclass = [&clonedIds](uint8 b_class, uint32 max_entry) -> CreatureTemplate const* {
        std::vector<CreatureTemplate const*> valid_templates;
        for (uint32 i = BOT_ENTRY_BEGIN; i < max_entry; ++i)
        {
            if (NpcBotExtras const* templateExtras = SelectNpcBotExtras(i))
            {
                if (templateExtras->bclass == b_class &&
                    std::find(std::cbegin(clonedIds), std::cend(clonedIds), i) == clonedIds.cend() &&
                    !BotDataMgr::FindBot(i))
                    valid_templates.push_back(sObjectMgr->GetCreatureTemplate(i));
            }
        }
        return valid_templates.empty() ? nullptr : Trinity::Containers::SelectRandomContainerElement(valid_templates);
    };

    std::set<uint32> botgrids;
    for (int32 i = 0; i < int32(WANDERING_BOTS_COUNT); ++i) // i is unused as value
    {
        while (all_templates.find(++bot_id) != all_templates.end()) {}

        uint8 bot_class = Trinity::Containers::SelectRandomContainerElement(allowed_classes);
        CreatureTemplate const* orig_template = find_bot_creature_template_by_botclass(bot_class, bot_id_start);
        if (!orig_template)
        {
            //try again
            --i;
            --bot_id;
            continue;
        }

        CreatureTemplate& bot_template = _botsWanderCreatureTemplates[bot_id];
        //copy all fields
        //pointers to non-const objects: QueryData[TOTAL_LOCALES]
        bot_template = *orig_template;
        bot_template.Entry = bot_id;
        //bot_template.Name = bot_template.Name;
        bot_template.Title = "";
        //possibly need to override whole array (and pointer)
        bot_template.InitializeQueryData();

        NpcBotExtras const* orig_extras = SelectNpcBotExtras(orig_template->Entry);
        ASSERT_NOTNULL(orig_extras);
        ChrRacesEntry const* rentry = sChrRacesStore.LookupEntry(orig_extras->race);

        NpcBotData* bot_data = new NpcBotData(bot_ai::DefaultRolesForClass(bot_class), rentry ? rentry->FactionID : 14, bot_ai::DefaultSpecForClass(bot_class));
        _botsData[bot_id] = bot_data;
        NpcBotExtras* bot_extras = new NpcBotExtras();
        ASSERT_NOTNULL(bot_extras);
        bot_extras->bclass = bot_class;
        bot_extras->race = orig_extras->race;
        _botsExtras[bot_id] = bot_extras;
        if (NpcBotAppearanceData const* orig_apdata = SelectNpcBotAppearance(orig_template->Entry))
        {
            NpcBotAppearanceData* bot_apdata = new NpcBotAppearanceData();
            bot_apdata->face = orig_apdata->face;
            bot_apdata->features = orig_apdata->features;
            bot_apdata->gender = orig_apdata->gender;
            bot_apdata->hair = orig_apdata->hair;
            bot_apdata->haircolor = orig_apdata->haircolor;
            bot_apdata->skin = orig_apdata->skin;
            _botsAppearanceData[bot_id] = bot_apdata;
        }
        int8 beqId = 1;
        _botsWanderCreatureEquipmentTemplates[bot_id] = sObjectMgr->GetEquipmentInfo(orig_template->Entry, beqId);

        clonedIds.push_back(orig_template->Entry);

        //We do not create CreatureData for generated bots

        auto const& spair = Trinity::Containers::SelectRandomContainerElement(Trinity::Containers::SelectRandomContainerElement(WanderMap.Nodes).second);
        auto const& spawnLocation = spair.second;

        CellCoord c = Trinity::ComputeCellCoord(spawnLocation.m_positionX, spawnLocation.m_positionY);
        GridCoord g = Trinity::ComputeGridCoord(spawnLocation.m_positionX, spawnLocation.m_positionY);
        ASSERT(c.IsCoordValid(), "Invalid Cell coord!");
        ASSERT(g.IsCoordValid(), "Invalid Grid coord!");
        Map* map = sMapMgr->CreateBaseMap(spawnLocation.m_mapId);
        map->LoadGrid(spawnLocation.m_positionX, spawnLocation.m_positionY);
        ASSERT(!map->Instanceable(), map->GetDebugInfo().c_str());

        TC_LOG_INFO("server.loading", "Spawning wandering bot: %s (%u) class %u race %u fac %u, location: mapId %u %s (%s)",
            bot_template.Name.c_str(), bot_id, uint8(bot_extras->bclass), uint32(bot_extras->race), bot_data->faction,
            spawnLocation.m_mapId, spawnLocation.ToString().c_str(), spawnLocation.name.c_str());
        Position spos;
        spos.Relocate(spawnLocation.m_positionX, spawnLocation.m_positionY, spawnLocation.m_positionZ, spawnLocation.GetOrientation());
        Creature* bot = new Creature();
        if (!bot->Create(map->GenerateLowGuid<HighGuid::Unit>(), map, PHASEMASK_NORMAL, bot_id, spos))
        {
            delete bot;
            TC_LOG_FATAL("server.loading", "Creature is not created!");
            ASSERT(false);
        }
        if (!bot->LoadBotCreatureFromDB(0, map, true, true, bot_id, &spos))
        {
            delete bot;
            TC_LOG_FATAL("server.loading", "Cannot load npcbot from DB!");
            ASSERT(false);
        }
        bot->GetBotAI()->SetTravelNodeCur(spawnLocation.id);

        botgrids.insert(g.GetId());

        //TC_LOG_INFO("server.loading", "Spawned wandering bot %u at: %s", bot_id, bot->ToString().c_str());
    }

    CharacterDatabase.PExecute("UPDATE worldstates SET value = %u WHERE entry = %u", bot_id, uint32(BOT_GIVER_ENTRY));

    TC_LOG_INFO("server.loading", ">> Spawned %u wandering bots in %u grids in %u ms",
        uint32(_botsWanderCreatureTemplates.size()), uint32(botgrids.size()), GetMSTimeDiffToNow(oldMSTime));
}

CreatureTemplate const* BotDataMgr::GetBotExtraCreatureTemplate(uint32 entry)
{
    CreatureTemplateContainer::const_iterator cit = _botsWanderCreatureTemplates.find(entry);
    return cit == _botsWanderCreatureTemplates.end() ? nullptr : &cit->second;
}

EquipmentInfo const* BotDataMgr::GetBotEquipmentInfo(uint32 entry)
{
    decltype(_botsWanderCreatureEquipmentTemplates)::const_iterator cit = _botsWanderCreatureEquipmentTemplates.find(entry);
    if (cit == _botsWanderCreatureEquipmentTemplates.cend())
    {
        static int8 eqId = 1;
        return sObjectMgr->GetEquipmentInfo(entry, eqId);
    }
    else
        return cit->second;
}

void BotDataMgr::AddNpcBotData(uint32 entry, uint32 roles, uint8 spec, uint32 faction)
{
    //botData must be allocated explicitly
    NpcBotDataMap::iterator itr = _botsData.find(entry);
    if (itr == _botsData.end())
    {
        NpcBotData* botData = new NpcBotData(roles, faction, spec);
        _botsData[entry] = botData;

        CharacterDatabasePreparedStatement* bstmt = CharacterDatabase.GetPreparedStatement(CHAR_INS_NPCBOT);
        //"INSERT INTO characters_npcbot (entry, roles, spec, faction) VALUES (?, ?, ?, ?)", CONNECTION_ASYNC);
        bstmt->setUInt32(0, entry);
        bstmt->setUInt32(1, roles);
        bstmt->setUInt8(2, spec);
        bstmt->setUInt32(3, faction);
        CharacterDatabase.Execute(bstmt);

        return;
    }

    TC_LOG_ERROR("sql.sql", "BotMgr::AddNpcBotData(): trying to add new data but entry already exists! entry = %u", entry);
}
NpcBotData const* BotDataMgr::SelectNpcBotData(uint32 entry)
{
    NpcBotDataMap::const_iterator itr = _botsData.find(entry);
    return itr != _botsData.end() ? itr->second : nullptr;
}
void BotDataMgr::UpdateNpcBotData(uint32 entry, NpcBotDataUpdateType updateType, void* data)
{
    NpcBotDataMap::iterator itr = _botsData.find(entry);
    if (itr == _botsData.end())
        return;

    CharacterDatabasePreparedStatement* bstmt;
    switch (updateType)
    {
        case NPCBOT_UPDATE_OWNER:
            if (itr->second->owner == *(uint32*)(data))
                break;
            itr->second->owner = *(uint32*)(data);
            bstmt = CharacterDatabase.GetPreparedStatement(CHAR_UPD_NPCBOT_OWNER);
            //"UPDATE characters_npcbot SET owner = ? WHERE entry = ?", CONNECTION_ASYNC
            bstmt->setUInt32(0, itr->second->owner);
            bstmt->setUInt32(1, entry);
            CharacterDatabase.Execute(bstmt);
            //break; //no break: erase transmogs
        [[fallthrough]];
        case NPCBOT_UPDATE_TRANSMOG_ERASE:
            bstmt = CharacterDatabase.GetPreparedStatement(CHAR_DEL_NPCBOT_TRANSMOG);
            //"DELETE FROM characters_npcbot_transmog WHERE entry = ?", CONNECTION_ASYNC
            bstmt->setUInt32(0, entry);
            CharacterDatabase.Execute(bstmt);
            break;
        case NPCBOT_UPDATE_ROLES:
            itr->second->roles = *(uint32*)(data);
            bstmt = CharacterDatabase.GetPreparedStatement(CHAR_UPD_NPCBOT_ROLES);
            //"UPDATE character_npcbot SET roles = ? WHERE entry = ?", CONNECTION_ASYNC
            bstmt->setUInt32(0, itr->second->roles);
            bstmt->setUInt32(1, entry);
            CharacterDatabase.Execute(bstmt);
            break;
        case NPCBOT_UPDATE_SPEC:
            itr->second->spec = *(uint8*)(data);
            bstmt = CharacterDatabase.GetPreparedStatement(CHAR_UPD_NPCBOT_SPEC);
            //"UPDATE characters_npcbot SET spec = ? WHERE entry = ?", CONNECTION_ASYNCH
            bstmt->setUInt8(0, itr->second->spec);
            bstmt->setUInt32(1, entry);
            CharacterDatabase.Execute(bstmt);
            break;
        case NPCBOT_UPDATE_FACTION:
            itr->second->faction = *(uint32*)(data);
            bstmt = CharacterDatabase.GetPreparedStatement(CHAR_UPD_NPCBOT_FACTION);
            //"UPDATE characters_npcbot SET faction = ? WHERE entry = ?", CONNECTION_ASYNCH
            bstmt->setUInt32(0, itr->second->faction);
            bstmt->setUInt32(1, entry);
            CharacterDatabase.Execute(bstmt);
            break;
        case NPCBOT_UPDATE_DISABLED_SPELLS:
        {
            NpcBotData::DisabledSpellsContainer const* spells = (NpcBotData::DisabledSpellsContainer const*)(data);
            std::ostringstream ss;
            for (NpcBotData::DisabledSpellsContainer::const_iterator citr = spells->begin(); citr != spells->end(); ++citr)
                ss << (*citr) << ' ';

            bstmt = CharacterDatabase.GetPreparedStatement(CHAR_UPD_NPCBOT_DISABLED_SPELLS);
            //"UPDATE characters_npcbot SET spells_disabled = ? WHERE entry = ?", CONNECTION_ASYNCH
            bstmt->setString(0, ss.str());
            bstmt->setUInt32(1, entry);
            CharacterDatabase.Execute(bstmt);
            break;
        }
        case NPCBOT_UPDATE_EQUIPS:
        {
            Item** items = (Item**)(data);

            EquipmentInfo const* einfo = BotDataMgr::GetBotEquipmentInfo(entry);

            CharacterDatabaseTransaction trans = CharacterDatabase.BeginTransaction();

            bstmt = CharacterDatabase.GetPreparedStatement(CHAR_UPD_NPCBOT_EQUIP);
            //"UPDATE character_npcbot SET equipMhEx = ?, equipOhEx = ?, equipRhEx = ?, equipHead = ?, equipShoulders = ?, equipChest = ?, equipWaist = ?, equipLegs = ?,
            //equipFeet = ?, equipWrist = ?, equipHands = ?, equipBack = ?, equipBody = ?, equipFinger1 = ?, equipFinger2 = ?, equipTrinket1 = ?, equipTrinket2 = ?, equipNeck = ? WHERE entry = ?", CONNECTION_ASYNC
            CharacterDatabasePreparedStatement* stmt;
            uint8 k;
            for (k = BOT_SLOT_MAINHAND; k != BOT_INVENTORY_SIZE; ++k)
            {
                itr->second->equips[k] = items[k] ? items[k]->GetGUID().GetCounter() : 0;
                if (Item const* botitem = items[k])
                {
                    bool standard = false;
                    for (uint8 i = 0; i != MAX_EQUIPMENT_ITEMS; ++i)
                    {
                        if (einfo->ItemEntry[i] == botitem->GetEntry())
                        {
                            itr->second->equips[k] = 0;
                            bstmt->setUInt32(k, 0);
                            standard = true;
                            break;
                        }
                    }
                    if (standard)
                        continue;

                    uint8 index = 0;
                    stmt = CharacterDatabase.GetPreparedStatement(CHAR_REP_ITEM_INSTANCE);
                    //REPLACE INTO item_instance (itemEntry, owner_guid, creatorGuid, giftCreatorGuid, count, duration, charges, flags, enchantments, randomPropertyId, durability, playedTime, text, guid)
                    //VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)", CONNECTION_ASYNC : 0-13
                    stmt->setUInt32(  index, botitem->GetEntry());
                    stmt->setUInt32(++index, botitem->GetOwnerGUID().GetCounter());
                    stmt->setUInt32(++index, botitem->GetGuidValue(ITEM_FIELD_CREATOR).GetCounter());
                    stmt->setUInt32(++index, botitem->GetGuidValue(ITEM_FIELD_GIFTCREATOR).GetCounter());
                    stmt->setUInt32(++index, botitem->GetCount());
                    stmt->setUInt32(++index, botitem->GetUInt32Value(ITEM_FIELD_DURATION));

                    std::ostringstream ssSpells;
                    for (uint8 i = 0; i < MAX_ITEM_PROTO_SPELLS; ++i)
                        ssSpells << botitem->GetSpellCharges(i) << ' ';
                    stmt->setString(++index, ssSpells.str());

                    stmt->setUInt32(++index, botitem->GetUInt32Value(ITEM_FIELD_FLAGS));

                    std::ostringstream ssEnchants;
                    for (uint8 i = 0; i < MAX_ENCHANTMENT_SLOT; ++i)
                    {
                        ssEnchants << botitem->GetEnchantmentId(EnchantmentSlot(i)) << ' ';
                        ssEnchants << botitem->GetEnchantmentDuration(EnchantmentSlot(i)) << ' ';
                        ssEnchants << botitem->GetEnchantmentCharges(EnchantmentSlot(i)) << ' ';
                    }
                    stmt->setString(++index, ssEnchants.str());

                    stmt->setInt16 (++index, botitem->GetItemRandomPropertyId());
                    stmt->setUInt16(++index, botitem->GetUInt32Value(ITEM_FIELD_DURABILITY));
                    stmt->setUInt32(++index, botitem->GetUInt32Value(ITEM_FIELD_CREATE_PLAYED_TIME));
                    stmt->setString(++index, botitem->GetText());
                    stmt->setUInt32(++index, botitem->GetGUID().GetCounter());

                    trans->Append(stmt);

                    Item::DeleteFromInventoryDB(trans, botitem->GetGUID().GetCounter()); //prevent duplicates

                    bstmt->setUInt32(k, botitem->GetGUID().GetCounter());
                }
                else
                    bstmt->setUInt32(k, uint32(0));
            }

            bstmt->setUInt32(k, entry);
            trans->Append(bstmt);
            CharacterDatabase.CommitTransaction(trans);
            break;
        }
        case NPCBOT_UPDATE_ERASE:
        {
            NpcBotDataMap::iterator bitr = _botsData.find(entry);
            ASSERT(bitr != _botsData.end());
            delete bitr->second;
            _botsData.erase(bitr);
            bstmt = CharacterDatabase.GetPreparedStatement(CHAR_DEL_NPCBOT);
            //"DELETE FROM characters_npcbot WHERE entry = ?", CONNECTION_ASYNC
            bstmt->setUInt32(0, entry);
            CharacterDatabase.Execute(bstmt);
            break;
        }
        default:
            TC_LOG_ERROR("sql.sql", "BotDataMgr:UpdateNpcBotData: unhandled updateType %u", uint32(updateType));
            break;
    }
}
void BotDataMgr::UpdateNpcBotDataAll(uint32 playerGuid, NpcBotDataUpdateType updateType, void* data)
{
    CharacterDatabasePreparedStatement* bstmt;
    switch (updateType)
    {
        case NPCBOT_UPDATE_OWNER:
            bstmt = CharacterDatabase.GetPreparedStatement(CHAR_UPD_NPCBOT_OWNER_ALL);
            //"UPDATE characters_npcbot SET owner = ? WHERE owner = ?", CONNECTION_ASYNC
            bstmt->setUInt32(0, *(uint32*)(data));
            bstmt->setUInt32(1, playerGuid);
            CharacterDatabase.Execute(bstmt);
            //break; //no break: erase transmogs
        [[fallthrough]];
        case NPCBOT_UPDATE_TRANSMOG_ERASE:
            bstmt = CharacterDatabase.GetPreparedStatement(CHAR_DEL_NPCBOT_TRANSMOG_ALL);
            //"DELETE FROM characters_npcbot_transmog WHERE entry IN (SELECT entry FROM characters_npcbot WHERE owner = ?)", CONNECTION_ASYNC
            bstmt->setUInt32(0, playerGuid);
            CharacterDatabase.Execute(bstmt);
            break;
        //case NPCBOT_UPDATE_ROLES:
        //case NPCBOT_UPDATE_FACTION:
        //case NPCBOT_UPDATE_EQUIPS:
        default:
            TC_LOG_ERROR("sql.sql", "BotDataMgr:UpdateNpcBotDataAll: unhandled updateType %u", uint32(updateType));
            break;
    }
}

void BotDataMgr::SaveNpcBotStats(NpcBotStats const* stats)
{
    CharacterDatabasePreparedStatement* bstmt = CharacterDatabase.GetPreparedStatement(CHAR_REP_NPCBOT_STATS);
    //"REPLACE INTO characters_npcbot_stats
    //(entry, maxhealth, maxpower, strength, agility, stamina, intellect, spirit, armor, defense,
    //resHoly, resFire, resNature, resFrost, resShadow, resArcane, blockPct, dodgePct, parryPct, critPct,
    //attackPower, spellPower, spellPen, hastePct, hitBonusPct, expertise, armorPenPct) VALUES
    //(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)", CONNECTION_ASYNC

    uint32 index = 0;
    bstmt->setUInt32(  index, stats->entry);
    bstmt->setUInt32(++index, stats->maxhealth);
    bstmt->setUInt32(++index, stats->maxpower);
    bstmt->setUInt32(++index, stats->strength);
    bstmt->setUInt32(++index, stats->agility);
    bstmt->setUInt32(++index, stats->stamina);
    bstmt->setUInt32(++index, stats->intellect);
    bstmt->setUInt32(++index, stats->spirit);
    bstmt->setUInt32(++index, stats->armor);
    bstmt->setUInt32(++index, stats->defense);
    bstmt->setUInt32(++index, stats->resHoly);
    bstmt->setUInt32(++index, stats->resFire);
    bstmt->setUInt32(++index, stats->resNature);
    bstmt->setUInt32(++index, stats->resFrost);
    bstmt->setUInt32(++index, stats->resShadow);
    bstmt->setUInt32(++index, stats->resArcane);
    bstmt->setFloat (++index, stats->blockPct);
    bstmt->setFloat (++index, stats->dodgePct);
    bstmt->setFloat (++index, stats->parryPct);
    bstmt->setFloat (++index, stats->critPct);
    bstmt->setUInt32(++index, stats->attackPower);
    bstmt->setUInt32(++index, stats->spellPower);
    bstmt->setUInt32(++index, stats->spellPen);
    bstmt->setFloat (++index, stats->hastePct);
    bstmt->setFloat (++index, stats->hitBonusPct);
    bstmt->setUInt32(++index, stats->expertise);
    bstmt->setFloat (++index, stats->armorPenPct);

    CharacterDatabase.Execute(bstmt);
}

NpcBotAppearanceData const* BotDataMgr::SelectNpcBotAppearance(uint32 entry)
{
    NpcBotAppearanceDataMap::const_iterator itr = _botsAppearanceData.find(entry);
    return itr != _botsAppearanceData.end() ? itr->second : nullptr;
}

NpcBotExtras const* BotDataMgr::SelectNpcBotExtras(uint32 entry)
{
    NpcBotExtrasMap::const_iterator itr = _botsExtras.find(entry);
    return itr != _botsExtras.end() ? itr->second : nullptr;
}

NpcBotTransmogData const* BotDataMgr::SelectNpcBotTransmogs(uint32 entry)
{
    NpcBotTransmogDataMap::const_iterator itr = _botsTransmogData.find(entry);
    return itr != _botsTransmogData.end() ? itr->second : nullptr;
}
void BotDataMgr::UpdateNpcBotTransmogData(uint32 entry, uint8 slot, uint32 item_id, uint32 fake_id, bool update_db)
{
    ASSERT(slot < BOT_TRANSMOG_INVENTORY_SIZE);

    NpcBotTransmogDataMap::iterator itr = _botsTransmogData.find(entry);
    if (itr == _botsTransmogData.end())
        _botsTransmogData[entry] = new NpcBotTransmogData();

    _botsTransmogData[entry]->transmogs[slot] = { item_id, fake_id };

    if (update_db)
    {
        CharacterDatabasePreparedStatement* bstmt = CharacterDatabase.GetPreparedStatement(CHAR_REP_NPCBOT_TRANSMOG);
        //"REPLACE INTO characters_npcbot_transmog (entry, slot, item_id, fake_id) VALUES (?, ?, ?, ?)", CONNECTION_ASYNC
        bstmt->setUInt32(0, entry);
        bstmt->setUInt8(1, slot);
        bstmt->setUInt32(2, item_id);
        bstmt->setUInt32(3, fake_id);
        CharacterDatabase.Execute(bstmt);
    }
}

void BotDataMgr::ResetNpcBotTransmogData(uint32 entry, bool update_db)
{
    NpcBotTransmogDataMap::iterator itr = _botsTransmogData.find(entry);
    if (itr == _botsTransmogData.end())
        return;

    if (update_db)
    {
        CharacterDatabaseTransaction trans = CharacterDatabase.BeginTransaction();
        for (uint8 i = 0; i != BOT_TRANSMOG_INVENTORY_SIZE; ++i)
        {
            if (_botsTransmogData[entry]->transmogs[i].first == 0 && _botsTransmogData[entry]->transmogs[i].second == 0)
                continue;

            CharacterDatabasePreparedStatement* bstmt = CharacterDatabase.GetPreparedStatement(CHAR_REP_NPCBOT_TRANSMOG);
            //"REPLACE INTO characters_npcbot_transmog (entry, slot, item_id, fake_id) VALUES (?, ?, ?, ?)", CONNECTION_ASYNC
            bstmt->setUInt32(0, entry);
            bstmt->setUInt8(1, i);
            bstmt->setUInt32(2, 0);
            bstmt->setUInt32(3, 0);
            trans->Append(bstmt);
        }

        if (trans->GetSize() > 0)
            CharacterDatabase.CommitTransaction(trans);
    }

    for (uint8 i = 0; i != BOT_TRANSMOG_INVENTORY_SIZE; ++i)
        _botsTransmogData[entry]->transmogs[i] = { 0, 0 };
}

void BotDataMgr::RegisterBot(Creature const* bot)
{
    if (_existingBots.find(bot) != _existingBots.end())
    {
        TC_LOG_ERROR("entities.unit", "BotDataMgr::RegisterBot: bot %u (%s) already registered!",
            bot->GetEntry(), bot->GetName().c_str());
        return;
    }

    std::unique_lock<std::shared_mutex> lock(*GetLock());

    _existingBots.insert(bot);
    //TC_LOG_ERROR("entities.unit", "BotDataMgr::RegisterBot: registered bot %u (%s)", bot->GetEntry(), bot->GetName().c_str());
}
void BotDataMgr::UnregisterBot(Creature const* bot)
{
    if (_existingBots.find(bot) == _existingBots.end())
    {
        TC_LOG_ERROR("entities.unit", "BotDataMgr::UnregisterBot: bot %u (%s) not found!",
            bot->GetEntry(), bot->GetName().c_str());
        return;
    }

    std::unique_lock<std::shared_mutex> lock(*GetLock());

    _existingBots.erase(bot);
    //TC_LOG_ERROR("entities.unit", "BotDataMgr::UnregisterBot: unregistered bot %u (%s)", bot->GetEntry(), bot->GetName().c_str());
}
Creature const* BotDataMgr::FindBot(uint32 entry)
{
    std::shared_lock<std::shared_mutex> lock(*GetLock());

    for (NpcBotRegistry::const_iterator ci = _existingBots.begin(); ci != _existingBots.end(); ++ci)
    {
        if ((*ci)->GetEntry() == entry)
            return *ci;
    }
    return nullptr;
}
Creature const* BotDataMgr::FindBot(std::string_view name, LocaleConstant loc)
{
    std::wstring wname;
    if (Utf8toWStr(name, wname))
    {
        wstrToLower(wname);
        std::shared_lock<std::shared_mutex> lock(*GetLock());
        for (NpcBotRegistry::const_iterator ci = _existingBots.begin(); ci != _existingBots.end(); ++ci)
        {
            std::string basename = (*ci)->GetName();
            if (CreatureLocale const* creatureInfo = sObjectMgr->GetCreatureLocale((*ci)->GetEntry()))
            {
                if (creatureInfo->Name.size() > loc && !creatureInfo->Name[loc].empty())
                    basename = creatureInfo->Name[loc];
            }

            std::wstring wbname;
            if (!Utf8toWStr(basename, wbname))
                continue;

            wstrToLower(wbname);
            if (wbname == wname)
                return *ci;
        }
    }

    return nullptr;
}

NpcBotRegistry const& BotDataMgr::GetExistingNPCBots()
{
    return _existingBots;
}

void BotDataMgr::GetNPCBotGuidsByOwner(std::vector<ObjectGuid> &guids_vec, ObjectGuid owner_guid)
{
    ASSERT(AllBotsLoaded());

    std::shared_lock<std::shared_mutex> lock(*GetLock());

    for (NpcBotRegistry::const_iterator ci = _existingBots.begin(); ci != _existingBots.end(); ++ci)
    {
        if (_botsData[(*ci)->GetEntry()]->owner == owner_guid.GetCounter())
            guids_vec.push_back((*ci)->GetGUID());
    }
}

ObjectGuid BotDataMgr::GetNPCBotGuid(uint32 entry)
{
    ASSERT(AllBotsLoaded());

    std::shared_lock<std::shared_mutex> lock(*GetLock());

    for (NpcBotRegistry::const_iterator ci = _existingBots.begin(); ci != _existingBots.end(); ++ci)
    {
        if ((*ci)->GetEntry() == entry)
            return (*ci)->GetGUID();
    }

    return ObjectGuid::Empty;
}

std::vector<uint32> BotDataMgr::GetExistingNPCBotIds()
{
    ASSERT(AllBotsLoaded());

    std::vector<uint32> existing_ids;
    existing_ids.reserve(_botsData.size());
    for (decltype(_botsData)::value_type const& bot_data_pair : _botsData)
        existing_ids.push_back(bot_data_pair.first);

    return existing_ids;
}

uint8 BotDataMgr::GetOwnedBotsCount(ObjectGuid owner_guid, uint32 class_mask)
{
    uint8 count = 0;
    for (decltype(_botsData)::value_type const& bdata : _botsData)
        if (bdata.second->owner == owner_guid.GetCounter() && (!class_mask || !!(class_mask & (1u << (_botsExtras[bdata.first]->bclass - 1)))))
            ++count;

    return count;
}

std::pair<uint8, uint8> BotDataMgr::GetZoneLevels(uint32 zoneId)
{
    //Only maps 0 and 1 are covered
    switch (zoneId)
    {
        case 1: // Dun Morogh
        case 12: // Elwynn Forest
        case 14: // Durotar
        case 85: // Tirisfal Glades
        case 141: // Teldrassil
        case 215: // Mulgore
        case 3430: // Eversong Woods
        case 3524: // Azuremyst Isle
            return { 1, 14 };
        case 38: // Loch Modan
        case 40: // Westfall
        case 130: // Silverpine Woods
        case 148: // Darkshore
        case 3433: // Ghostlands
        case 3525: // Bloodmyst Isle
            return { 8, 24 };
        case 17: // Barrens
            return { 8, 30 };
        case 44: // Redridge Mountains
            return { 13, 30 };
        case 406: // Stonetalon Mountains
            return { 13, 32 };
        case 10: // Duskwood
        case 11: // Wetlands
        case 267: // Hillsbrad Foothills
        case 331: // Ashenvale
            return { 18, 34 };
        case 400: // Thousand Needles
            return { 23, 40 };
        case 36: // Alterac Mountains
        case 45: // Arathi Highlands
        case 405: // Desolace
            return { 28, 44 };
        case 33: // Stranglethorn Valley
            return { 28, 50 };
        case 3: // Badlands
        case 8: // Swamp of Sorrows
        case 15: // Dustwallow Marsh
            return { 33, 50 };
        case 47: // Hinterlands
        case 357: // Feralas
        case 440: // Tanaris
            return { 38, 54 };
        case 4: // Blasted Lands
        case 16: // Azshara
        case 51: // Searing Gorge
            return { 43, 60 };
        case 490: // Un'Goro Crater
            return { 45, 60 };
        case 361: // Felwood
            return { 46, 60 };
        case 28: // Western Plaguelands
        case 46: // Burning Steppes
            return { 48, 60 };
        case 41: // Deadwind Pass
            return { 50, 60 };
        case 1377: // Silithus
            return { 53, 60 };
        case 139: // Eastern Plaguelands
        case 618: // Winterspring
            return { 53, 60 }; //63
        default:
            return { 0, 0 };
    }
}

std::pair<uint32, Position const*> BotDataMgr::GetWanderMapNode(uint32 mapId, uint32 curNodeId, uint32 lastNodeId, uint8 lvl)
{
    decltype(WanderMap.Nodes)::const_iterator cit = WanderMap.Nodes.find(mapId);
    if (cit != WanderMap.Nodes.cend())
    {
        decltype(WanderMap.Nodes)::value_type::second_type::const_iterator ici = cit->second.find(curNodeId);
        if (ici != cit->second.cend())
        {
            std::vector<decltype(WanderMap)::BotTravelNode const*> convec;
            if (ici->second.connections.size() == 1)
                convec.push_back(ici->second.connections.front());
            else
            {
                uint8 minlevel = 255;
                for (auto const* con : ici->second.connections)
                {
                    if (con->id != lastNodeId && (con->minlevel + 4 >= lvl || con->maxlevel <= lvl + 6))
                        convec.push_back(con);
                    if (con->maxlevel < minlevel)
                        minlevel = con->maxlevel;
                }
                if (convec.empty())
                {
                    for (auto const* con : ici->second.connections)
                    {
                        if (con->maxlevel == minlevel || con->minlevel < minlevel + 4)
                            convec.push_back(con);
                    }
                }
                if (convec.empty())
                {
                    for (auto const* con : ici->second.connections)
                    {
                        if (con->id != lastNodeId)
                            convec.push_back(con);
                    }
                }
            }
            auto const* randomNode = Trinity::Containers::SelectRandomContainerElement(convec);
            return std::make_pair(randomNode->id, static_cast<Position const*>(randomNode));
        }
    }

    return { 0, nullptr };
}

Position const* BotDataMgr::GetWanderMapNodePosition(uint32 mapId, uint32 nodeId)
{
    decltype(WanderMap.Nodes)::const_iterator cit = WanderMap.Nodes.find(mapId);
    if (cit != WanderMap.Nodes.cend())
    {
        decltype(WanderMap.Nodes)::value_type::second_type::const_iterator ici = cit->second.find(nodeId);
        if (ici != cit->second.cend())
            return static_cast<Position const*>(&ici->second);
    }
    return nullptr;
}

std::string BotDataMgr::GetWanderMapNodeName(uint32 mapId, uint32 nodeId)
{
    decltype(WanderMap.Nodes)::const_iterator cit = WanderMap.Nodes.find(mapId);
    if (cit != WanderMap.Nodes.cend())
    {
        decltype(WanderMap.Nodes)::value_type::second_type::const_iterator ici = cit->second.find(nodeId);
        if (ici != cit->second.cend())
            return ici->second.name;
    }
    return {};
}
