# Area folders: the `.dungeon` idea, rebuilt

This is MUD §2.1. The idea comes from Bread's `docs/AUTHORING-DUNGEONS.md:1-12`: an area is a text a person
writes, and parsing is fail-closed, so a broken area never becomes a world. That document's grammar is not
reused here. The file format is JSON, because `area load` passes every number to the Host as a canonical
decimal string anyway (p-templates README item 7). JSON also puts every exit and every lock on its own line,
so a refusal can name the line.

## A realm folder

```
REALM/realm.json          areas and load order, spawn room, shrine, wells, starter kit, quests,
                          the law constants (constants.*, with their derivation), tariff and table paths
REALM/AREA/area.json      rooms, exits, locks, darkness, leases, items and placements, mob spawns, shop
REALM/AREA/rooms/*.md     one scene per room (MUD §2.0: R/scene, a content cell)
```

`tidewrack/` is the first realm. It has 30 rooms: harbour 101–110, warrens 201–212 and manses 301–308.
`tidewrack-broken/` is the refusal fixture (see its README).

## `area.json`

| key | meaning | becomes |
|---|---|---|
| `areaId` | the area's number | room field `area` (pinned by law.room clause 2) |
| `builder` | `{W_FOUNDER}` or `{CONCIERGE}` (manses) | `{BUILDER}` in law.room |
| `rooms[].id` | realm-unique room number, decimal string | room field `id` (pinned). Sheets store `at` as this number. |
| `rooms[].exits` | `DIR: ROOM` for DIR in `room/fields.json` `directions` | fields `exit-DIR` = ROOM, `locked-DIR` = 0/1 and `key-DIR` = item id or 0, **all three created for every exit** (the door clause reads `locked-DIR` of whichever exit is taken, and fails closed if it is absent) |
| `rooms[].locks` | `DIR: ITEM-SLUG` | `locked-DIR` = 1 and `key-DIR` = that item's id |
| `rooms[].dark` | "0"/"1" | field `dark` (law.sheet clause 18 needs a lit lantern to enter) |
| `rooms[].leased` | "0"/"1" | field `leased` (pinned). `until` is created as 0, and the concierge mirrors each lease's `expiresAt` into it (MUD §2.9). |
| `rooms[].scene` | path of the scene | written into the content cell `{REALM}-scene-{ID}` |
| `items[]` | `slug`, `id`, `kind`, `placed: {room\|mob\|quest: …}` | an item cell (`item/init.item.json`). `placed.room` means owner REF with where = room. `placed.mob` and `placed.quest` mean owner REF with where = 0. A quest reward also gets `law.item-reward`. |
| `spawns[]` | `mob`, `room` (= HOME), `hp`, `respawn`, `skill`, `wander`, `program` | a mob subject (key held by the referee), a mob sheet (`sheet/init.sheet.json` with S = the mob, HOME = room, HPMAX = hp, NEG_RESPAWN = −respawn), and its program document |
| `shop` | room, market name, what it sells | a market cell under the area (`market/`) |

Direction k (0-based, in `room/fields.json` order) sits at fields `8+3k`, `9+3k` and `10+3k`.

## `area load REALM AREA`: validate everything, then birth, in this order

1. **Validate the whole realm** (the rules are in `../validate.py`, and every refusal names `file:line`):
   dangling exit · unreachable room (BFS from `realm.json` `spawn`, ignoring locks and darkness) ·
   unplaced key (a lock whose key no area places) · lock on a non-exit · duplicate id · unknown direction ·
   missing scene · spawn, shop or placement in an unknown room · a reward for an unknown quest ·
   constants that disagree with `affliction-table.json`. **Any refusal means nothing is born.**
   The whole realm is validated, not just the area, because exits cross areas (quay `d` → cellar 201).
   Validating one area alone would call every cross-area exit dangling.
2. For each room, in file order: create `{REALM}-room-{ID}` declared under `law.management`, propose its
   init fields, install `law.management ; law.room`, create the scene cell and write `rooms/SLUG.md` into it.
   Each creation pays `tariff.create`. This is the story order (`../../story/README.md`): create, then init,
   then law, because clauses fail closed on absent fields.
3. Items, then spawns (a mob sheet needs its HOME room to exist, but no law reads another cell at birth).
4. The shop's market cell, if there is one.

**Load order across areas does not matter to the laws**, because exits are numbers, and a room whose
neighbour is not born yet is only a room nobody can enter yet. `realm.json` `loadOrder` is the order the
evening uses.
