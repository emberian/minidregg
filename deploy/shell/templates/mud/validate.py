# Reference area validator for `area load` (MUD.md §2.1): fail-closed, every refusal names its file:line.
# This is a COPY OF THE RULES for the MUD-AREA lane to implement in native/resource-client/src/mud.rs and to
# check its refusals against; it is not the shell and it births nothing. Checks (Bread's parse_dungeon set,
# docs/AUTHORING-DUNGEONS.md:8-10, plus what the laws need):
#   dangling exit · unreachable room · unplaced key · lock on a missing exit · duplicate room id ·
#   unknown direction · missing scene · spawn/shop/placement in an unknown room · constants that disagree
#   with affliction-table.json
# usage: python3 validate.py REALM_DIR      exit 0 = loads, 1 = refused (every refusal printed)
import json, os, sys
from collections import deque

HERE = os.path.dirname(os.path.abspath(__file__))
DIRS = json.load(open(os.path.join(HERE, "room", "fields.json")))["directions"]
realm_dir = sys.argv[1].rstrip("/")
realm = json.load(open(os.path.join(realm_dir, "realm.json")))
errs = []

def line_of(path, needle, after=None):
    lines = open(path).read().splitlines()
    start = 0
    if after is not None:
        start = next((i for i, l in enumerate(lines) if after in l), 0)
    for i in range(start, len(lines)):
        if needle in lines[i]:
            return i + 1
    return 0

def refuse(path, line, msg):
    errs.append(f"REFUSED {os.path.relpath(path, realm_dir)}:{line}: {msg}")

rooms, items, owner_file = {}, {}, {}
areas = []
for name in realm["loadOrder"]:
    adir = os.path.normpath(os.path.join(realm_dir, realm["areas"][name]))
    apath = os.path.join(adir, "area.json")
    area = json.load(open(apath))
    areas.append((name, adir, apath, area))
    for r in area["rooms"]:
        if r["id"] in rooms:
            refuse(apath, line_of(apath, f'"id": "{r["id"]}"'), f"duplicate room id {r['id']}")
        rooms[r["id"]] = (name, apath, r)
        if not os.path.exists(os.path.join(adir, r["scene"])):
            refuse(apath, line_of(apath, f'"scene": "{r["scene"]}"'), f"room {r['id']}: scene {r['scene']} does not exist")
    for it in area["items"]:
        items[it["slug"]] = (apath, it)

for name, adir, apath, area in areas:
    for r in area["rooms"]:
        anchor = f'"id": "{r["id"]}"'
        for d, to in r["exits"].items():
            if d not in DIRS:
                refuse(apath, line_of(apath, f'"{d}": "{to}"', anchor), f"room {r['id']}: unknown direction {d}")
            if to not in rooms:
                refuse(apath, line_of(apath, f'"{d}": "{to}"', anchor),
                       f"dangling exit {d} from {r['id']} ({r['title']}) to {to}: no such room in realm {realm['realm']}")
        for d, key in r.get("locks", {}).items():
            if d not in r["exits"]:
                refuse(apath, line_of(apath, f'"{d}": "{key}"', anchor), f"room {r['id']}: lock on {d}, which is not an exit")
            it = items.get(key)
            if it is None or it[1]["kind"] != "key" or not it[1].get("placed"):
                refuse(apath, line_of(apath, f'"{d}": "{key}"', anchor),
                       f"unplaced key: the lock on {r['id']} {d} needs {key}, which no area places in a room, on a mob or as a quest reward")
    for it in area["items"]:
        p = it.get("placed", {})
        if len(p) != 1 or next(iter(p)) not in ("room", "mob", "quest"):
            refuse(apath, line_of(apath, f'"slug": "{it["slug"]}"'), f"item {it['slug']}: placed must name exactly one of room|mob|quest")
        elif "quest" in p and not os.path.exists(os.path.join(realm_dir, realm.get("quests", {}).get(p["quest"], "/nonexistent"), "quest.json")):
            refuse(apath, line_of(apath, f'"slug": "{it["slug"]}"'), f"item {it['slug']}: placed as the reward of unknown quest {p['quest']}")
        elif "room" in p and p["room"] not in rooms:
            refuse(apath, line_of(apath, f'"slug": "{it["slug"]}"'), f"item {it['slug']}: placed in unknown room {p['room']}")
    for s in area["spawns"]:
        for rid in [s["room"]] + s.get("wander", []):
            if rid not in rooms:
                refuse(apath, line_of(apath, f'"mob": "{s["mob"]}"'), f"spawn {s['mob']}: unknown room {rid}")
        if not os.path.exists(os.path.join(adir, s["program"])):
            refuse(apath, line_of(apath, f'"mob": "{s["mob"]}"'), f"spawn {s['mob']}: program {s['program']} does not exist")
    if area.get("shop") and area["shop"]["room"] not in rooms:
        refuse(apath, line_of(apath, '"shop"'), f"shop in unknown room {area['shop']['room']}")

# reachability from the realm spawn, ignoring locks and darkness (a key or a lantern can always be obtained)
seen, q = {realm["spawn"]}, deque([realm["spawn"]])
while q:
    for to in rooms[q.popleft()][2]["exits"].values():
        if to in rooms and to not in seen:
            seen.add(to); q.append(to)
for rid, (name, apath, r) in rooms.items():
    if rid not in seen:
        refuse(apath, line_of(apath, f'"id": "{rid}"'), f"unreachable room {rid} ({r['title']}): no path from the spawn {realm['spawn']}")

# the law constants must agree with the table (a law bound tighter than the table refuses honest play;
# a looser one is not a bound)
rpath = os.path.join(realm_dir, "realm.json")
c = realm["constants"]
tab = json.load(open(os.path.normpath(os.path.join(realm_dir, realm["afflictionTable"]))))
bal = min(int(a["cost"]) for a in tab["actions"].values() if a.get("balance") == "bal")
want = {"MAXHIT_LT": -(int(c["MAXHIT"]) + 1), "NEG_COST": -bal, "NEG_ECOST": -int(tab["actions"]["cast"]["cost"]),
        "NEG_RESPAWN": -int(c["RESPAWN"]), "MAXPAY_LT": -(int(c["MAXPAY"]) + 1)}
for k, v in want.items():
    if int(c[k]) != v:
        refuse(rpath, line_of(rpath, f'"{k}"'), f"constant {k} = {c[k]}, derived value is {v}")
worst = max(int(s["damage"]) for s in tab["skills"].values() if "damage" in s)
if worst > int(c["MAXHIT"]):
    refuse(rpath, line_of(rpath, '"MAXHIT"'), f"the table deals {worst} > MAXHIT {c['MAXHIT']}")

if errs:
    print("\n".join(errs)); sys.exit(1)
print(f"OK {realm['realm']}: {len(rooms)} rooms in {len(areas)} areas, {len(items)} items, all reachable from {realm['spawn']}")
