# tidewrack-broken: the validator's refusal fixture

Only `warrens/area.json` differs from `../tidewrack/warrens/area.json` (harbour and manses are the good
ones, referenced through `realm.json`), and it differs by exactly three defects. The scenes point back at the
good folder, except for the one added room. `python3 ../validate.py .` exits 1 and prints:

```
REFUSED warrens/area.json:19: dangling exit w from 201 (The Wet Cellar) to 299: no such room in realm tidewrack-broken
REFUSED warrens/area.json:86: unplaced key: the lock on 206 s needs sluice-wheel, which no area places in a room, on a mob or as a quest reward
REFUSED warrens/area.json:159: unreachable room 213 (The Sealed Sump): no path from the spawn 101
```

| defect | line | the text on it |
|---|---|---|
| dangling exit | 19 | `"w": "299"` in room 201's `exits` (MUD §4 hour 0: "a dangling `exit w` in the cellar") |
| unplaced key | 86 | `"s": "sluice-wheel"` in room 206's `locks`; no area has an item `sluice-wheel` |
| unreachable room | 159 | `"id": "213"`, The Sealed Sump; its only exit leads out (`u` → 203), and nothing leads in |

MUD-AREA's `jmud1.sh` should assert these three reasons at these lines, and assert that no cell was born.
