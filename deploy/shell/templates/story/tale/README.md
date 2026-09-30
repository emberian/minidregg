# tale — The Lamplighter's House

Five scene docs (`scene/0.md` … `scene/4.md`), one key (scene 1), one locked door (3 → 4).
Field numbers: state cell `0 = scene`, `1 = gm/beat`; player cell `0 = at`, `1 = has/key`.
The file contract and the order `story new` follows are in `../README.md`.

## The clauses

`law.player`, one clause per line of the file. Management is clause 0 of the
installed law.

| # | name | clause | reads |
|---|---|---|---|
| 0 | management | `any [ verb == 1, verb == 2, all [ verb in {3,4,5}, subject == {FOUNDER} ] ]` | reads and mutates pass (grants decide who holds them); delegate/installPolicy/revoke only for the founder (sealed: `{3,5}`, no installPolicy) |
| 1 | mover | `any [ subject == {S}, not (verb == 2) ]` | only this player moves this player |
| 2 | range | `any [ all [ field 0 in {0,1,2,3,4}, field 1 in {0,1} ], not (verb == 2) ]` | the scene exists; the key is held or not |
| 3 | onward | `any [ field 0 monotone, not (verb == 2) ]` | no walking back |
| 4 | exits | `any [ field 0 delta == 0, all [0→1], all [1→2], all [1→3], all [3→4], not (verb == 2) ]` | the transition table |
| 5 | door | `any [ not (field 0 after == 4), field 1 before == 1, not (verb == 2) ]` | entering 4 needs the key already held |
| 6 | key-kept | `any [ field 1 writeOnce, not (verb == 2) ]` | a found key cannot be dropped |
| 7 | key-here | `any [ field 1 delta == 0, all [ field 0 before == 1, field 0 delta == 0 ], not (verb == 2) ]` | the key is taken in scene 1, standing still |
| 8 | take-once | `any [ not (field 1 after == 1), field 1 before == 0, not (field 0 delta == 0), not (verb == 2) ]` | a key already held is not taken again |
| 9 | no-idle | `any [ not (field 0 delta == 0), not (field 1 delta == 0), not (verb == 2) ]` | every turn moves or takes |

`law.state`: 0 management, 1 **gm** `any [ subject == {GM}, not (verb == 2) ]`,
2 **range** `field 0 in {0..4}`, 3 **onward** `field 0 monotone`, 4 **table**
(the same four edges). `onward` comes before `table`, so a rewind is reported
as `monotone`, which is the refutation pole of the "cannot be rewound" theorem.

## J15 assertion table

Subjects: A founder, B and C players, H the GM. Clause numbers count from 0 in
the installed (composed) law. Every refused row fails that clause first, and
the earlier clauses hold.

| # | who | move | cell, before → after (at,key) | expected |
|---|---|---|---|---|
| 1 | B | `go 1` | player-B (0,0)→(1,0) | admitted |
| 2 | C | `go 2` | player-C (0,0)→(2,0) | `refused: law-denied:` clause 4 **exits** |
| 3 | C | `go 1` | (0,0)→(1,0) | admitted |
| 4 | C | `go 0` | (1,0)→(0,0) | `refused: law-denied:` clause 3 **onward** (`field 0 monotone`) |
| 5 | C | `take key` | (1,0)→(1,1) | admitted |
| 6 | C | `take key` again | (1,1)→(1,1) | `refused: law-denied:` clause 8 **take-once** |
| 7 | C | drop the key (`write 1 0`) | (1,1)→(1,0) | `refused: law-denied:` clause 6 **key-kept** (`field 1 writeOnce`) |
| 8 | B | `take key` from scene 0 | (0,0)→(0,1) | `refused: law-denied:` clause 7 **key-here** |
| 9 | B | `go 3` | (1,0)→(3,0) | admitted |
| 10 | B | `go 4` without the key | (3,0)→(4,0) | `refused: law-denied:` clause 5 **door** |
| 11 | C | `go 3`, then `go 4` with the key | (3,1)→(4,1) | admitted |
| 12 | B | writes C's cell (with a stray grant) | player-C | `refused: law-denied:` clause 1 **mover** (without a grant: `no-grant` first) |
| 13 | H | advance scene 0→1, 1→3 | state | admitted |
| 14 | H | scene 3→1 | state | `refused: law-denied:` clause 3 **onward** |
| 15 | H | scene 0→2 | state | `refused: law-denied:` clause 4 **table** |
| 16 | A | moves the scene | state | `refused: law-denied:` clause 1 **gm** |
| 17 | A | `story seal tale` | every cell | admitted |
| 18 | A | `law tale-state "open"` | state | `refused: law-denied:` clause 0 **management** |
| 19 | H | after seal, scene 1→2 | state | admitted (sealed means no re-lawing, and play goes on) |

The text after `law-denied:` is whatever K-LAW-LEAF renders for that clause
(PLACE §2.6). Every refusing clause above is an `any`, and all of its children
are false, so a leaf rule that stops at "the first false child" would name
`not (verb == 2)` or the first table row. The rule J15 needs is: **report the
failing top-level clause**, and within it the failing atom that is not a verb
or subject guard. That is a requirement on P-LAW, recorded here because this
table depends on it.

What the law does **not** refuse, deliberately: moving into 2 or 3 with or
without the key; reading any story cell (read access is the grants' business).
