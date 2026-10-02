# Story templates

A story is a **table** a friend writes and then seals. After `story seal`, the
table is the law on every player's cell: a player's `go`, `take` and `act` are
one write each, and the Host judges it against the table. The client is
`native/resource-client/src/story.rs`; the theorems are
`Assurance/StoryLaw.lean`.

One directory per built-in story; `tale/` is the first. A friend's own table
is a file in `HOME/requests/` (`story new NAME --from @FILE`).

## The table

One row per line. Blank lines and `#` lines are not rows. Rows may come in any
order.

| row | meaning |
|---|---|
| `title TEXT` | the story's title (once) |
| `scene N TITLE \| TEXT` | scene `N` (a number), its title and the text a player reads there |
| `start N` | where every player begins (once) |
| `end N` | an ending: no way leads on from it |
| `item NAME N` | an item that lies in scene `N`; `take NAME` there, once |
| `exit N WORD M [needs ITEM]` | `go WORD` in scene `N` leads to `M` (holding `ITEM`, if named) |
| `act N VERB M [needs ITEM]` | `act VERB` in scene `N` leads to `M` (holding `ITEM`, if named) |

`story new` refuses a table, naming the row, when: a row is not one of these;
a scene, start, end, item or way names a scene the table does not have; a way
leaves an end, or leads back to its own scene; two ways join the same pair of
scenes; a word is used twice in one scene; a way needs an item no row places;
a scene cannot be reached from the start; a scene that is not an end has no
way on.

## The law it becomes

A player's cell holds `scene` (field 0), `turn` (field 1) and `carries/ITEM`
(field 2, 3, … in item-name order). The law on it, for player `S`:

| # | name | admits |
|---|---|---|
| 0 | management | reads and writes only: nobody (the author included) installs another law, delegates or revokes |
| 1 | mover | a write only by `S` |
| 2 | turn | `turn` goes up by exactly one |
| 3 | exits | the scene stays, or moves along one way of the table |
| 4… | needs ITEM | per conditional way: its item was already held |
| … | here ITEM | per item: taken only in its scene, standing still |
| … | once ITEM | per item: 0 to 1, never back |
| last | progress | every turn moves or takes something |

Clauses 1 onward are guarded by `not (verb == write)`. A refusal names the
first clause that fails, as the Host renders it (`refused: law-denied: …`), and
the client adds the clause's number and name.

`tale/law.player` (the grammar, one clause per line, `{S}` unbound),
`tale/law.player.json` and `tale/law.table.json` are **generated**:
`scripts/gen-storylaw.py --mini PATH` runs the client's own parser and
generator (`mini story-law --table tale/table`) and writes them, and writes
the tale's table and law into `Assurance/StoryLaw.lean` §8, where
`tale_embedded_is_law` proves them equal to the Lean `law` of that table.
`--check` fails if any of them is not what the client generates now.

The table document's own law: until the seal, only the author writes it; at
the seal it becomes `law.table.json` (a write is refused `sealed`, and only
reads and writes are verbs it admits, so no law ever replaces it).

## The verbs, in order

1. `story new NAME --from tale|@FILE [--gm S]` (the author): runs the room
   template `room/story` (room, index, chapters, the scenes stream only the GM
   writes, cast), births `NAME/table` and writes the table's rows into it,
   links the index to it.
2. `story seal NAME`: installs `law.table.json` on the table.
3. `story invite NAME S` (only once sealed): births `NAME/p-S` in the room
   under a law only the author satisfies, writes its start (`scene` = start,
   everything else 0), installs `S`'s law, and grants `S` the room
   (observe, mutate, append). `story invite NAME S gm`: the GM's grant
   (observe, append). Each prints the line `S` types: `story join NAME …`.
4. `look`: signed reads of the table, its law, my cell and its law. It refuses
   to play when the table's law is not the sealed one or my cell's law is not
   the one the table generates for me, or when a cell nobody has moved is not
   at the start.
5. `go WORD` / `act VERB` / `take ITEM`: one write of `scene` (or
   `carries/ITEM`) and `turn + 1`, each with `expected` = the value just read.
   `go N` with a scene number sends that scene to the law as asked.
6. `narrate TEXT` (the GM): an entry in `NAME/scenes`.

Why the author births a player's cell: the room's birth gate judges a
placement by the request's slots only, and nothing there names the law the new
cell is born with. A cell a player bore would carry whatever law their client
chose. The author's birth, checked by the player's own `look`, is the shape
the kernel enforces today.
