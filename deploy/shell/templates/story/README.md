# Story templates

One directory per story. `story new NAME --from DIR` reads a directory in this
shape and nothing else; `tale/` is the first one. Placeholders are `{UPPER}`
words, substituted textually (in JSON they sit inside strings, and after
substitution every value is a canonical decimal string, which is what the Host
parser requires: `Host/Json.lean:139-145`).

| placeholder | bound by | value |
|---|---|---|
| `{STORY}` | `story new NAME` | NAME (letters, digits, hyphens; `workspace.rs:67-77`) |
| `{FOUNDER}` | `story new` | the founder's subject, decimal |
| `{GM}` | `story new` (= `{FOUNDER}`), rebound by `summon STORY as gm` | the GM's subject |
| `{S}` | `room invite STORY S player` | the player's subject |
| `{N}` | `story new`, once per scene | the scene number |

## Files and the verb that reads each

| file | read by | used as |
|---|---|---|
| `story.json` | `story new` | cell names, field numbers, initial values, scene list, exits, grants per role, and which law files compose each installed law |
| `scene/{N}.md` | `story new` (writes `{STORY}-scene-{N}`), `look` (prints the doc for my `at`) | the text a player reads |
| `init.state.json` | `story new` → `propose @…` | creates fields 0 and 1 on `{STORY}-state` |
| `init.player.json` | `room invite … player` → `propose @…` | creates fields 0 and 1 on `{STORY}-player-{S}` |
| `law.management.open` / `.json` | `story new`, `room invite`, `summon … as gm` | the first clause of every installed law before sealing |
| `law.management.sealed` / `.json` | `story seal` | the same clause without `installPolicy` |
| `law.state` / `.json` | `story new`, `summon … as gm`, `story seal` | the scene cell's rules |
| `law.player` / `.json` | `room invite … player`, `story seal` | one player's rules |
| `law.scene` / `.json` | `story new`, `summon … as gm`, `story seal` | who may edit a scene doc |

Each law file is written twice: the one-line grammar (§2.6, lane P-LAW) and the
same predicate as `Pred` JSON, which the shell's `law ID REF @FILE` verb accepts
today. The JSON was produced from the grammar text mechanically and must be kept
in step with it.

**Composition.** The installed law of a cell is
`law.management.{open|sealed} ; law.X`, and in JSON
`{"type":"all","predicates":[<management>, ...<law.X>.predicates]}` (a
single-clause `law.X` contributes itself). One clause per `;`, in file order.
That order is the order refusals are reported in, so do not re-sort it.

## `story new NAME --from DIR`, in order

The order matters because every game clause reads `resource/field/*` slots and
fails closed where they are absent.

1. `create {STORY}-state declared @management` (management.open with
   `{FOUNDER}` bound), then `propose`/`submit` `init.state.json`.
2. For each scene N: create `{STORY}-scene-{N}` (content) under management.open,
   write `scene/{N}.md` into it.
3. Install `management.open ; law.state` on the state cell and
   `management.open ; law.scene` on each scene doc, with `{GM}` = `{FOUNDER}`.

`room invite STORY S player`: create `{STORY}-player-{S}` under
management.open, `init.player.json`, delegate `observe,mutate` on it to S,
delegate `observe` on the state cell and every scene doc to S, and install
`management.open ; law.player` with `{S}` bound. Delegation comes before the
law only by convention; management.open admits the founder's delegation either
way.

`summon STORY as gm`: delegate the `gm` grants from `story.json` to Hermes and
re-install the state and scene laws with `{GM}` = Hermes's subject.

`story seal STORY`: re-install every cell's law with management.sealed in place
of management.open. After that no subject, the founder included, can install a
law on any cell of the story. Delegation and revocation stay with the founder,
so friends can still be invited and a GM can still be dismissed.

## The moves, as writes

| verb | write on `{STORY}-player-{S}` |
|---|---|
| `go N` | `write` field 0, value N, expected = current signed `at` |
| `take key` | `write` field 1, value 1, expected = current signed `has/key` |
| `look` | read `at`, print `scene/{at}.md` |

`expected` must be the value just read, not a constant. If `take key` sent
`expected 0`, the second take would be refused at the expected-value check
before the law runs, and J15 would be checking the wrong thing.

The GM's `narrate`/advance writes field 0 (`scene`) or field 1 (`gm/beat`) of
`{STORY}-state`.

The rules of a particular story, and its J15 assertion table, are in that story's own README (`tale/README.md`).
