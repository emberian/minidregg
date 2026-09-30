# Hermes role templates

`summon ROOM as ROLE [--budget N]` reads `hermes/ROLE/` and nothing else. The
three roles differ only in these files: the grants and the program text (PLACE
§2.7). Placeholders are `{UPPER}` words, substituted textually. Every
placeholder a file uses is listed in its `placeholders` object, or at the top of
its program.

| placeholder | bound by | notes |
|---|---|---|
| `{ROOM}` / `{STORY}` | the ROOM argument | the story role calls it `{STORY}` |
| `{H}` | step 1 | Hermes's subject, decimal |
| `{ACCOUNT}` | step 2 | the name of Hermes's account |
| `{N}` | librarian: `summon`, default 10 | digest cadence in stream entries. In the gm files `{N}` is a scene number from `story.json` |
| `{S}`, `{CELL}`, `{OUT}`, `{IN}` | each `delegateEach` iteration | as each file's `placeholders` says |
| `{P}`, `{INPUTS}`, `{OUTPUTS}`, `{TASK}` | runner only, see `runner/README.md` | |

## `summon ROOM as ROLE [--budget N]`, in order

| step | file | what happens |
|---|---|---|
| 1 | — | enroll Hermes's key, or reuse the one already enrolled. This binds `{H}`. |
| 2 | `ROLE/budget.json` | birth Hermes's account `{ACCOUNT}`, owned by `{H}` and funded from the summoner's account with `--budget N`, or with `fund` if N is not given (the M3 sponsor-funded account path, `product/m3-provision.md:17-22`). |
| 3 | `ROLE/grants.json` | one `delegate` proposal per entry in `delegate`, and one per cell for each `delegateEach` (`over` names the set). Each entry is already the request `delegate` sends today (`shell.rs:480-487`: `name`, `recipient`, `verbs`, `maxCost`; the client requires `observe` among the verbs, `workspace.rs:54-66`). `own` lists cells Hermes creates itself, under its own account, so it needs no grant for them. |
| 4 | `ROLE/program.md` | substitute, then write it to the room's program document `{ROOM}-program-hermes`. Members can read and edit it; Hermes reads it on every attach as its instructions. |
| 5 | — | attach Hermes (M5 phase A). It works only through the MCP tools, which are the client contract: `mini_workspace_read/propose/submit/attempts/import_reference/export_reference` (`product/m5-hermes.md:18-40`). It imports each delegated reference with `mini_workspace_import_reference`. |

For the `gm` role, `summon` also re-installs the story's state and scene laws
with `{GM}` = `{H}` (`grants.json` `relaw`, and `../story/README.md`). That is
only possible before `story seal`.

`dismiss ROOM` revokes the grants from step 3. Hermes's stream and history stay.

## Roles

| role | mutate | observe | program |
|---|---|---|---|
| librarian | `{ROOM}-index`, `{ROOM}-digest` | every other cell of the room | keep the index current, digest every `{N}` stream entries, answer `since` questions from history |
| gm | `{STORY}-state`, every `{STORY}-scene-{N}` | every player cell and player stream | narrate to players, advance the story's scene, never move a player |
| runner | the outputs named in its program | the inputs named in its program | compute outputs from inputs, write nothing else |

PLACE §2.7 says the librarian has mutate on `R/index` only, and its program
writes `R/digest`. Those cannot both hold, so this template grants both cells.
J14's refusal (`lab/paper` refused `no-grant`) is unaffected.

## Budget

`fund` is the default when `--budget` is omitted. Every admitted write costs
`Operation.fee`, which must equal the pinned `tariff.base`
(`product/m8-fleet-surface.md:40-43`; `Kernel/FleetTurn.lean:74,462` on the m8
branch). The one measured value is 3 (`m8-fleet-surface.md:86-87`), so 100 is
about 33 writes. That figure is in `tariffBaseObserved` for people reading the
file; nothing computes with it. When the account cannot pay, the turn is
refused `bookRefused` at plan. `maxCostPerTurn` is the `maxCost` on every grant
(the value J3 used, `shell.rs:1293`). It caps one turn's cost, not the total.

## What binds a runner's writes at assurance level 1

Two things, and nothing else:

1. **The output cell's law.** A write the law refuses is refused, whatever the
   runner meant. Today a law compares a slot with a constant, not with another
   slot (`Pred/Core.lean:103-122`), so it cannot say "the output equals that
   input". That needs K-PRED-SLOTEQ.
2. **The retained signed observations.** Every read Hermes makes is a signed
   Mini read, and M5's attempt journal keeps each attempt's resolution
   (`performed` / `refused` / `uncertain` with a basis). After the fact, anyone
   can check a write against the reads that came before it.

The kernel does not check that the output was computed from the inputs. At
level 1 the runner is accountable, not verified.
