# Shell templates

These are the files that `mini shell` verbs load without changing them. Lane
P-STORY built the story verbs on `story/`, and lane P-HERMES-ROOM builds
`summon`, `ask` and `dismiss` on `hermes/`. Each directory's README gives the
order in which its verb reads its files.

| verb | reads | contract |
|---|---|---|
| `story new NAME --from tale\|@FILE` | `story/tale/table` (compiled into `mini`) or `HOME/requests/FILE`; runs `room/story/template.shell` | `story/README.md` |
| `story seal NAME` / `story invite NAME S` / `look` / `go` / `take` / `act` / `narrate` | the table document; the law each player's cell carries is generated from it (`story/tale/law.player*`, `scripts/gen-storylaw.py`) | `story/README.md` |
| `summon ROOM as librarian\|runner [--budget N]` (gm: marked for MUD-GM) | `hermes/ROLE/budget.json`, `grants.json`, `program.md` (compiled into `mini`) | `hermes/README.md` |
| `ask ROOM TEXT` | the room cell's `hermes` field (a signed read) | `hermes/README.md` |
| `dismiss ROOM` | the summon record `HOME/hermes/ROOM.json` (the grants it made) | `hermes/README.md` |
| `room new NAME --template workroom\|social\|story` | `room/T/template.shell` (compiled into `mini`; `room template show T` prints it) | `room/README.md` |
| `room welcome NAME SUBJECT --template social` | `room/social/member.shell` | `room/README.md` |
| `chat new ROOM` / `chat invite ROOM S` | `room/chat/law.author.json` (compiled into `mini`; `@SUBJECT` = the founder, or S) | `room/chat/README.md` |
| `room new NAME --private` | `room/private/law.room.json` (the room), `room/private/law.keys.json` (its keys cell, `@FOUNDER` replaced) — compiled into the client with `include_str!` | `room/private/README.md` |

`law.X` is the §2.6 one-line grammar. `law.X.json` is the same predicate as
`Pred` JSON, which `law ID REF @FILE` installs today: shell.rs wraps it as
`{"type":"minidregg-workspace-proposal-v1","action":"install-policy","name":REF,"predicate":<file>}`
(`native/resource-client/src/shell.rs:489-496`, `json_argument` at `:231-243`).
The client passes it through to the install-source declaration
(`workspace.rs:697-725`). The Host parses it with exact keys and canonical
signed decimal strings (`Host/Json.lean:139-145, 206-230`). `@FILE` is read
from `HOME/requests/FILE`, a plain name (`shell.rs:231-238`), so a verb has to
copy the substituted template there before it installs it.

## What the templates rely on, and where it was read

Each item is marked READ (seen at source), MEASURED (seen in a run's
artifacts), or ASSUMED (my choice or inference, not checked).

1. **READ: `before` slots can be addressed.** `scalarSlots` emits
   `resource/field/{n}/before`, `/after` and `/delta`
   (`Kernel/DeclaredResourceProjection.lean:13,28-36`). For a mutate, the policy
   sees `old = project(pre, pre)` and `new = project(pre, post)`
   (`Compiler/CanonicalPolicyAdmission.lean:190-191`,
   `Kernel/DeclaredResourceController.lean:131-141,181-193`). So `eq …/before v`
   reads the pre value. `monotone` and `writeOnce` go on `/after`: they compare
   old `/after` (pre) with new `/after` (post). On `/before` they would always
   hold. A field created in this turn has no `/before` or `/delta`, and atoms
   that read those fail closed on it.
2. **READ: field keys are numbers, not names.** `values` keys on
   `field.value : Nat` (`DeclaredResourceProjection.lean:18-22`), and the shell
   sends `"field":"2"` (`shell.rs:466-471`). `scene`, `player/S/at` and
   `has/key` are not slots. `story.json` `fields` maps each name to a number, and
   the law files use the numbers.
3. **READ: a cell has one law, and it governs every verb.** An installPolicy is
   judged under the current law with only `request/*` and `policy/*` slots
   (`Kernel/PolicyInstallController.lean:250-259`). A delegation is judged with
   `request/*`, `command/bytes`, `resource/bytes` and `authority/*`
   (`Kernel/CapabilityDelegationController.lean:342-347`). Neither has any
   `resource/field/*` slot. MEASURED: J8 shows `any []` refuses reads and the
   owner's repair (`product/mj-journey.md`, J8 row).
4. **READ: verb tags.** observe = 1, mutate = 2, delegate = 3,
   installPolicy = 4, revokeCapability = 5
   (`Compiler/CredentialAuthorityEntryCodec.lean:71-82`). That is the table
   `request/verb` is projected from (`Compiler/CanonicalRuntimeProfile.lean:116`).
   **Trap:** `Theory/AuthorizationDeclaration.lean:69-80` has a second `verbTag`
   with different numbers (installPolicy = 10, revokeCapability = 11). A law
   that uses those numbers never matches.
   ASSUMED: a plain `read` carries verb 1, which `observeVerb` suggests
   (`DeclaredResourceController.lean:148-152`). ASSUMED: a revoke on an object
   cell is judged under that cell's law with verb 5.
5. **READ: the atoms.** `eq` / `le` / `memberOf` / `writeOnce` / `monotone` /
   `witnessed` / `not` / `all` / `any`, and none of them compares one slot with
   another (`Pred/Core.lean:103-122`, eval `:193-211`).
6. **READ: `writeOnce` does not refuse rewriting the same value.** With
   `old = 1`, a write of `1` passes (`Pred/Core.lean:202-204`). The second
   `take key` is refused by the `take-once` clause, not by `writeOnce`.
7. **ASSUMED (P-LAW is writing it now): the grammar.** The law files use only
   forms that appear in PLACE §2.6 and §2.8: `field N [before|after|delta] == v`,
   `field N in {…}`, `field N monotone`, `field N writeOnce`, `subject == v`,
   `verb == v`, `any [ … ]`, `all [ … ]`, `not ( … )`, clauses separated by `;`,
   with newlines treated as whitespace. One form is extrapolated: `verb in {…}`
   (from `field N in {…}`). It renders to `memberOf "request/verb"`.
   `field N monotone|writeOnce` renders to the `/after` slot (item 1).
8. **READ: names.** A reference name is a word (letters, digits, hyphens) or
   words joined by `/` under a room (`lab/index`; `workspace.rs`
   `validate_ref_name`, stored as `refs/lab.index.json`). These story
   templates still spell their cells `{STORY}-state`, `{STORY}-scene-{N}`,
   `{STORY}-player-{S}`; the room templates (`room/`) use `$ROOM/index`.
9. **ASSUMED: scene docs are content cells.** They are written by whatever
   doc verb the room lanes build: the client accepts content
   `createAtom`/`createDocument`/`createRun` only (`workspace.rs:580-605`), and
   the body shape was not read. The `.md` files are the text to put in them.
10. **MEASURED: a declared cell holds only a few fields.** K4 was refused at
    field 4 of 32 (`mj-journey.md`, K4 row), so each tale cell uses 2.
11. **READ: delegate shape.** `name`, `recipient`, `verbs`, `maxCost`, all
    strings (`shell.rs:480-487`), and `observe` must be among the verbs
    (`workspace.rs:54-66`). `maxCost` 50000 is the value J3 used
    (`shell.rs:1293`). ASSUMED to cover a scalar write's cost.
12. **READ: fee.** `Operation.fee` = the pinned `tariff.base`
    (`product/m8-fleet-surface.md:40-43`). MEASURED: it was 3 in M8's run
    (`:86-87`). ASSUMED: `summon`'s account pays with this fee, not with M5's
    grain tool-purse charge. Those are two different meters today.
