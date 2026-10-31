# MUD templates

Data for a MUD on Mini: a character sheet, rooms, items, quests, organisations, a market and the
Tidewrack realm. No shell verb loads these files: `native/resource-client/src/shell_grammar.rs` has no
`area`, `strike`, `cast`, `flee`, `give`, `buy` or `org` leaf. They are read by

- `native/resource-client/journey.d/jclock.sh:340-363`, which substitutes `law.management.json`,
  `sheet/law.sheet.json`, `sheet/init.sheet.json` and `tidewrack/realm.json`, births one sheet on a
  journey Host (`create --fields 0-14`, init, grant, install `law.management ; law.sheet`) and drives
  the sheet's clock clauses (`:364-395`);
- `scripts/gen-sheetlaw.py` and the theorems in `Assurance/SheetLaw.lean` and `Assurance/ItemLaw.lean`.

Scope of the evidence: those are the only places a template meets a Host. The last recorded run of
`jclock.sh` is `K-CLOCK FAIL 21/32` in all three CI runs of 2026-10-26
(`docs/review/2026-10-26-native-crates/resource-client--G-journeys-contracts.md:153`); which rows failed
is not recorded there, so no sheet row is evidenced as passing. `docs/evidence/2026-10-05-clock-law/`
is the pay-clock journey (`jpay3.sh`), not a sheet. `validate.py` is a copy of the realm-loading rules,
not the kernel, and the programs under `programs/` have not been through a Hoon compiler
(`programs/README.md`).

## Layout

One directory per kind (`sheet/`, `room/`, `item/`, `quest/`, `org/`, `market/`), the realm under
`tidewrack/` (`realm.json`, areas), and `affliction-table.json`, `tariff.json`, `law.management*`.

- `*/fields.json` is the map from field names to field numbers (fields are numbers, never names:
  `Kernel/DeclaredResourceProjection.lean:17-22`). Read the file; the numbers are not repeated here.
- `law.X` is the source and `law.X.json` is rendered from it by `render.py`; never edit the JSON by hand
  (`sheet/README.md`). Clause numbers in `-- N name` comments are indices in the composed law and are
  only ever appended to.
- **Composition.** A cell's installed law is `law.management ; law.KIND [; appended files]`, in JSON
  `{"type":"all","predicates":[<management>, ...<law.KIND>.predicates, ...]}` (as `jclock.sh:349-351`
  builds it). Management is clause 0.
- **Placeholders.** `{UPPER}` words are substituted textually before parsing, from the realm's
  `constants` and the subjects involved (`jclock.sh:345-348`); every value must be a canonical decimal
  string.

## What the laws need from the kernel

Each is in the code today; the table says where.

| need | where |
|---|---|
| `eqSlots`, `leSlots`, `leSlotsOff A B k` (`new[A] <= new[B] + k`, JSON keys `type left right offset`) | `Pred/Core.lean:182-186`, `Host/Json.lean:307-312` |
| `clock/now` | `Kernel/DeclaredResourceController.lean:512-517` |
| `joint/index/{i}/resource/field/{n}/{view}` (i = the command's 0-based target order) and `joint/target/{id}/...` | `Kernel/DeclaredResourceController.lean:274` |
| delegation scope `fields` and `maxDelta` | `native/resource-client/src/workspace.rs:3405-3420` |
| `witnessed` | no host discharges it, so the compiler refuses any law containing it (`Compiler.supported_no_witnessed`); `law.sheet-witnessed` therefore cannot be installed today |

A clause that reads an absent slot is false (`Pred/Core.lean:166`), so a clause that
needs a slot fails closed. Never put a clock or joint atom under `not`: that turns "absent" into
"admitted". The sheet writes the positive bound instead (`leSlotsOff clock now X {NEG_K}`).

## Not settled

- The consuming verbs for rooms, items, quests, organisations and markets do not exist; the field maps,
  the move table and the ids (realm-local numbers, a sheet's id = its subject) are the design a verb would
  follow, and no kernel run checks them.
- `go DIR` with no exit in that direction produces no write, so the shell, not the law, would have to
  refuse it; the law refuses a destination no exit of the current room reaches (clause 16).
- `org/offices.json` `valid_until`/`notAfter` is a block height.
