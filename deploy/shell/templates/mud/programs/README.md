# MUD programs: TEXT, NOT COMPILED

These four files are Hoon-like source for the NOCK lanes (NOCK.md §2.6, "templates a friend edits") and the
MUD-REFEREE / MUD-MOBS-QUESTS / MUD-ORG / MUD-INVENTORY lanes. **None of them has been through `hoonc`.** Some
names are stand-ins (`get`, `put`, `@s` arithmetic via `si`). The shape is the contract, and it is what a lane
must preserve: the sample layout, the output, and the law the output must pass.

## The sample, as every program here assumes it

NOCK.md §2.3 (READ): the sample is `[ctx=[height caller room] inv=(list [key=@t val])]`, and the output is
`(list [key=@t val])`. It is written against that shape, with three ASSUMPTIONS the NOCK lanes must confirm
or change:

1. **`now` in ctx.** `ctx=[height=@ caller=@ room=@ now=@]`. NOCK.md §2.3 says K-CLOCK "changes one field of
   `RunContext` later". Every balance and respawn write needs `now`. If K-CLOCK instead gives `clock/now` as
   an observed input, `now` moves into `inv` under the key `'clock/now'` and nothing else changes.
2. **Keys carry the target index.** `sampleOf` takes `List (AddressCode × Int)` with no cell id
   (NOCK.md §2.3 PROPOSED `sampleOf`). `RunClaim.inputs` does carry `(CellId × AddressCode)`. With two sheets
   as inputs, `hp` would appear twice and could not be told apart. These programs key inputs and outputs as
   `'I/N'`: joint target index `I` (the same index K-JOINT-INDEX uses) and field number `N` (see the kinds'
   `fields.json`). `decodeWrites` needs the same keying to split one run's writes across the two legs of
   a resolution command. **This is a question for K-RAN, not a detail.**
3. **Signed values.** hp goes below 0 (death is admitted). The values are `@s` (Hoon's zigzag signed atom),
   and `Int.toNoun` must be the same encoding.

## Why the affliction table is compiled in

A sample carries field values (integers) and nothing else. So `affliction-table.json` cannot be an input.
It is turned into Hoon constants (the `++table` arm in `resolver.hoon`) and compiled into the resolver's jam.
If the table changes, the jam changes, and so do the programId and `{VK_RESOLVER}`. The sheet law's
`witnessed` clause (`sheet/law.sheet-witnessed`) then has to be re-installed with the new id. "Rules are
versioned content" (MUD §3, DESIGN-verifiable-game) is therefore a law rotation, and it shows up in the
journal.

| file | runner | inputs (joint targets, observe) | writes | output law (must admit every write) |
|---|---|---|---|---|
| `resolver.hoon` | referee | 0 attacker sheet, 1 defender sheet | 0: bal/eq, intent, target, skill · 1: hp, alive, deaths, respawn, aff-* | `law.sheet` clauses 5, 6, 20–30 (REF-side) and 26–27 (attacker proof) |
| `rat.hoon` | referee, signing as the rat's own subject | 0 the rat's sheet, 1 its room, 2 the next room | the rat's `at` + `intent`/`target` | `law.sheet` owner clauses 7–18 (a mob is a sheet under the same law) |
| `tally.hoon` | returning officer | 0 the closed ballot | 0: `result` | `law.ballot` clauses 6, 7 |
| `market.hoon` | market runner | 0 the order book | 0: order slots, `seq` | `law.market`; the Book batch it also emits is accountable only (market.json) |
