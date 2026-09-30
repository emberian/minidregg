# sheet: the MUD character-sheet law

`law.sheet` is the source. `law.sheet.json` is rendered from it by `../render.py` and must never be edited by
hand. The installed law is `law.management ; law.sheet`, so clause 0 is management. Numbers are indices in
that composed law and are the numbers refusals print. **Clauses are only ever appended.** Inserting one would
renumber every clause after it, which breaks every refusal string, every `sim.py` expectation and the clause
numbers SHEET-ITEM-LAW's theorems cite. The appended files continue the numbering.

| # | name | guards | needs |
|---|---|---|---|
| 0 | management | reads and mutates pass; delegate / installPolicy / revoke only for `{W_FOUNDER}` | — |
| 1 | writer | only `{S}` and `{REF}` mutate | — |
| 2 | pinned | `id == {S}` | — |
| 3 | range | alive, afflictions, ward in {0,1}; intent, skill are known codes | — |
| 4 | deaths-monotone | deaths never falls | — |
| 5 | deaths-count | deaths moves by exactly +1, only on alive 1→0 | — |
| 6 | dead-at-zero | hp ≤ 0 ⇒ alive = 0 | — |
| 7 | owner-alive | a dead owner writes only intent := pray | — |
| 8 | owner-fields | the owner never writes combat fields | — |
| 9 | pray-dead | pray only while dead | — |
| 10 | bal | owner's physical intent needs bal ≤ now | K-CLOCK |
| 11 | eq | owner's cast needs eq ≤ now | K-CLOCK |
| 12 | paralysis | paralysed: no physical intent, no walking | — |
| 13 | asthma | asthmatic: no cast | — |
| 14 | move-from | joint 1 is the room I am in | K-JOINT-INDEX |
| 15 | move-to | joint 2 is the room I arrive in | K-JOINT-INDEX |
| 16 | exits | some exit of joint 1 is joint 2 | K-JOINT-INDEX |
| 17 | door | a locked exit needs its key (joint 3), held by the mover | K-JOINT-INDEX |
| 18 | dark | a dark room needs a lit lantern (joint 3 or 4), held by the mover | K-JOINT-INDEX |
| 19 | lease | a leased room admits only while now ≤ until | K-CLOCK, K-JOINT-INDEX |
| 20 | ref-at | the referee moves a sheet only when reviving it | — |
| 21 | no-heal | the referee never raises hp except on revive | — |
| 22 | maxhit | hp/delta ≥ −MAXHIT | — |
| 23 | revive | alive 0→1 only by `{REF}`, after a prayer and respawn ≤ now, to HPMAX at HOME | K-CLOCK |
| 24 | respawn-at-death | respawn moves only on alive 1→0 | — |
| 25 | death-timer | dying: `now ≤ respawn − RESPAWN` (**positive form, fails closed**) | K-CLOCK, K-PRED-OFFSET |
| 26 | attacker | hurting needs a live attacker at joint 0, same room, whose intent names me | K-JOINT-INDEX |
| 27 | attacker-paid | the attacker had bal/eq ≤ now and paid: `now ≤ bal − COST` / `now ≤ eq − ECOST` (**positive form**) | K-JOINT-INDEX, K-CLOCK, K-PRED-OFFSET |
| 28 | bal-paid | the referee raises bal only for my physical intent, to `now ≤ bal − COST` (**positive form, fails closed**) | K-CLOCK, K-PRED-OFFSET |
| 29 | eq-paid | the same for eq and cast, `now ≤ eq − ECOST` (**positive form, fails closed**) | K-CLOCK, K-PRED-OFFSET |
| 30 | intent-clear | the referee only clears intent, target and skill | — |
| 31 | ward | a raised ward blocks paralysis | — |
| 32 | defend | a ward is raised only on my own defend intent | — |
| 33 | death-needs-hp | alive 1→0 only with hp/after ≤ 0 (the converse of 6) | — |
| 34 | witnessed (`law.sheet-witnessed`) | a referee write is the resolver's run | K-RAN |
| 35 | cure-burns (`law.sheet-cure-lawful`) | an affliction falls only in a turn that burns its herb | K-BOOK-SLOTS |

## Corrections from SHEET-ITEM-LAW (`planning/mud/sheet-item-law.md`)

- **33 death-needs-hp** was added because of `referee_kills_healthy_sheet`. Before it, the referee could zero
  `alive` and bump `deaths` on a sheet at hp 3 with no attacker, and every clause admitted it: 6 forced only
  "hp ≤ 0 ⇒ dead", and 26 fires only when hp falls. The death is one step, because the resolver writes hp and
  alive in one product, and 6 already refuses a lethal hp that leaves alive at 1. The pole is
  `fixed_law_refuses_smite_admits_strike`, and in `sim.py` it is J-MUD-3 r8c (smite refused at 33) and r8
  (the combat death is still admitted).
- **25, 27, 28, 29** used to read `not (leSlotsOff X clock now K-1)`. With no `clock/now` slot the atom is
  false, so the `not` is true, and the clause admitted anything. They now read
  `leSlotsOff clock now X {NEG_K}`, which is the same inequality over the integers (`X ≥ now + K` ⇔
  `now ≤ X − K`) and is false when either slot is missing. Constants: `NEG_COST = −COST`,
  `NEG_ECOST = −ECOST`, `NEG_RESPAWN = −RESPAWN`, written `"0"` when RESPAWN is 0. `validate.py` derives and
  checks all three. `sim.py` rows r2c, r2h, r8d, r8f and J-MUD-4 r2f are the no-clock refusals. Rows r2d, r2g
  and J-MUD-4 r2e are the one-short boundaries.
- **Rule:** never put an atom that reads a possibly-absent slot (clock, joint, Book) under `not`. Write the
  positive bound.
