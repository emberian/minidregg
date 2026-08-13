# minidregg

Formal-first reimplementation of ~/dev/breadstuffs at ≤10% of its LOC: everything
derived via logic-arithmetization compilers and (e)DSLs, nothing hand-written.
The proof-native semantic computer.

**Read `ATLAS.md` before doing anything.** It carries the diagnosis, the sixteen
design laws (each bought with a documented breadstuffs wound), and the
architecture carve. The active design docs: `docs/PROOF-SYSTEM-SURVEY.md` (the
backend decision), `docs/SELVAGE-RECOMPOSITION.md` (the proof system + obligation
ledger), `docs/HYPEREDGE-DESIGN.md` (one turn model), `docs/KERNEL-NECESSITY.md`
(exhibit the kernel, don't design it).

## The laws that bind every session here

- **The derived path is the ONLY path.** Nothing lands beside what it
  supersedes; everything replaces; delete the twin. Before writing any
  AIR/constraint/circuit/executor arm by hand: stop — it comes out of the
  compiler, or the compiler grows the missing vocabulary.
- **Statement-first.** Every keystone enters as a `Prop` with its ATLAS fields
  (satisfiable + teeth + premise-inhabitation) BEFORE proof work starts. A
  wrong statement proved fast is the expensive failure.
- **Green + self-reported done ≠ verified.** Theorem statements get adversarial
  audit; the whole tree builds after any swarm touches shared interfaces
  (per-file green hides a red umbrella).
- **Quote the pessimistic number; state covered scope in the same sentence as
  the claim. Proven parameters only — zero conjectures on the label.**
- **`Theory/` is candidate-independent** — `scripts/check-import-boundary.sh`
  enforces it; keep it green.

## North star: fit to carry tools like helm

minidregg should be *suitable as the substrate under tools like helm* — the
fleet-coordination layer (rooms as cells, posts as signed turns, premises as
attested claims, review verdicts and land-receipts as receipts on chain) is a
first-class target application, not a someday. Design decisions get tested
against "could the helm run on this, better than it runs on dregg1?" Our own
development fleet is the first user.

## Build etiquette

- Iterate single-file: `lake env lean <file>` (fast, race-free). Full
  `lake build Minidregg` is the integration gate — never mid-swarm.
- **On hbox: EVERY build goes through `swarm-build`** (enforced MemoryMax —
  bare cargo/lake OOM'd the box into a power-cycle once already). hbox is
  co-tenant: spare codex's datacake procs (`poly`/`Holmake`); keep waves small
  when they're running.
- Swarm hygiene: commit NAMED files (never `git add -A`), never `git stash`,
  prose commit messages with code spans via `git commit -F`.

## Fleet conduct (remote seats)

Work on lane branches; the steering-station helm (ember's Mac) adjudicates
what lands on main. Unsigned commits are fine and expected while working
autonomously — they mark work for morning review. When blocked on something
only the owner can supply: make it loud (`helm asks add ... --needs ...`),
never a silent tee.
