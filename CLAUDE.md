# minidregg

Formal-first reimplementation of ~/dev/breadstuffs at ≤10% of its LOC: everything
derived via logic-arithmetization compilers and (e)DSLs, nothing hand-written.
The proof-native semantic computer.

**Start with `HANDOFF.md`**, then the plan `docs/DEMO-PREFIX-2026-10-26.md` (the work
and the public-opening contract) and **`board/README.md` (how we work now: `main` is the trunk, the board, owned seats, the builder; read
`board/RULINGS.md` and your `board/seats/<seat>.md` next)** and `docs/COORDINATION-2026-10-27.md` (older:
what we optimise, the gates and their verdicts, how a lane and the orchestrator work,
the boxes, the cadence)**. `ATLAS.md` §6 carries the seventeen design laws.

## The laws that bind every session here

- **The derived path is the ONLY path.** Nothing lands beside what it
  supersedes; everything replaces; delete the twin. Before writing any
  AIR/constraint/circuit/executor arm by hand: stop — it comes out of the
  compiler, or the compiler grows the missing vocabulary.
- **Statement-first.** Every keystone enters as a `Prop` with its ATLAS fields
  (satisfiable + teeth + premise-inhabitation) BEFORE proof work starts. A
  wrong statement proved fast is the expensive failure. Only a lane's top-level
  theorem must be non-vacuous; it gets an adversarial audit of its statement.
- **Green + self-reported done ≠ verified.** The whole tree builds once, on the
  build box, after lanes touch shared interfaces (per-file green hides a red
  umbrella).
- **Quote the pessimistic number; state covered scope in the same sentence as
  the claim. Proven parameters only — zero conjectures on the label.**
- **Performance is published, never a gate.**
- **`Theory/` is candidate-independent** — `scripts/check-import-boundary.sh`
  enforces it; keep it green.

## North star: fit to carry tools like helm

minidregg should be *suitable as the substrate under tools like helm* — the
fleet-coordination layer (rooms as cells, posts as signed turns, premises as
attested claims, review verdicts and land-receipts as receipts on chain) is a
first-class target application, not a someday. Our own development fleet is the
first user.

## Where things run (COORDINATION §5)

- **The Mac**: edit, `cargo check`, filtered macOS-runnable unit tests. Its `.lake`
  is stale: no Lean rebuild here.
- **`dregg-build`** (`ssh dregg-build`, lanes user `lanes`, worktrees under
  `/build/lanes/<lane>`): every Linux check, `lake env lean <file>`, Lean builds,
  the integration build, candidates, the nightly. Every build goes through
  `swarm-build <cmd>` (enforced MemoryMax 28 G; prints the build's peak RSS).
- **hbox**: the pipeline's standing run and warm base only; co-tenant; never a
  lane's default; never a timing measurement (`/tank` is an HDD mirror).
- **`dregg-demo`**: rehearsals and the opening; never a build.

## Hygiene

- One worktree per lane on a `lane/<name>` branch; never the main worktree.
- Named-file commits (never `git add -A`); never `git stash`; prose commit
  messages with code spans via `git commit -F <uniquely named file>`.
- Filtered tests only, run once per coherent batch; never an unfiltered suite.
- Every process you start gets a PID file; stop a process by the PID in its PID file,
  and only that. No `pkill -f`, `pkill -x`, `killall`, `kill -u`. No PID file: say so instead.
- Per-lane `CARGO_TARGET_DIR` and scratch subdirectory; no foreground waits (`box-wait`
  in one background call); no "was it red before me" baselines; REPL-first Lean; no
  whole-file `Read` over 2,000 lines (COORDINATION §3 states each).
- The gate is the tour (`jtour` plus the composed scenario); standing rows are the
  nightly's and never a candidate's reds (COORDINATION §6).
- Disk pressure is a pause-and-tell condition, never a delete.
- Unsigned commits are fine and expected while working autonomously.
