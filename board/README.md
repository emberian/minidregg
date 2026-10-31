# How we work (2026-10-31 onward)

One trunk, a board, owned seats, an unattended builder. Supersedes the gate, batch and cadence parts of
docs/COORDINATION-2026-10-27.md; the laws (ATLAS §6) and box rules there still bind.

## The trunk is `main`
- Every seat commits straight to `main` from its own worktree: small commits by path
  (`git commit -F <msgfile> -- <paths>`), `git pull --rebase origin main`, push. Push before verify; fix forward.
  Never force-push `main`, never revert another seat's commit (fix it forward, or tell its owner).
- A commit's acceptance is the narrowest check that could refute it: `lane-check` of the changed Lean files, the
  filtered tests for what it touched, one measurement if it claims speed, and its author read the diff. No
  per-commit gate, no batch, no candidate cut.
- No long-lived side branches. A seat's branch, if it has one, lands on `main` the same day and is deleted.
- `green` is the newest commit the builder found fully green. Rehearsals and the demo ship from `green` on ember's word.

## The builder (unattended, owned by the build-loop seat)
A script on hbox loops on the `main` tip: whole-tree build, the gate rows (tour, enrol, j14-apps, composed; forge
composed via infra), umbrellas, fixture rerecord. It writes `board/REDS.md` and moves `green` when everything
passes. Nobody waits on it; `main` may be red for a while; the owner of a red fixes it forward.

## The board (one owner per file, so nothing conflicts)
- `seats/<seat>.md`: owned by that seat, rewritten whole after every landing: its current agent id, the files and
  paths it owns, its quest, its last commits, its before/after numbers, its next steps, the seams it needs from
  others. This is the address book and the seat's continuation.
- `COSTS.md`: owned by the explorer. Every user-, agent- and operator-visible action with its warm cost, whether it
  grows with history, and its owner, sorted worst first. This is the progress metric. Seats take their worst rows.
- `REDS.md`: owned by the builder. Each red: failure signature (stage, error or refusal text, first divergence),
  "reruns?", "breaks in the same place?", suspect commits, owner.
- `RULINGS.md`: owned by root. Present-state decisions; ember overrules by editing it.

## Talking
- Seats message each other directly for seams, using the ids in `seats/*.md`. The asker may write the change in the
  owner's file; the owner reads the diff.
- Root is for decisions that change a standard, cross-seat rulings, and anything that needs ember. Report events to
  root in three lines or fewer (landed, red, blocked, handoff); no status summaries.

## Measuring
persvati (`ssh persvati-remote`) is the quiet measurement box; hbox is for builds. One standing world per `main` tip
lives there, kept up and hotpatched by anyone; one shared measure script. Before/after goes in the seat's file; the
explorer folds numbers into COSTS.md.

## What binds every seat
The laws (ATLAS §6); law 17, never slower over time; retained mode, a derived value is maintained, never
recomputed (writing f(state) on a hot path means you owe its update rule); about 1 ms of warm work per action is the
direction, and the widest costs come first (the 1,000 ms rows before the 5 ms ones); read and trace the code before
profiling; statement-first, statements may be rephrased but never weakened, no sorry; filtered tests only; every
process gets a PID file and is stopped only by it (no pattern kills); disk pressure means stop and tell ember; no new
data on /tank; builds through swarm-build.

## Seat lifecycle
A seat is long-lived and owns its layer: it orients from the originals and decides its own design and order. At
about 500K tokens root distills it once; after that a fresh seat starts from its `seats/<seat>.md`, root runs
`cv retire <old> --successor <new>`, and the new seat rewrites its row with its id the same hour.
