# Developing minidregg: the lane loop

How a lane edits one Lean file, checks it, runs its guards and lands, without rebuilding what another
machine already built and without fighting other lanes over a shared tree. Measured 2026-11-06; the
numbers and the reasoning behind each rule are in redregg-notes
`landscape/ITERATION-SPEED-2026-11-06.md`.

## Rule 1: never run `lake` in a shared tree

`/Users/ember/dev/minidregg` (and `/Users/ember/dev/breadstuffs/metatheory`) are shared by every lane on
the Mac. Any `lake` command there (`lake build`, `lake env lean`, `lake lean`, `lake update`) may check
out the manifest's package revisions. As of 2026-11-06 the Mac minidregg tree's `.lake/packages` are symlinks
into breadstuffs' packages (the switch to the keyed directories below waits on ember), so a minidregg `lake` run checks breadstuffs' Mathlib (v4.30) out to
minidregg's rev (v4.35), and the next breadstuffs run checks it back. The reflogs show this on
10-30 (5,964 v4.35 oleans unpacked into the v4.30 Mathlib), 11-05 and 11-06. While that goes on,
every single-file check in either tree is unreliable.

A lane works in its own clone or worktree and links it to the read-only packages directory for its
manifest:

    git -C /Users/ember/dev/minidregg worktree add /Users/ember/dev/minidregg-lanes/<lane> origin/main
    ~/tools/lean-packages/lean-packages ensure /Users/ember/dev/minidregg-lanes/<lane>     # once per manifest, ~2.5 min
    ~/tools/lean-packages/lean-packages link   /Users/ember/dev/minidregg-lanes/<lane> --mine
    cd /Users/ember/dev/minidregg-lanes/<lane> && bash scripts/build-mini-kernels.sh   # .lake/native, ~30 s

The packages directory is `~/tools/lean-packages/<key>`, where key =
`cat lake-manifest.json lean-toolchain | sha256sum | cut -c1-12`. That is the same key the build
boxes use for `/srv/pool/packages-<key>` and `/home/hbox/pool/packages-<key>`. The directory is
read-only, so a `lake` run with the wrong manifest fails with "Permission denied" instead of moving
the checkout. A manifest bump needs a new key: run `ensure` and then `link`. Never edit a packages
directory in place.

On the build boxes the same rule holds: a lane builds in its own pool tree
(`lane-tree acquire`) or its own clone under its own directory.

## Rule 2: start warm. Fetch oleans, do not rebuild them

A fresh clone has no oleans for the repo's own ~1,400 modules. A cold umbrella build is 40-60+
minutes on bb2. Instead, fetch the snapshot of the nearest ancestor commit that a build box
published:

    scripts/iter-check fetch                 # from bb2's store
    scripts/iter-check fetch --box hbox      # from hbox's store
    lake build --no-build <Module>           # confirm: "All targets up-to-date"

`fetch` walks `git rev-list HEAD` (up to 500 commits back) and takes the first commit the box has
a READY snapshot for. It refuses a snapshot whose `lake-manifest.json` + `lean-toolchain` key
differs from this tree's. It then rsyncs two directories:
- `<store>/<commit>/lib/` into `.lake/build/lib/`: oleans, ileans, IR and traces;
- `<store>/<commit>/ir/` into `.lake/build/ir/`: the generated `.c` and `.c.hash`.

Both are needed. A module's trace lists its `.c` as an output, and Lake rebuilds a module whose
recorded outputs are missing. The first test, with oleans only, left every module stale.

Lake's traces key on content hashes, not paths. A snapshot taken at one path and on one OS is up
to date at another path on another OS. Measured 2026-11-06:
- bb2: a copy of a built tree into a second clone gave `lake build --no-build Minidregg`:
  "All targets up-to-date (10418 jobs)".
- hbox to the Mac: a 324 MB snapshot came across in 135 s, and then `lake build --no-build`
  reported "All targets up-to-date (3006 jobs)" in 6 s.

Modules your branch changed, and their dependents, still rebuild as usual. Boxes publish from a
tree whose tracked `.lean` files are clean at HEAD:

    scripts/iter-check publish               # -> ~/olean-store/minidregg/<commit>/{lib,ir}, READY last

A partial build is publishable: an olean exists only for a module that compiled, and the consumer's
Lake rebuilds anything whose hash disagrees. A snapshot is read-only and hard-linked against the
previous snapshot of the same repo. It is never linked into a live tree, because a Lean `.lake`
must never share inodes with another tree (pool rule). `fetch` copies.

## Rule 3: concrete data by the compiler, general theorems by the kernel

Ember, 2026-11-06: "we DO trust the lean system ... later on when assurance is more important
than iteration time, THEN someone can go ahead and rerun the entire proof process on a verified
lean kernel; this present hybrid is the worst of both tradeoffs." So:

- **Facts about concrete data** are checked by compiled evaluation: hashes, codec outputs on a
  sample, big tables, demo states, test vectors. That means `#guard`, a `lean_exe`, or
  `native_decide` when a downstream theorem needs the fact as a proof.
- **Concrete data is never checked by the kernel.** No `decide`, `decide +kernel` or `rfl`
  through an encoder, a hash or a long table: that made the kernel evaluate cSHAKE (16.5 GB,
  81 s in Kernel.ObjectLaw) or unfold a codec (13 GB).
- **General theorems** (quantified statements) stay kernel-proved.

In this toolchain a `native_decide` does not rest on `Lean.ofReduceBool`. Each use mints its own
axiom, named exactly

    <theorem>._native.native_decide.ax_1_1

(`Lean.Meta.nativeEqTrue`: its type is `<closed Bool expr> = true`), and every theorem that uses
the fact inherits that axiom. The pin rules:

- A theorem proved by `native_decide`, or resting on one, is pinned with `#assert_compiled <theorem>`
  (`Theory/AssertCompiled.lean`). It re-runs the claim and refuses any other axiom. Never pin it with
  `#assert_axioms`, which refuses compiler trust by design.
- A `#guard_msgs in #print axioms <theorem>` pin names the `_native` axiom in its expected
  message. Update it in the same commit that changes the axiom.
- Any `#guard_msgs` over `#assert_axioms_tree`'s "N rest on the compiler trust" count is updated
  in the same commit when the count changes.
- breadstuffs' `orb/Hygiene.lean` admits the axiom only when the theorem's pin lists the
  `nativeDecide` set.

When several facts share an expensive input (the 566 KB
`forge.jam` in `Theory/NockCost`), prove their conjunction with ONE `native_decide` and take each
named fact as a projection. The input is then evaluated once, and every fact pins the one shared
`<conjunction>._native.native_decide.ax_1_1`.

## The loop

    make check-fast                   # here (the Mac): each changed .lean file
    make check-full                   # on the least-loaded box: changed modules + every module importing them
    make check-umbrella               # the umbrella (scripts/pipeline/umbrella-targets), bb2 only
    make boxes                        # what check-full would choose, and why

`FILES="Kernel/Job.lean"` restricts either check. All of them drive `scripts/iter-check` (python3,
no dependencies).

- **check-fast** finds the changed `.lean` files: the diff against the merge base with
  `origin/main` plus untracked files. It runs `lake build --no-build` over their in-tree imports. If
  the imports are stale and the stale set is small (40 jobs; `ITER_FAST_MAX_STALE`), it builds them
  here; otherwise it stops and tells you to use check-full. It then runs `lake lean FILE` per file,
  so the file's `#guard`, `#guard_msgs` and `#assert_axioms` lines run, and times each file.
  It uses `lake lean`, not `lake env lean`. Only `lake lean` passes the lakefile's `leanOptions`
  and `moreLeanArgs` (`--load-dynlib=.lake/native/libmini_kernels_lean.so`,
  `backward.privateInPublic`, ...), so `lake env lean` checks something different from what
  `lake build` checks.
- **check-full** rsyncs the tracked and untracked-not-ignored files to a persistent clone on the
  chosen box. It then builds the changed modules and every in-tree module that imports them.
  Per-file green hides a red umbrella, so the reverse dependents are part of the check. The build
  runs detached under the box's memory containment with a PID file, and the log comes back to
  `.iter-check/<run>/build.log`. `scripts/iter-check status|wait|log|stop [RUN]` manage a run;
  `stop` kills only the PID in that run's PID file, after re-reading its command line.

## Which box (policy of 2026-11-06)

check-full scores every box that answers as `load1/ncpu + used/total` (used = MemTotal - MemAvailable - ZFS ARC, not summed RSS, which counts shared olean pages once per process) and takes the lowest.
A box is skipped when it:

- has less free memory than the job's cap plus headroom (40 GB on bb2 and hbox, 4 GB on forge,
  which is a 32 GB machine);
- has less than 30 GB free on the filesystem that holds its clone (disk pressure is a pause
  condition: a box under the floor takes no new build; hbox was at 21-25 GB on 2026-11-06);
- is in a pause window (forge: 10:00-11:00 UTC, fn2's nightly);
- already holds a live run of this lane (one `lake` per lane per box).

| box | job | cap | LEAN_NUM_THREADS | containment | clone |
|---|---|---|---|---|---|
| bb2 (`ssh bb2`) | umbrella, 32G jobs, medium | 32G | 8 | `swarm-build` | `/home/build/iter-check/<repo>-<lane>` |
| hbox (`ssh hbox`) | medium (12G, < ~10 min) | 12G | 6 | `swarm-build` | `/home/hbox/iter-check/...` (nvme root, never `/tank`) |
| dregg-forge | medium | 12G | 6 | `systemd-run --scope -p MemoryMax=12G nice -n 15` | `/srv/lanes/iter-check/...` (own elan) |

Each box keeps ONE packages directory per manifest key (`<base>/packages-<key>`, or the pool's
`packages-<key>` for minidregg), symlinked from every check-full clone: never a 7.5 GB Mathlib
per clone. A clone is persistent and incremental; a cold one is seeded from the box's snapshot
store before its first build.

Umbrella builds and 32G jobs go to bb2 only. Never touch forge's `demo`, `nano` or `composed`
containers, fn2's `/build`, or its certify lock.

**On bb2, `flock` on the `build` user's PATH is not util-linux.** `/home/build/.elan/bin/flock` is an
obend shim. It ignores the lock for most commands and wraps `lake env lean` in `timeout 60s`. Scripts
that need a real lock there call `/usr/bin/flock` by absolute path.

## Memory: what a module costs

Peak RSS per module, from a cold bb2 build of f54c4205e: 27 modules over 4 GiB, 3 over 12 GiB.
Any module that imports the whole tree (the `Minidregg` umbrella, `Assurance`, the censuses) costs
about 8 GiB just to load its imports. A 12 GiB umbrella build therefore needs at most one such
module running at a time. The per-module table is in the notes. The causes found so far:

- `decide +kernel` over a hash (the kernel evaluates cSHAKE);
- `rfl`/`rw` through a codec's `encode`/`decode`;
- `native_decide` that re-decodes a 566 KB literal in the interpreter for every theorem;
- `decide`/`simp` over string-keyed states that unfold `Nat.repr`.

Statements stay unchanged in every fix.
