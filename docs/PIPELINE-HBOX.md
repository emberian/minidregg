# The landing pipeline on hbox

Goal: a lane can **land by the rule** on hbox without a rented burst box (PROTOCOL-20261009 §6–7). "Landed" means
the commit is on GitHub main AND a full static gate is red=0 at that sha AND the standing journey run at that sha has
every required row PASS. A required row may also be UNCONFIGURED, but only when the missing input is one the box
declares absent. Tools never run from an installed copy. RETRO-20261008 §d counted four stale-installed-copy
incidents in one day. On hbox that class has no file to go stale: nothing in the pipeline executes from a
copied script.

## Layout (everything under /tank/dregg-build; no /srv)

| path | what |
|---|---|
| `/tank/dregg-build/pipeline/box.env` | the ONE env file. Written by `scripts/pipeline/box-env --layout /tank/dregg-build/pipeline ...`. Every pipeline script reads it through `lib.sh` once `PIPELINE_ROOT=/tank/dregg-build/pipeline` is exported |
| `.../pipeline/warm-base/{src,FROZEN,logs}` | the built, read-only base (umbrella replays 0 modules). Lanes are made by `warm-base/src/scripts/pipeline/mk-lane.sh`, the base tree's own copy |
| `.../pipeline/lanes/<lane>/{src,logs}` | mk-lane clones (`cp -al` .lake, allow-listed shared inodes) |
| `.../pipeline/artifacts/<tip>/` | READY sets (publish-artifacts), labels `next`/`green`/`main` |
| `.../pipeline/journeys/<tip>/` | standing-run results (`results.tsv`, `table.txt`, `rows/`, `DONE` or `REFUSED`). `journeys/.trees/<tip>/` holds the set's source tree, read-only, which the run executes |
| `.../pipeline/slots/build-slot-{1,2,mk}` | lane slots and the gate slot (flock files). swarm-build's cgroup caps memory |
| `.../pipeline/absent-inputs.tsv` | the box's DECLARED absent product inputs (below) |
| `.../pipeline/pylib/` | PyNaCl 1.6.2 wheel, unpacked after a sha256 check. hbox's python3 has no nacl and no pip; `PYTHONPATH` in box.env lets JPAY1–4 run |
| `~/.config/systemd/user/pipeline-journeys.{service,timer}` | the standing run (below) |

The shared git remote is the bundles mirror `/tank/dregg-build/claude-lanes/bundles/burst3-minidregg.git`
(`PIPELINE_SHARED_GIT`).

### box.env (as written 2026-10-14; re-run with the cache line below)

```
scripts/pipeline/box-env --layout /tank/dregg-build/pipeline \
  --slots "/tank/dregg-build/pipeline/slots/build-slot-1 /tank/dregg-build/pipeline/slots/build-slot-2" \
  --gate-slots /tank/dregg-build/pipeline/slots/build-slot-mk --lean-threads 8 \
  --shared-git /tank/dregg-build/claude-lanes/bundles/burst3-minidregg.git \
  --lake-cache /tank/dregg-build/pipeline/lake-cache \
  --set "PIPELINE_LEANENV_WAIT_S=0 PIPELINE_JOURNEY_JOBS=8 PYTHONPATH=/tank/dregg-build/pipeline/pylib"
```

- `--lake-cache DIR`: the box's one shared Lake artifact cache. box.env exports `LAKE_CACHE_DIR=DIR` and
  `LAKE_ARTIFACT_CACHE=true`; there is no shim and no PATH entry (the old `--no-lake-shim` refused the
  installed-copy PATH entry and, with it, the cache: hbox lanes recompiled each other's modules, e.g. 823
  modules / 8,046 s in land-perffix4, CYCLE-TIME-20261016 §2 T2). The guard, `lake-cache-audit --since
  --purge`, runs from the tip tree's `lib.sh` (`pipeline_cache_audit`) before every slot build, lane-check,
  landing gate and publish.
- `PIPELINE_LEANENV_WAIT_S=0`: hbox has no lean envs, so `objective` is UNCONFIGURED. It was UNCONFIGURED on
  burst3 too, and it is not a required row.

### What was generalized, not forked

The /srv paths were defaults. Each edit makes a default come from box.env:

- `box-env --layout DIR` sets `PIPELINE_ROOT` and the roots `ARTIFACT_ROOT`, `JOURNEY_ROOT`, `PIPELINE_LANES`,
  `PIPELINE_WARM_BASE`, `PIPELINE_NEXT_BASE` and `PIPELINE_GATE_SLOT`, all under DIR. It also gains
  `--shared-git`, `--set` and `--lake-cache`.
- `lib.sh` `pipeline_find_tree`: the next base comes from `PIPELINE_NEXT_BASE`.
- `mk-lane.sh`: the `shared` remote comes from `PIPELINE_SHARED_GIT`.
- `advance-base-burst.sh`: the probe lane goes under `$LANES`. `$W/mk-lane.sh` is now a **relative symlink**
  into the base tree, not a copy.
- `journey-rows` hostupgrade: the EF set is looked up under `$ARTIFACT_ROOT`; `HOSTUPGRADE_EF_SET` overrides it.

## The standing run: the set's own tree, never a copy

`scripts/pipeline/install-journey-units` writes the units; re-run it after changing the generator. The service is a
oneshot, kicked every 5 min by the timer and immediately by `landing.sh`. Its **only** logic is an inline
dispatch:

1. Take the first label among `next`, `green`, `main` whose READY set has no `DONE` or `REFUSED` run.
2. Check the set's `SHA256SUMS`; `source.tar` is listed there.
3. Extract `source.tar` once into `journeys/.trees/<tip>` and make it read-only.
4. Log `dispatch: tip T (label) runs <tree>/scripts/pipeline/journey-runner sha256:<…>`.
5. `exec` that runner with `--tip T`.

The runner, rows, `lib.sh` and `journey-red-lines` are therefore always the tip's own. Logs:
`journalctl --user -u pipeline-journeys`.

The runner also guards itself. `journey-runner --version` prints its path and sha. In `run_tip`, its
`journey-runner`, `lib.sh` and `journey-red-lines` must be byte-identical to the copies in the tree the rows come
from: the lean env or source.tar, or the `--source-tree` override if given. If they differ, it prints both
sha256s, writes `TIP/REFUSED` and exits 3. The loop does not retry a refused tip.

## landing.sh TIP

`scripts/pipeline/landing.sh` runs on hbox with `PIPELINE_ROOT=/tank/dregg-build/pipeline`:

```
cd /tank/dregg-build/pipeline && PIPELINE_ROOT=$PWD setsid nohup bash <tree>/scripts/pipeline/landing.sh TIP \
  > logs/landing-TIP.log 2>&1 < /dev/null & echo $! > logs/landing-TIP.pid
```

1. Create a lane with the **base tree's** mk-lane. Fetch TIP from the shared repo and check it out (`main`).
   If TIP carries a different `landing.sh`, hand off to it (`exec … --in-lane`). If TIP predates landing.sh,
   the log says so and names the copy that continued.
2. Run TIP's own `run-gate-burst.sh`: the umbrella in the gate slot under swarm-build, then
   `merge-gate-checks.sh`. It waits while the 1-min load is above 20. It needs `umbrella PASS` and
   `TOTAL red=0 HEAD=TIP`; otherwise exit 10.
3. Run TIP's own `publish-artifacts TIP next LANE/src`. This is the gated tree, so nothing compiles. It smokes
   the set, writes READY and sets the `next` label. Failure exits 11.
4. Kick `pipeline-journeys.service` and wait for `journeys/TIP/DONE`. A refusal or a timeout exits 12.
5. Print the verdict. It opens with two greppable lines from the service's dispatch record
   (`journeys/.trees/TIP.dispatch`). `RUN-TREE` gives the tree, the runner path and sha256, and the
   source.tar sha256. `SELF-CHECK PASS|FAIL` says whether the executed runner is byte-identical to
   `git show TIP:scripts/pipeline/journey-runner` from the shared repo; FAIL exits 12. If the plant marker
   exists, a `STALE-COPY EXECUTED` line follows. Then the verdict body: `awk -F'\t' '$2!="PASS"' results.tsv` and the row count. Then check every id in
   `required-rows`, read from the **main base's** tree so a lane cannot drop its own required rows. Each must be
   PASS, or UNCONFIGURED with a detail that matches that row's declaration in `absent-inputs.tsv`. A required id
   with no line in results.tsv is MISSING. Exit 0 only if every required id passes this check; otherwise exit 13.
   The verdict is also written to `LANE/logs/landing-TIP.txt`.

`landing.sh --check TIP` runs only step 5, against a finished run. landing.sh never pushes; the root pushes main
from the results.tsv it has read.

### required-rows

The ids come from MATURATION-MAP-20261009 §3. A row id covers its sub-rows. A parent that is UNCONFIGURED only
because of declared sub-rows is accepted. Two rows on the map do not exist yet: HERMES-LIVE and jcertify. They are
`pending` lines: printed on every landing, not counted. The first time a row of that name appears in results.tsv, it
is required automatically (ROOT, 2026-10-14).

`births` (THE BAR) exists and runs on every landing, but its line is `pending births when-green-at-main …`: it
becomes required only once main's own baseline run has it PASS. Until then landing.sh prints
`pending   births (when green at main; main's baseline: …; candidate: …)` and does not count it. Rule (b) below
still applies to it, so once main is PASS a candidate that turns it red is a NEW RED.

## The bar per landing: `births`; the soak: the nightly

THE BAR (cv 01a0f9c0-521b) is on CREATES: write p99 <= 5 s, cold reopen <= 60 s. The standing run judges it with
`births` (journey-rows `row_births`): `scripts/perf/workload.py --births-only` on a fresh native Store: genesis,
setup, `PERF_BIRTHS_N` births (default **64**), then the Host stopped by its PID file and restarted on the same
Store, timed to the first answered read. PASS iff all N resource writes and N `create` turns completed, each
op's p99 <= 5 s, and the reopen <= 60 s; FAIL names the op and the bound. The detail carries create p50/p99/max,
resource p99, reopen, cells and records at the end, the Store size, and the 1-min loadavg at start and end: a loaded
box is recorded, never a reason to skip (the row has no UNCONFIGURED-for-load path, unlike `perf`). Sub-rows
`births/create`, `births/resource`, `births/reopen`. Plant: `JOURNEY_PLANT_BIRTHS=bar-1ms`
judges the same run against a 0.001 s write bar and must FAIL naming `births/create p99 … > 1 ms bar`.

`growth` (1000 records through journey.sh; 2,436–5,401 s; it measures UPDATES on existing cells and flipped PASS/FAIL
on the same bar with box load, FOLLIES-20261014 F1) is **not** in a landing's standing run: journey-rows appends it
to `JOURNEY_ROWS` only when `PIPELINE_NIGHTLY=1`.

### Nightly

The nightly is the 1000-create run plus the full growth soak, against the `main` set, into its own results root
(never `$JOURNEY_ROOT`: run_tip moves an existing `TIP/` aside, which would hide the standing run from landing.sh).
With `PIPELINE_NIGHTLY=1`, `births` defaults to N=1000 (`PERF_BIRTHS_N` overrides) and `growth` is in the row set:

```
cd /tank/dregg-build/pipeline && T=$(readlink artifacts/main) && tree=journeys/.trees/$T && \
  PIPELINE_ROOT=$PWD PIPELINE_NIGHTLY=1 PIPELINE_ROW_TIMEOUT_S=7200 setsid nohup bash $tree/scripts/pipeline/journey-runner \
    --tip $T --row births --results-root $PWD/nightly > logs/nightly-births-$T.log 2>&1 < /dev/null & echo $! > logs/nightly-births.pid
# then the same with --row growth (logs/nightly-growth-$T.log, logs/nightly-growth.pid), after births has finished
```

Results: `nightly/<tip>/{results.tsv,table.txt,rows/}`. The nightly blocks nothing; it is the measurement a Store
change that claims a speedup is judged by.

### One row by hand (a lane verifying its own row)

`--source-tree` runs the lane's rows against an existing READY set; the self-check then compares the runner with
the lane tree's own:

```
cd /tank/dregg-build/pipeline && PIPELINE_ROOT=$PWD bash LANE/src/scripts/pipeline/journey-runner \
  --tip $(readlink artifacts/next) --row births --source-tree LANE/src --results-root LANE/journeys
```

### absent-inputs.tsv (hbox, measured 2026-10-14)

| row | detail regex | why absent |
|---|---|---|
| m6grain | `^missing input: operator uid 1001 ` | the pipeline runs as uid 1000 (`hbox`). There is no uid-1001 operator account or subuid range |. Also hard-coded: the operator name `ember`; the row needs the runner itself at uid 1001, and then hits the bwrap userns restriction (spk-host uses /usr/bin/bwrap) |
| hostupgrade | `^missing hostupgrade candidate input: .*/e0a8ba21…$` | the pinned old-epoch EF set existed only on burst3 |
| hostupgrade/HOST-UPGRADE-PREVIOUS | `^no previous READY main set with the tip Store epoch$` | no same-epoch main set has been published on hbox yet |
| hermes | `^missing input: unprivileged user namespaces for bwrap ` | hbox has `kernel.apparmor_restrict_unprivileged_userns=1` and no AppArmor profile that lets bwrap create a user namespace (`bwrap: setting up uid map: Permission denied`). **DECISION PENDING (Ember, box security):** until a bwrap profile exists, hbox landings do not prove hermes. JPAY6 accepts this message too (its probe comes before TEST_PROVIDER) |

Supplied 2026-10-14 (INPUTS-HBOX), no longer declared: **m7** takes its reference from the newest other READY
set with identical compiled inputs (journey-runner `m7_reference_for`); **exchange** gets `MINI_FN_LAUNCHER`/`MINI_FN_CORE`
from box.env = a verified copy of fn's 6679dae0e image at `$PIPELINE_ROOT/inputs/fnbin/6679dae0e/` (outside /tank/fn,
which the row forbids); **JPAY6** gets `MINI_TEST_PROVIDER_BIN`/`MINI_LAUNCH_GATE_BIN` from box.env
(`$PIPELINE_ROOT/inputs/fixtures/7ffd6524/`, built from the tree; same sources at next) and its userns probe tries
`/usr/local/libexec/mini-grain-bwrap`, the AppArmor-profiled copy jpay6.sh itself falls back to.

`sudo -n true` succeeds, `Linger=yes` is set for `hbox`, and sshd, bwrap and jq are present.

Verdict check tested on main 7dea0626's burst3 results.tsv: 40 ids, 0 not met. Planted variant (m3 FAIL, m8
UNCONFIGURED undeclared, sshe2e removed): 3 not met, exit 1.

## Warm base

`clone-warm /tank/dregg-build/claude-lanes/warm-7dea0626/src`, then checkout 7dea0626. That tree had built only the
Host closure, so the first `mk-lane --verify` probe compiled 533 umbrella modules. The probe tree was then swapped
in as `warm-base/src`, and a second probe confirmed a warm replay with 0 modules compiled. To advance the base:
`advance-base-burst.sh TIP [GATED_LANE_DIR]`, with PIPELINE_ROOT set.

## The plant (2026-10-14): a stale installed runner is not used

The old burst service read `$PIPELINE_ROOT/scripts/journey-runner`. Before the first landing, the 8be9bd910
journey-runner was planted at `/tank/dregg-build/pipeline/scripts/`. That is the pre-`product_inputs` version
that decided verdicts on burst3 (RETRO d). The planted copy appends to `logs/PLANT-STALE-RUNNER-EXECUTED` whenever
it executes; its `lib.sh`, `journey-red-lines` and `journey-rows` were planted beside it.

- The standing run of d37eee80 dispatched
  `journeys/.trees/d37eee80…/scripts/pipeline/journey-runner sha256:bb8e1c6c…`. landing.sh printed
  `SELF-CHECK PASS` (equal to `git show d37eee80:scripts/pipeline/journey-runner`), and the marker file was
  **absent**.
- Positive control: executing the planted copy directly writes the marker (`logs/PLANT-positive-control.txt`),
  so its absence above is a real signal.
- Self-check control: the new runner, copied to a scratch directory and pointed at d37eee80, printed
  `REFUSED … differs: journey-runner(here:9e9b5b64 tree:bb8e1c6c) lib.sh(...)` and exited 3.

## Findings on hbox at the first landing (d37eee80; gate red=0, 136 lines, PASS=125 FAIL=3 UNCONFIGURED=8)

- `hermes` FAIL: the user-namespace restriction above. The driver waited 15 min and reported
  "Hermes ACP stream closed". `product_userns` now names this as UNCONFIGURED.
- `fleetsign` FAIL, reproduced 3 of 3: interleaved turns refused with "remote challenge differs from locally
  prepared intent" (cv 01a13985). Evidence is in `/tank/dregg-build/pipeline/evidence/fleetsign-race/`.
- `growth` FAIL (write p99 10 s at 1000 records) and `perf` UNCONFIGURED (box not quiet). Neither is required.
  `growth` has since moved to the nightly; `births` judges the bar per landing (above).
- `jserve` is a KNOWN FLAKY row on hbox (cv 01a139e1). It is timing-sensitive and not required. In main 7dea0626's
  hbox run it FAILED 10/12 serve rows; the failing cases were (a) "a client sends 3 bytes then sleeps 30 s" and
  (c) "50 connections that send nothing". It PASSED in the d37eee80 run an hour earlier. It is not declared absent:
  a jserve that was PASS at main's baseline and fails in a candidate counts as a new red.

## Baseline-relative landing rule (ROOT, 2026-10-14; the header of scripts/pipeline/required-rows)

A candidate lands when all three hold:

1. Its gate is red=0.
2. Its standing run has **no line non-PASS (or missing) that was PASS in main's own most recent standing run on
   this box**. landing.sh prints `new reds vs baseline: N`, and each one as `NEW RED`.
3. Every required line is PASS or declared absent by name. The exception is a line that was already non-PASS at
   main's baseline **and** is listed in required-rows as `known-red ROW CV-TASK note`; that line prints as
   `PRE-RED` and blocks nothing until fixed. A pre-existing red with no `known-red` line still blocks, so its cv
   task must be opened first.

The verdict prints `required unmet: [...] (of which pre-existing at main: [...])`. Exit 0 iff new reds = 0 and
nothing blocks.

- Known-red today: fleetsign (cv 01a13985).
- Plant for the rule: the d37eee80 results with m3 set to FAIL and rooms removed against the main baseline gave
  `NEW RED rooms MISSING` and `NEW RED m3 FAIL`, and exited 1.
