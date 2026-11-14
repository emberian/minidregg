# Qualification lane: state for a successor

Present state, rewritten whole. This lane qualifies rehearsal #3. Its board is
`docs/REHEARSAL-3-BOARD.md`. Rehearsal #3 ships only when every board row is green on ONE candidate
(ember's rule: never rehearse something that tests broken). **Verdict: NO-GO.**

## The system this lane built

- **Keep-going composed** (on main since bbadd8e11):
  - each phase has its own ledger, and a red phase blocks only its REQUIRES dependents;
  - adapter reds carry their retained refusal line;
  - `preflight` fails a phase in seconds when its inputs can't work;
  - `store-restart` restarts the Store independently of the app chain;
  - tests: `native/resource-client/test_composed_scenario.py`, `tests/test_composed_keep_going.py`,
    `scripts/spk-platform/tests/test_composed_selection.py`.
- **composed-inputs.sh**:
  - derives the connector selection and the resident binding from the world;
  - names what the world lacks as `CONNECTOR/RESIDENTS UNAVAILABLE:` lines and exits 0;
  - the app is the qualified EtherCalc (93bd2c29…, class M);
  - writes `OUT/broker-setup/recovery.json`, so `world-down.sh OUT` removes the grain world (9e7eeab2f).
- **Test-ahead loop, dregg-build** (`/build/lanes/qualify/`):
  - `qrun.sh NAME CAND PORT` runs one standing world (`qiter.sh up/inputs/gate/down`). The harness is
    laid from the Mac:
    `git archive HEAD scripts native/resource-client/journey.d <resource-client *.py|*.sh> | ssh dregg-build tar -x -C /build/lanes/cs-NAME/src`,
    plus HARNESS-COMMIT.
  - One world at a time, under `mkdir /build/lanes/qualify/world.lock`.
  - `AGE=N` ticks the clock before apps bootstrap (the aged-world row).
  - `qiter down` runs world-down on the inputs too.
- **Overlay candidates**:
  - `qoverlay.sh BASE_CAND TIP` gives Host and consent from a READY candidate, Rust at TIP. It lives in
    `/build/lanes/qualify/cand/overlay-*`, never ships, and its QUALIFY-OVERLAY.json names the Host commit.
  - The Rust is built on hbox: `/tank/lanes/qualify/src` (a clone; check out TIP), then
    `LANE_DIR=/tank/lanes/qualify swarm-build bash deploy/candidate/lane-build.sh rust`, about 10 min
    cold and 2 min incremental.
  - Artifacts are streamed hbox → Mac → dregg-build `/build/lanes/qualify/rust-TIP/`, and the source
    archive goes to `/build/lanes/qualify/src-TIP.tar`. `cand/toolchains-TIP12.json` carries hbox's
    `rustc -vV`.
- **Demo-dry**: infra successor 4 (ac204a2887d583805) runs `edge/demo/demo-dry-walk CP` (dregg-infra
  demo-vm 9b6ce95+). The TSV has the item, status (GREEN/RED/BLOCKED/SEEN/UNCONFIGURED), evidence and
  first_refusal. UNCONFIGURED is shown but not counted red, like the exchange row.

## In flight (at hand-off, 2026-10-28 ~18:15 UTC)

- **japps two-subject e2e** on hbox: Lean roles from 9bd52317c, Rust at lane/un-japps-rows b65465c72
  (the share-issue fix: the member delegates the manager a child capability, and route() names it).
  - Job `/tank/lanes/qualify/japps1.sh`, PID file `japps1.pid`, outputs `j1.up.log`, `j1.japps.out`
    and `.err`.
  - Its world is `/tank/lanes/qualify/runs/j1`; the script runs world-down itself.
  - The verdict, by row name, goes to the deputy a308118209b4a48ea and the integrator a34bdb948f1cf4796.
- **Composed apps:sheet does NOT yet test that fix.** The composed fixture
  (scripts/spk-platform/same-store-app.py and ws-continuity-fixture.py `issue`) still cites the
  member's appOwnerCapability as `appDelegateCapability`. The product fix is 52d15a6ce (apps.rs
  `delegate_share`). Owed harness change: after `lifecycle`, a step `share-delegation` in which the
  owner delegates the manager a child of appOwnerCapability (verbs observe, mutate, delegate, append,
  place; perRequestBytes = template ownerBudget), with propose/submit/publish-delegation in the owner's
  workspace, and the ticket's `appDelegateCapability` naming the child. Then run
  `qrun.sh` on an overlay of Host 9bd52317c and Rust b65465c72.
- **Lean, on dregg-ref:**
  - lane/qualify-lean-refusals 59fadc9cf (code 664f8e09b): operator-log reasons for ops
    34/26/22/84/105/242/246/189 and the fn arms. Unelaborated: the earlier runs never compiled
    (runuser without the lanes user's bus env, so swarm-build's `systemd-run --user` failed; not OOM).
    Relaunched with the bus env: PID file /srv/lanes/qlr-state/retry.pid, verdict in
    /srv/lanes/qlr-state/retry.log. Trap for briefs: `runuser -u lanes` needs XDG_RUNTIME_DIR and
    DBUS_SESSION_BUS_ADDRESS for swarm-build.
  - lane/qualify-certify-prefix: statement c71fa04ec (green, audited); implementation at 9d00fba59:
    TailBound and DurableLogTags lane-check green (one proof fixed); next file to check is
    Compiler/DurableReceiverCore; continuation note docs/CERTIFY-PREFIX-STATE.md. Nothing running.
  - lane/qualify-doc-contention: CommutingAppend statement dcde47a1e (audited, merge hold lifted;
    ELABORATES on dregg-ref: lane-check 0 errors; state note a0b45fe8e);
    proofs drafted at 25c84470c, UNELABORATED; continuation note 162e36a15
    (docs/COMMUTING-APPEND-STATE.md). Owed proofs: commutingPrepare, movedRootAccepted,
    twoAppendersOneObservation. Check job: PID file /build/lanes/qualify-doc-contention-check1.pid.
    Don't merge it until the proofs are green and the whole tree has built.
- **dregg-infra qualify/jworld-composed f025c3114**:
  - verified: route front, and bwrap beside launch-gate;
  - untested: `JWORLD_MANAGEMENT=distinct`. composed-inputs must also read `operatorCustody` instead
    of hard-coding owner = management;
  - open, needing ember's sudoers rule: root-owned keys-client.json, and the resident's root hand-offs.
  - With infra successor 4 to merge.
- **Leftover root state on dregg-build:** qj-3's grain world, store d52307664949a32e, helper
  `/usr/local/libexec/mini-spk-volume-helper-c8af5b0cd5dbe1e6`. Its root cleanup refused "mounted
  world". Unmount first: `sudo -n HELPER '{"verb":"unmount",...}'` for each volume request under
  `GRAINS_ROOT/broker/volume-*.json` (world-down.sh does exactly this), then rerun world-down with a
  recovery.json.

## Merged to main from this lane

bbadd8e11 (keep-going), 4241cf11a (Rust refusal logging), f8cbcd5d3 (doc re-plan), 047fcd553
(clock/certify re-plan, house names, cold reader), and the EtherCalc + local-check fix (41581198b,
c54f43c9c; confirm on main). **To send the integrator:** 9e7eeab2f (grain-world teardown), plus its
cleanup-trap line for composed-full2.

## Owners (route reds on sight)

- integrator a34bdb948f1cf4796: harness and build
- deputy a308118209b4a48ea: market, spk and apps; acec1de6f1c53a04c handles worker ids and genesis shape
- B3 a85d12892ea6de3ca: share-issue. At its limit; continuation note B3-STATE.md 6087140cf
- L4d a450fc35eb510f987: Hermes
- story faerie acf88647b53657831: door and story
- infra 4 ac204a2887d583805: edge, demo and demo-dry
- auditor af7a93e7b8ba729d4: statements

Usage is short (root, 18:10): route new fixes to codex astra workers, which leave a commit script, or
to the owning lanes. Keep turns event-driven.
