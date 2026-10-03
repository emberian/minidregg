# World runbook: staging and constructing a Mini world on hbox

Facts from the world lane's construction of `mini-bigstep-hbox-r1` (2026-10-03) and from
finishing its setup. Paths are hbox paths. Nothing here needs root except the steps marked
ROOT, and no step prints or stores key contents.

Terms: **frame** is the world's root directory (`/var/lib/mini-bigstep-hbox-r1`). **Store root**
`R` is `FRAME/var/lib/mini/store`. **Candidate** `C` is
`FRAME/var/lib/mini/candidate/<commit>` (`candidate/current` is a relative symlink to it).

## 1. Seal a capsule family

A family is an immutable directory `/home/hbox/build/mini-bigstep/family-<commit8>/` holding one
copy of every executable role, a `manifest.json` whose `sha256` map pins every role path by
the hash of its actual bytes, a source archive and extracted `source/` for the same commit, the
materialized launcher wrapper and launch gate, `execution-dependencies.json`,
`hbox-execution-supplement.json` (usage and `ldd` smoke of each role) and `provenance.json`.
The seal script refuses an existing family directory and never edits another family.

- Roles: `mini` (also the `shell` role), `grainRuntime` (also `hermes`), `grainProviderBridge`,
  `host`, `store`, `verifier`, `inferenceScheduler`, `payWatcher`, `launchGate`, `bwrapLauncher`,
  and four SPK roles. SPK roles under the unsuffixed names (`spkHost`, `spkBroker`, `spkHostd`,
  `spkBrowserProxy`, `browserProxy`) are the ORDINARY release build. The
  `integration-qualification` build is published only under `*Qualification` keys for the race
  fixtures.
- `bwrap` is the physical `/usr/local/libexec/mini-grain-bwrap` (root-owned, covered by the
  AppArmor profile `/etc/apparmor.d/mini-grain-bwrap`). The launcher wrapper is
  `deploy/grain-host/bwrap` with its physical invocation rewritten to that path and must keep the
  file name `bwrap` beside `launch-gate`.
- Build recipes: `integration/client-runtime-build.py`, `integration/spk-hbox-build.py`
  (ordinary then qualification), both through `integration/cargo-bounded` under `swarm-build`.
  Lean Host: `scripts/build-native-host.sh --umbrella --output DIR --binary BIN`, from a tree
  whose `.lake/packages` is a real copy (the script refuses package symlinks).
- Reference seal scripts: `/home/hbox/workbox/claude-r1/world/seal-family.py` (helper-only delta on
  an earlier family) and `seal-d5ba.py`.

## 2. Stage the root candidate (ROOT)

`/home/hbox/workbox/claude-r1/world/stage-root.py` run as root copies each role into
`candidate/<commit>/` with a root-variant manifest whose paths resolve inside root custody, writes
`candidate/current`, and installs `usr/local/lib/mini/` (the SSH forced-command launcher
`mini-shell-ssh`, service tooling, `infra/`, the SPK physical assets). Every byte is re-hashed against the sealed
manifest and any existing destination refuses. Then
`mini-service-config.py --frame` publishes `etc/mini/ingress.json` (private/public topology) before any Store.

## 3. Plan and units

`world/make-plan.py` fills `provision-plan.template.json` from the staged candidate. The plan carries
the member list (`entry` paid or sponsored), rooms, budgets, task ids (parent 7901, tool 7902),
`paidEntryAdapter` and `payObserver`, and

    "serviceManager": {"type": "systemd-system",
                       "systemctl": ["/usr/bin/sudo", "-n", "/usr/bin/systemctl"],
                       "unitDirectory": "/etc/systemd/system",
                       "units": {"operator": "<prefix>-store.service",
                                 "public": "<prefix>-ingress.service",
                                 "sshd": "<prefix>-sshd.service"}}

Units (`User=<service user>`, `UMask=0077`, `Restart=no`, no `[Install]`) are rendered by
`platform-service-cut.py`/`platform-provision.py` into `world/units/` and installed root 0644 in
`/etc/systemd/system` (ROOT). A Store write/fsync probe as the unit user should pass before genesis.

## 4. Construct (the one genesis)

    nohup world/run-construct.sh        # log world/construct.log

It runs `candidate/source/native/resource-client/platform-provision.py start world/provision-plan.json`:
genesis, paid synthetic-RPC members, the sponsored connector, forced-SSH `whoami` for every
member. Last observed: about 50 s. Never re-run against a non-empty Store root. If it fails,
preserve the Store contents under a renamed directory, understand, then rebuild.

Outputs under `R`: `runtime.json` (service pids, unit names, invocation ids, manifest pins),
`journey.json`, `platform-inputs.json` (member inventory keyed by SUBJECT, custody, authority),
`paid-entry-result.json`, `plan.json`, `source-pins.json`, `node/` (config, genesis), `sock/operator.sock`
(private) and `sock/public.sock`, `ssh/` (`sshd_config`, `known_hosts`, authorized keys, connector key),
`members/<name>/join/{workspace,id_ed25519,mini.key,...}`.

Deployment binding: write `world/binding-request.json`, run `platform-service-cut.py prepare`
(verify-only plus the sshd auxiliary unit), publish the result root 0644 at
`FRAME/etc/mini/deployment-binding.json` (ROOT), then rerun `mini-service-config.py` with it.

## 5. Finish setup (as the service user, no sudo)

Let `W` be the lane directory, `HOSTPID` the `hostProcessId` from

    $C/mini operator-status --socket $R/sock/operator.sock --host $C/minidregg-host \
        --config $R/node/deployment/pinned-config.json

**Pre-room timing baseline** (read-only; records `/proc/loadavg` on every row):

    python3 $W/latency-prebaseline.py --spec $R/journey.json --output $W/baseline-prerooms \
        --member <member-0 subject> --expected-manifest-sha <root manifest sha> --host-pid HOSTPID

(`native/resource-client/latency-prebaseline.py`, next to `latency-same-store.py`.)

**Rooms.** Copy `journey.json` to `journey-rooms.json` adding
`deployment.binding = {"path": ".../etc/mini/deployment-binding.json", "sha256": "..."}`, then
detached:

    python3 $C/source/native/resource-client/joined-member-journey.py run $W/journey-rooms.json \
        --output $W/journey-rooms-out

Use `run`, not `sweep` (sweep births a second shared room). It is not resumable: a failed row stops
the journey, and rerunning repeats `room new`. On the r1 world it created the shared room
`<prefix>-r0`, invited and imported four members, admitted five concurrent writes and passed
read-back checks (about 11 minutes), then stopped at the row
`doc transclude <prefix>-r0/tasks <prefix>-r0/notes 1 1 snapshot` with
`no run of the source holds both endpoints`. Rooms r1/r2 and the kick/rejoin/law-lockout rows were
not reached. `restart`, `hermes`, `spk` and `growth` hooks are intentionally absent and show as blocked.
The shared document target is the `target` of the `room resolve <prefix>-r0/notes` row.

**Task readiness:**

    python3 $C/source/native/resource-client/platform-task-readiness.py \
        --platform-inputs $R/platform-inputs.json --evidence $R/task-readiness

Reply `confirmed: true` with attach/reserve actions for task 7901 and attach for 7902; evidence
under `$R/task-readiness/`. Idempotent evidence files; do not delete them.

## 6. WORLD-IDENTITY.json

Written to `W/WORLD-IDENTITY.json` (protocol `mini-world-identity-v1`). It holds: frame; Store and
node roots; `domain`, genesis identity id, genesis seed and config sha; capsule manifest path and
sha (root variant and sealed family) and candidate path; unit names, manager, user; operator
and public socket paths; SSH host, port, `known_hosts` and `sshd_config` paths; for each member NAME its
subject, account (the service user, forced command `mini-shell-ssh`), workspace, home, SSH key FILE
path, mini key file path, entry kind and the exact `ssh` invocation; created and not-created rooms
with targets; the shared document alias and target; task ids and readiness attempt directories;
connector identity; paths of `runtime.json`, `journey.json`, `platform-inputs.json`, `plan.json`, the
deployment binding, journey output and the baseline result; per-member forced-SSH `whoami` proof
(rc, timing, loadavg, match against inventory) and one refused outsider (a throwaway key outside
`authorized_keys`: `Permission denied (publickey)`, rc 255). Key contents never appear.

Member ssh form:

    ssh -F /dev/null -T -o BatchMode=yes -o IdentitiesOnly=yes -o StrictHostKeyChecking=yes \
        -o UserKnownHostsFile=$R/ssh/known_hosts -i <key file> -p 22027 <user>@127.0.0.1 whoami

## 7. Known sharp edges

- Units are not boot-enabled (`[Install]` absent) and use `Restart=no`: a reboot or crash leaves the world down.
- There is no drained-restart hook; restarting the Store unit is an unannounced interruption.
- The rooms journey is not resumable; a single failing row strands the remaining rooms.
- The v3 physical-dependencies JSON (`physical-dependencies-v3.json` in the SPK workbox) still names
  stale build-directory and `/usr/bin/bwrap` paths; the sealed capsule pins
  `/usr/local/libexec/mini-grain-bwrap` instead. Do not stage from it unmodified.
- The pre-room baseline needs the live Host pid and checks `/proc/<pid>/exe` bytes against the manifest Host sha.
- Several harness tests create sockets under temp directories; on macOS the temp path exceeds the
  107-byte Unix socket bound, so run those tests on hbox or with a short `TMPDIR`.
- The resident adapter `testing/journeys/shared-resident-useful-work.py` is an untested draft.
- `/home/hbox/workbox/cycle1-service-hbox-r1/infra/edge/mini` is the staging source of service tooling;
  the same files are in dregg-infra `main` (`edge/mini/`).
