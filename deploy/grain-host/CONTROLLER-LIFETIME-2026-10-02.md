# Cross-manager controller lifetime

Canonical deployment can place the controller in SYSTEM systemd with its fixed
service UID while sandbox workers remain in that UID's USER manager. USER
`BindsTo` cannot name a SYSTEM unit. The launcher therefore requires an
incarnation-bound launch gate for that topology.

At `init`, the source runtime supplies the explicitly selected manager, canonical
controller unit, active MainPID and InvocationID. The gate checks the manager
observation, process UID and Linux process start time and persists the tuple with
the armed operation. At `run`, it verifies the tuple before and after opening a
pidfd. A replacement controller cannot adopt the old operation. Missing or changed
identity refuses before sandbox launch. An old gate binary refuses the extended
armed record rather than silently dropping the lifetime requirement.

The gate remains the worker unit MainPID and supervises the existing bubblewrap
sandbox. Controller pidfd readiness immediately kills/reaps bubblewrap, then persists a
fence. The existing `started` record already blocks replay; a contended gate lock
or slow fsync must not extend sandbox lifetime.
The monitor's child has a parent-death signal, and bubblewrap retains its existing
`--die-with-parent` and PID namespace, so monitor death also kills sandbox
children, including processes that create new sessions. The worker cgroup remains
the exact operation's cgroup; ordinary source recovery fences before killing and
requires inactive/MainPID-zero/empty descendants as before. A stop is asynchronous
and must still be physically observed before releasing/reusing a slot. This adds
no native settlement or completed-effect claim.

Same-manager legacy USER controllers retain `BindsTo`; tuple-bearing USER gates
can also use the monitor. The `--controller-manager-protocol` handshake returns
`mini-controller-manager-v1`. Runtime manager selection comes from the root-owned
controller registration, not probe-and-fallback. The gate's tuple is durable;
worker execution does not trust a fresh environment to replace it.

## Linux receiving, 2026-10-02

On persvati, `probe-controller-lifetime.py SOURCE_DIR NEW_PRIVATE_SCRATCH` uses a
new transient SYSTEM controller (`Type=exec`, service UID = caller), actual USER
worker units and the production bubblewrap launcher. It retains all command
outputs and cleans only its own units. Run with a compiled `launch-gate` beside
`bwrap`. This is lifecycle/confinement component evidence, not a native grain
budget or provider-effect journey.

`/home/ember/workbox/controller-lifetime-r3/result.json` records seven checks:
wrong PID/invocation refusal; controller SIGKILL fencing and recursive cgroup
empty after six captured sandbox processes; queued old launch refusal across
restart; old armed operation refusal by the new invocation; no rearming of a
fenced operation; monitor SIGKILL descendant cleanup; ordinary controller stop
cleanup. Each held sandbox includes a child and setsid grandchild.

The earlier r1 fixture failed while using systemd's default `Type=simple`: its
reported active MainPID had not yet dropped to the configured UID. Refusal was
correct. The actual canonical template uses `Type=exec`; r2 and r3 use that
contract. Original r1 evidence is retained.

The existing `scripts/overnight-tests/launch-gate-probe.sh` also passed unchanged
at `/home/ember/workbox/controller-lifetime-legacy-r1`, covering late queued launch
after fence, fence-before-init, and exact running-unit kill plus retry refusal.
`bash -n` passed. ShellCheck was unavailable on the build host.

Review found that the original death branch fenced before killing, so ordinary
lock or fsync delay could prolong sandbox execution. The corrected ordering was
received in `/home/ember/workbox/controller-lifetime-r4/result.json`: all eight
checks pass, including holding the gate flock during controller SIGKILL and
observing all five sandbox descendants gone before releasing that lock. The
monitor then persists the fence and the entire worker cgroup empties.
