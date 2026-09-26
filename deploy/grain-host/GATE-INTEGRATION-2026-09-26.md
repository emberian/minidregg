# Linux launch-gate and bwrap integration probe, 2026-09-26

On persvati (Linux 6.17.0-40-generic, systemd 257), the production `launch-gate.rs` was compiled beside the production `bwrap` launcher in private scratch `/tmp/mini-grain-gate-prod.pGzyJW`. The bounded `probe.sh` ran only transient user units and private `/tmp` state. Its [raw log](GATE-INTEGRATION-2026-09-26.log) records:

- Exact `mini-grain-launch-gate-v1` launcher protocol after checking the sibling gate's own protocol. An executable but incompatible `/usr/bin/true` sibling was separately refused with `launch-gate protocol mismatch`.
- Exact broker socket bind and bidirectional ping/pong while controller state and keys stayed outside the worker mount.
- `/usr` host-config and workspace-contained controller-state mount refusals.
- Provider custody key and provider key file refusals when either lies under the worker workspace.
- Wrapper TERM and controller `BindsTo=` stop of `setsid` descendants: four host cgroup PIDs in each worker, all dead or zombie afterward, units inactive.

Reproduce in a new private Linux scratch by copying `deploy/grain-host/`, compiling `rustc --edition=2021 launch-gate.rs -o launch-gate`, then running `./probe.sh ./bwrap`. The separate delayed-systemd-start race probe is in `scripts/overnight-tests/launch-gate-probe.sh` and compiles this same deployed source.

SHA-256 at execution: gate source `65a4ad217a43b103e70dfa41e91a804d7e0e11ce27d376577569f5c65aa68e96`; compiled Linux gate `e4e90c9ef16961bb305e42df6e9d40a69933d1b02294727454425339063cd554`; launcher `09b76dd5cb04a3e0668921483842996c9b19600225490a300a0ab6a5ae1ee6bd`; probe `1e7ee0ee9d91e149bde4b669ff8a1d2b9907a08180d7093a1eaf8d1bac91d9c5`; raw log `abc401415458d8fce58379ea2f7b8dc9b278f3c79418cf531df74964ce703b9c`.

This probe covers the physical launcher and unit behavior. Signed Mini grain operations are exercised separately by `native/grain-runtime/acceptance.sh`.
