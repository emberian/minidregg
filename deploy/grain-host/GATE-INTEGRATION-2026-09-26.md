# Linux launch-gate and bwrap integration probe, 2026-09-26

On persvati (Linux 6.17.0-40-generic, systemd 257), the production `launch-gate.rs` was compiled beside the production `bwrap` launcher in private scratch `/tmp/mini-grain-gate-prod.pGzyJW`. The bounded `probe.sh` ran only transient user units and private `/tmp` state. Its [raw log](GATE-INTEGRATION-2026-09-26.log) records:

- Exact `mini-grain-launch-gate-v1` launcher protocol after checking the sibling gate's own protocol. An executable but incompatible `/usr/bin/true` sibling was separately refused with `launch-gate protocol mismatch`.
- Exact broker socket bind and bidirectional ping/pong while controller state and keys stayed outside the worker mount.
- `/usr` host-config and workspace-contained controller-state mount refusals.
- Wrapper TERM and controller `BindsTo=` stop of `setsid` descendants: four host cgroup PIDs in each worker, all dead or zombie afterward, units inactive.

Reproduce in a new private Linux scratch by copying `deploy/grain-host/`, compiling `rustc --edition=2021 launch-gate.rs -o launch-gate`, then running `./probe.sh ./bwrap`. The separate delayed-systemd-start race probe is in `scripts/overnight-tests/launch-gate-probe.sh` and compiles this same deployed source.

SHA-256 at execution: gate source `65a4ad217a43b103e70dfa41e91a804d7e0e11ce27d376577569f5c65aa68e96`; compiled Linux gate `e4e90c9ef16961bb305e42df6e9d40a69933d1b02294727454425339063cd554`; launcher `9cd9b650d82f90985bd9be625d853de949714e01417f9878d29d33cadf6630ef`; probe `9b744f6f7915d96b8eeedc67819905c616b845b9a00866bbcbc081ad06dbc291`; raw log `ea6d835cf8044e775a9cd8c5ac126a8a7b827eef04e6b0e56ae3cbe1bf8aad8d`.

This probe covers the physical launcher and unit behavior. Signed Mini grain operations are exercised separately by `native/grain-runtime/acceptance.sh`.
