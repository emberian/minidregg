# Linux launch-fence race probe

The deployed source is `deploy/grain-host/launch-gate.rs`. The sibling
`launch-gate.rs` in this test directory preserves the first isolated prototype
used for the historical race evidence. `launch-gate-probe.sh` compiles and runs
the deployed source, not that prototype. The gate controls one unique
`mini-grain-tTASK-oOP` systemd user service.

Compile on Linux with
`rustc --edition=2021 deploy/grain-host/launch-gate.rs -o launch-gate`.
The state directory must be an owned real directory with mode 0700. Commands:

```sh
launch-gate init ABS_STATE_DIR mini-grain-tTASK-oOP
launch-gate fence ABS_STATE_DIR mini-grain-tTASK-oOP
launch-gate run ABS_STATE_DIR mini-grain-tTASK-oOP -- /usr/bin/bwrap ...
```

The per-operation `UNIT.gate` is a private regular file. `init` creates and
fsyncs `armed`; `run`, as the transient service's ExecStart/MainPID, takes an
exclusive `flock`, requires `armed`, fsyncs `started`, releases the lock, then
execs the worker command. `fence` takes the same lock and fsyncs terminal
`fenced`; it can create the file if the controller died before `init`. Neither
`init` nor `run` can rearm or launch after `fence`.

The intended recovery order is **fence, kill/stop the exact unique systemd
unit, then observe its cgroup empty/inactive** before clearing the journaled
child marker. If a `systemd-run` DBus start request materializes after the
fence, its service ExecStart reads `fenced` and cannot execute the worker. If
`run` already marked `started` before the fence, it is the unit MainPID;
kill/stop must stop it and its descendants. The file marker alone does not
prove a running worker is dead. The controller must durably initialize the
gate before launching its wrapper and persist the matching operation ID/unit
in its own journal.

Run `launch-gate-probe.sh NEW_ABSOLUTE_SCRATCH_ROOT` on Linux with a working
user systemd manager. It retains logs in the new root. The probe submits a
real transient start request, pauses ExecStart with `ExecStartPre`, fences
while the unit is `activating/start-pre`, and requires the late gate to exit
without a worker marker. It also checks fence-before-init and an already
running worker stopped by exact unit kill. The 2026-09-26 persvati prototype
and deployed-source results are in
`docs/evidence/2026-09-26-host-session/launch-gate-linux-*.log`.

This probe exercises systemd ordering and the deployed gate with a harmless
sleep worker. The paired `bwrap` launcher and runtime require separate
integration acceptance with the final host/client image.
