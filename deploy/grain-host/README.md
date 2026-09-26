# Linux grain worker host

This directory supplies a Linux launcher for `native/grain-runtime`. The
runtime remains the Mini authority and budget controller. Its worker process
uses this `bwrap` executable, which creates a distinct transient **user**
systemd service for each reserved operation, then executes the fixed command
inside a bubblewrap mount, user, PID, IPC and cgroup namespace. The name is
`mini-grain-t<TASK>-o<OPERATION_ID>` and comes from the runtime's durable child
marker as `MINI_GRAIN_UNIT`. The runtime also supplies
`MINI_GRAIN_STATE_DIR`, `MINI_GRAIN_CUSTODY_KEY`, and, when configured,
`MINI_GRAIN_TOOL_CUSTODY_KEY`, plus `MINI_GRAIN_TASK_CONFIG` and
`MINI_GRAIN_HOST_CONFIG`. The launcher refuses any mount (including `/usr`
and the optional network certificate mounts) that contains these paths, and
refuses a unit name that already exists. If the controller sets
`MINI_GRAIN_BROKER_SOCKET`, the launcher binds exactly that Unix socket at
`/run/mini-grain.sock` for the MCP broker client in `/agent/grain-runtime`;
the state directory itself stays hidden.

Example fixed runtime command (the operator chooses paths and amounts):

```json
{"name":"hermes-acp", "program":"/opt/mini/deploy/grain-host/bwrap",
 "args":["--workspace","/srv/mini/grains/7001/work",
         "--runtime-root","/opt/hermes/runtime",
         "--network","host","--","/agent/hermes-acp"],
 "reserve":"10000","charge":"10000"}
```

The controller must put the exact unit name in its child journal before spawn,
set `MINI_GRAIN_UNIT` on the command, and on hard disconnect first signal its
owned process group, then kill **all** processes in that unit with
`systemctl --user kill --signal=SIGKILL --kill-whom=all NAME.service`. It must
observe the unit stopped before clearing the child marker or fencing the Mini
generation. The wrapper also kills the unit when it receives TERM, INT or HUP.
After controller death, an old journal entry is only an audit clue; it must
never trigger an automatic kill of a possibly reused unit.

`mini-grain-controller@.service` is a user-systemd template for a persistent
`grain-runtime serve` process. Its `%i` is the decimal task ID and its JSON
file must configure `controlSocket` directly inside its durable private
`stateDir` (for example,
`/var/lib/mini/grains/task-7001/control.sock`). The account must own that
directory and keep it at mode 0700. The service
sets `MINI_GRAIN_CONTROLLER_UNIT` for the launcher, which adds a `BindsTo=`
dependency: stopping the controller service also stops its worker units.
The operator must install the runtime and per-task config at the template's
paths or adjust those paths before using the unit. `grain-ssh` is an SSH forced
command front end for the runtime's `connect ABS_CONTROL_SOCKET` mode. A
per-task `authorized_keys` entry can fix both absolute arguments and use
OpenSSH's `restrict` option. It ignores `SSH_ORIGINAL_COMMAND`.

The persistent controller process is required for hard SSH EOF to signal the
worker before Mini fencing and for a deliberate soft attachment to continue
after SSH disconnect. A direct SSH forced command invoking `serve` is unsafe
for those semantics. The controller socket must be accessible only to the
intended Unix account; separate users need separate account/socket policy.

The caller must run under a working `systemd --user` manager with `bwrap` and
unprivileged user namespaces. The runtime root should contain only the fixed
worker executable and its nonsecret assets. The workspace is the worker's
sole host writable mount. The launcher clears inherited environment variables
and does not mount the controller's key, configuration or state directory.
`--network none` has no network access. `--network host` permits the worker to
reach the host network, including loopback services, and is suitable only
when those services have their own authorization boundary. Provider credentials
and network policy still need a dedicated deployment decision.

The unit has a 600 second runtime ceiling, 2 GiB memory ceiling and 128 task
ceiling. Those are physical backstops, not Mini allowance units or provider
usage measurements. A `--network host` worker cannot be treated as having
network egress containment. Do not use this script to start a task until its
Mini host, custody key, task IDs, budget and reconciliation records are
independently bootstrapped.
