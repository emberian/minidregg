# Linux grain worker host

This directory supplies a Linux launcher for `native/grain-runtime`. The
runtime remains the Mini authority and budget controller. Its worker process
uses this `bwrap` executable and its sibling `launch-gate` executable. The
launcher creates a distinct transient **user** systemd service for each
reserved operation. The gate is that service's `ExecStart` and executes the fixed command
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
"systemdScope":true,"reserve":"10000","charge":"10000"}
```

Compile `launch-gate.rs` on the Linux host with
`rustc --edition=2021 launch-gate.rs -o launch-gate` and install it beside
`bwrap`; both must be executable. The launcher verifies the sibling gate's
exact protocol response before advertising its own protocol to the runtime.
Before spawning, the controller durably arms
the operation gate and records the exact unit name in its private state. The
service's `ExecStart` runs `launch-gate run STATE_DIR UNIT -- /usr/bin/bwrap …`.
After a hard disconnect or crash, the controller durably fences the gate before
killing **all** processes in that unit with
`systemctl --user kill --signal=SIGKILL --kill-whom=all NAME.service`. This
also blocks a start request that reached systemd but has not executed yet. The
controller must audit the unit stopped before clearing the child marker or
reconciling the Mini reservation; a failed fence or audit leaves it unresolved.
The wrapper also kills the unit when it receives TERM, INT or HUP. Gate
tombstones must remain while an operation ID might be reused. An old journal
entry alone must never trigger an automatic kill of a possibly reused unit.

`mini-grain-controller@.service` is a user-systemd template for a persistent
`grain-runtime serve` process. Its `%i` is the decimal task ID and its JSON
file must configure `controlSocket` directly inside its durable private
`stateDir` (for example,
`/var/lib/mini/grains/task-7001/control.sock`). The account must own that
directory and keep it at mode 0700. The service
sets `MINI_GRAIN_CONTROLLER_UNIT` for the launcher, which adds a `BindsTo=`
dependency: stopping the controller service also stops its worker units.
The operator must install the runtime and per-task config at the template's
paths or adjust those paths before using the unit. `grain-ssh` is an SSH
forced-command front end for the runtime's `connect ABS_CONTROL_SOCKET
hard|soft` mode. A per-task `authorized_keys` entry fixes the absolute
runtime and socket paths and uses OpenSSH's `restrict` option. For example,
after installing the persistent service and task configuration:

```text
restrict,pty,command="/opt/mini/deploy/grain-host/grain-ssh /opt/mini/bin/grain-runtime /var/lib/mini/grains/task-7001/controller.sock" ssh-ed25519 AAAA... hard-key
restrict,pty,command="/opt/mini/deploy/grain-host/grain-ssh /opt/mini/bin/grain-runtime /var/lib/mini/grains/task-7001/controller.sock soft" ssh-ed25519 AAAA... soft-key
```

The two-argument entry defaults to **hard**: SSH EOF interrupts an active
worker and the persistent controller fences its Mini generation. **Soft** is
an explicit third argument in a separate fixed entry: SSH EOF detaches while
the already reserved task may finish; a later connection can reattach. The
wrapper ignores `SSH_ORIGINAL_COMMAND`, sends exactly one attach line, and
forwards only the controller's line interface. Wait for its `attached ...`
or reconnect message before entering `hermes PROMPT`, an allowlisted
`run NAME`, `status`, `conversation new`, `recover`, or `disconnect`.
Attachment can take seconds while Mini confirms the transition; a refusal is
printed and closes the SSH connection. A reconnect resumes the task's
controller and retained Hermes conversation when its state permits; it does
not claim to resume an interrupted provider call or settle unresolved effects.

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
