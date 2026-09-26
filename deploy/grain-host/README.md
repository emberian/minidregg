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
`MINI_GRAIN_TOOL_CUSTODY_KEY`, `MINI_GRAIN_PROVIDER_CUSTODY_KEY`, and
`MINI_GRAIN_PROVIDER_KEY_FILE`, plus `MINI_GRAIN_TASK_CONFIG` and
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

## Controller unit installation

`install-controller` creates a direct `mini-grain-controller@TASK.service`
user unit for a persistent `grain-runtime serve` process. The historical
`mini-grain-controller@.service` template shows the same service limits, but
the installer writes the exact task, executable and config paths so the
operator need not edit a template. The runtime JSON must configure
`controlSocket` directly inside its durable private `stateDir` (for example,
`/var/lib/mini/grains/task-7001/control.sock`). The task account must own
that directory and keep it at mode 0700. The service
sets `MINI_GRAIN_CONTROLLER_UNIT` for the launcher, which adds a `BindsTo=`
dependency: stopping the controller service also stops its worker units.

Run the installer as the task account after placing the runtime JSON and
executables. The pins file is JSON with one entry per executable, including
the runtime, `mini`, Mini host, every scoped `bwrap` command, and each
`bwrap` sibling `launch-gate`:

```json
{"artifacts":[
  {"path":"/opt/mini/bin/grain-runtime","sha256":"REPLACE_WITH_64_LOWERCASE_HEX"},
  {"path":"/opt/mini/bin/mini","sha256":"REPLACE_WITH_64_LOWERCASE_HEX"},
  {"path":"/opt/mini/bin/minidregg-host","sha256":"REPLACE_WITH_64_LOWERCASE_HEX"},
  {"path":"/opt/mini/bin/bwrap","sha256":"REPLACE_WITH_64_LOWERCASE_HEX"},
  {"path":"/opt/mini/bin/launch-gate","sha256":"REPLACE_WITH_64_LOWERCASE_HEX"}
]}
```

```sh
install-controller --config /opt/mini/grains/7001.json \
  --runtime /opt/mini/bin/grain-runtime \
  --pins /opt/mini/grains/7001-pins.json \
  --unit-dir "$HOME/.config/systemd/user" --render-only
install-controller --config /opt/mini/grains/7001.json \
  --runtime /opt/mini/bin/grain-runtime \
  --pins /opt/mini/grains/7001-pins.json \
  --unit-dir "$HOME/.config/systemd/user"
systemd-analyze --user verify "$HOME/.config/systemd/user/mini-grain-controller@7001.service"
# After inspecting the unit and signed Mini task state:
systemctl --user enable --now mini-grain-controller@7001.service
```

The installer never enables or starts a unit. The unit directory must already
exist, be owned by the task account, and be in its user systemd load path.
Installation is atomic and refuses an active unit, a conflicting unit file,
a journal bound to another task, unpinned or changed executable bytes, or
paths requiring systemd escaping (spaces, `%`, quotes, backslashes). The
private JSON, keys and state remain outside worker mounts. Pins identify
operator-selected artifact bytes **at installer time**; an artifact writable
by the same Unix account can change later. Their provenance and compatibility
still need the separately retained source/build evidence. Deploy executable
artifacts in immutable, administrator-owned locations before starting a
friend's controller.

`grain-ssh` is an SSH
forced-command front end for the runtime's `connect ABS_CONTROL_SOCKET
hard|soft` mode. A per-task `authorized_keys` entry fixes the absolute
runtime and socket paths and uses OpenSSH's `restrict` option. For example,
after installing the persistent service and task configuration:

```text
restrict,command="/opt/mini/deploy/grain-host/grain-ssh /opt/mini/bin/grain-runtime /var/lib/mini/grains/task-7001/controller.sock" ssh-ed25519 AAAA... hard-key
restrict,command="/opt/mini/deploy/grain-host/grain-ssh /opt/mini/bin/grain-runtime /var/lib/mini/grains/task-7001/controller.sock soft" ssh-ed25519 AAAA... soft-key
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
