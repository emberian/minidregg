# Private operator Mini Host and frontend services

[`install-operator-stack`](install-operator-stack) renders and installs one operator-owned `mini serve` user service with one Unix-socket frontend per task UID. Optional provider services are **only** the reviewed deterministic `--content-peer-a`/`--content-peer-b` loopback fixtures. A real provider gateway has separate custody and is not provisioned by this script. This complements [`offer-render-task`](offer-render-task), which owns each task account's controller unit; it does not create accounts, grant Mini authority, install SSH keys, or contact a model provider.

The operator supplies a mode-0600 JSON manifest in an operator-owned directory. All paths are absolute and deliberately restricted to letters, digits, `_./@-`; paths with spaces, `%`, quotes, backslashes, traversal, or symlinks are refused so systemd unit arguments cannot be reinterpreted. The `installer` entry pins the reviewed executable itself. Example shape (replace every path, SHA and UID with selected qualified artifacts):

```json
{
  "version": "mini-grain-operator-stack-v1",
  "installer": {"path":"/opt/mini/bin/install-operator-stack","sha256":"<64 hex>"},
  "host": {
    "unit":"mini-offer-host.service",
    "mini":{"path":"/opt/mini/bin/mini","sha256":"<64 hex>"},
    "image":{"path":"/opt/mini/bin/minidregg-host","sha256":"<64 hex>"},
    "storageBinary":{"path":"/opt/mini/bin/store","sha256":"<64 hex>"},
    "signatureBinary":{"path":"/opt/mini/bin/signature","sha256":"<64 hex>"},
    "config":{"path":"/var/lib/mini-operator/host.json","sha256":"<64 hex>"},
    "socket":"/var/lib/mini-operator/runtime/host.sock"
  },
  "frontends":[{
    "unit":"mini-offer-front-a.service",
    "binary":{"path":"/opt/mini/bin/host-frontend","sha256":"<64 hex>"},
    "uid":1001,
    "socket":"/opt/mini/front-a/host.sock",
    "config":{"path":"/opt/mini/front-a/host.json","sha256":"<same host config SHA>"}
  }],
  "controllers":[{
    "uid":1001,"task":"7801","unit":"mini-grain-controller@7801.service",
    "runtime":{"path":"/opt/mini/bin/grain-runtime","sha256":"<64 hex>"},
    "workerRuntime":{"path":"/opt/mini/worker-a/grain-runtime","sha256":"<same runtime SHA>"},
    "config":{"path":"/home/friend-a/grain-7801/runtime-config.json","sha256":"<64 hex>"},
    "fragment":{"path":"/home/friend-a/.config/systemd/user/mini-grain-controller@7801.service","sha256":"<64 hex>"}
  }],
  "signedCheck":{"binary":{"path":"/opt/mini/bin/check-content-root","sha256":"<64 hex>"}},
  "providers":[]
}
```

`host.config` must name the same pinned `storageBinary` and `signatureBinary`; its `storageRoot` and private socket directory stay operator-owned 0700 outside every worker mount. Each public frontend directory is operator-owned, mode 0700 before launch. The frontend binds its own socket and grants only its named UID directory traverse, config read, and socket connect. The installer checks exact ACLs and listener PIDs at `status`/`start`/`restart`. Task custody keys, state, workspace, and output belong to separate task accounts in mode-0700 homes. Paths to selected executables, configs, Store, sockets, logs, and units must have root/operator-owned, non-task-writable ancestors; root-owned sticky `/tmp` is accepted for bounded scratch but **cannot be boot-enabled**.

Each `workerRuntime` pin must name the `grain-runtime` executable in that task's configured Hermes `--runtime-root`. Its SHA must equal the controller runtime SHA. This binds the keyless MCP process inside the worker to the controller image; the installer rechecks both worker files in its pre-exec guard. Changing a task config to point at a new runtime root also changes its durable journal binding, so an existing grain upgrade must retain the configured root path and replace its operator-owned executable only while the controller and all worker cgroups are stopped.

For a controller with an isolated `providerTask`, also pin
`controllers[].workerBridge` with the operator-owned executable
`RUNTIME_ROOT/grain-provider-bridge` and its exact SHA-256. Both installers
require that pin before a provider-enabled controller can start. Local
deterministic fixtures that explicitly select `localFixtureHostNetwork` are a
separate host-network test route.

As the operator, with a working user systemd manager, use:

```sh
install-operator-stack --manifest /absolute/operator-stack.json --unit-dir /absolute/user-systemd-dir render
install-operator-stack --manifest /absolute/operator-stack.json --unit-dir /absolute/user-systemd-dir install
install-operator-stack --manifest /absolute/operator-stack.json --unit-dir /absolute/user-systemd-dir start
install-operator-stack --manifest /absolute/operator-stack.json --unit-dir /absolute/user-systemd-dir status
install-operator-stack --manifest /absolute/operator-stack.json --unit-dir /absolute/user-systemd-dir quiescence
install-operator-stack --manifest /absolute/operator-stack.json --unit-dir /absolute/user-systemd-dir restart
```

`render` writes unit text to stdout without a manager mutation. `install` checks the manager's actual `UnitPath`, refuses active or foreign units, installs only absent exact files, and is idempotent; it does **not** start or enable them. Every generated unit has an `ExecStartPre` guard that rechecks the pinned manifest, binaries, helpers, config, path ownership, and exact unit source on every start. The guard checks operator-readable inputs; task-private controller config/journal checks run only in operator lifecycle commands, because systemd's `NoNewPrivileges=yes` intentionally prevents `sudo` within `ExecStartPre`. A frontend guard also waits for the private Host's exact listening socket before binding. The units deliberately have no automatic failure restart: recovery of a private Host while task controllers are active needs an explicit custody check. Frontends bind to the Host unit and stop if it goes away. `status` checks loaded fragment/drop-ins, running UID/executable bytes/argv, bound socket or loopback listener PID, and frontend ACL/access from the intended UID. A partial `start` or `restart` failure stops the operator stack and configured task controllers rather than leaving one public frontend open.

`quiescence` checks the configured task controller process, its pinned config/unit, journal authority slots, and every known worker unit's inactive/MainPID-zero/empty-cgroup state. `restart` requires one controller per frontend and a pinned private `signedCheck.binary`. That executable must perform an independently authorized **read-only signed Mini query** using an operator-selected task credential and emit exactly one canonical decimal content root. The installer does not print the key or query body. It checks the root before restart, stops both task controllers, rechecks journals and worker cgroups, restarts the Host/frontends/optional fixtures, repeats the signed query, requires the root unchanged, then starts and checks the controllers. A prompt can race the first quiescence read; stopping the controller hard-fences it and the second check then refuses the Host restart. This preserves custody but can interrupt work, so close offered sessions and schedule maintenance before calling `restart`. A nonempty provider hold/pending/attempt, tool or parent hold, pending prompt, or unresolved external effect refuses restart; a historical completed provider settlement record is retained.

`enable` deliberately refuses: cross-user manager boot ordering and persistent path migration have not had an actual acceptance. The generated units omit `[Install]`, so they cannot silently become boot services. The source-reviewed command makes a bounded operator stack restartable while its user manager is alive; it does not yet survive a machine reboot unattended. A later boot qualification must move the selected Store/artifacts out of `/tmp`, arrange task account and operator linger, prove task controllers start only after the private Host/frontends are ready, and compare a signed read after reboot. Pins identify artifacts at each launch but do not make same-UID writable media immutable. For the current persvati demonstration, operator linger is off and the Store/artifacts are under `/tmp`.

The installer requires noninteractive `sudo -n -u TASK` from the operator for the specific task config/unit reads, journal/cgroup inspection, and controller stop/start. Provision only the required operator-to-task commands; an interactive sudo prompt is refused. It does not grant the task accounts access to the private Store or operator Mini keys. Separate frontend sockets do not give per-tenant backend availability isolation, and native signed authority still decides every read or mutation.
