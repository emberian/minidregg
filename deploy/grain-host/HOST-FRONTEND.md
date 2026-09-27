# Mini host access from separate Unix task accounts

The native `mini serve` socket and its pinned config stay in an operator-owned
0700 directory with the Store and operator keys. The native transport refuses a
socket in a less private directory. A different Unix task account cannot traverse
that directory, so each task needs an operator-run `host-frontend` and its own
public socket. This is a local Unix-socket entrance, not a TCP listener.

Build [`host-frontend.rs`](host-frontend.rs) on the Linux host with
`rustc --edition=2021 -D warnings host-frontend.rs -o host-frontend`. Install the
source-reviewed binary at an operator-selected absolute path. It uses Linux
`SO_PEERCRED`, `flock`, `/usr/bin/setfacl`, and monotonic `poll` deadlines.

For each task, create a **dedicated operator-owned 0700 directory** under
operator-controlled, non-task-writable ancestors. Copy the exact bytes of the
private pinned host config into that directory as an operator-owned mode-0600
regular file. Never put Store files, Mini keys, controller JSON, or the private
host socket there. Start one operator-owned frontend with:

```sh
host-frontend PRIVATE_HOST_SOCKET PUBLIC_TASK_SOCKET PUBLIC_CONFIG TASK_UID HOST_SHA256
```

`HOST_SHA256` is the lowercase SHA-256 of the fixed Mini Host executable
selected for this service. The frontend requires the public config bytes to
match the native socket's private `host.config` pin. Its public socket, config,
and durable service lock all live directly in the dedicated public directory.
It removes inherited default/access ACLs, then grants only `TASK_UID` directory
traverse, config read, and socket connect. A second instance refuses the lock
before changing ACLs or unlinking a socket. The operator must run one frontend
per task UID and use a distinct directory for each.

The task's runtime JSON uses the public `hostSocket` and `hostConfig`; its
`stateDir`, control socket, custody keys, and workspace remain task-private and
distinct. Run [`install-controller`](install-controller) as the task account for
each reviewed runtime JSON. The frontend does not replace native signed
authority, generation, budget, or Store admission. Publish only a reviewed
host config: it is intentionally readable by that task UID, even though its
private original and Store remain operator-only.

Each request must carry the exact version-2 native socket envelope with the
pinned config bytes and Host image digest. The frontend permits native grain
operations 0–11, bounded read-only provider continuity operation 17, and
bounded read-only provider quote operation 19. It refuses fn operator actions
12–16 and 18. The configured provider resource is one cell per Mini Host
config; tenants with different provider cells need separate private Host
services/configs. A task UID has the allowed operations on its frontend; source
authority and the native Host still decide whether any signed call is valid.
The frontend does not reinterpret an accepted request or retry it. If a client
disconnects after forwarding, the native outcome can be uncertain and must be
read back through the normal Mini/controller recovery path. One slow backend
can also delay other frontends sharing that private Host; do not claim
per-tenant availability isolation from separate sockets.

Before offering access, check the native Host binary hash, pinned config and
Store provenance, task UID, dedicated ACLs, and a signed read through each
task's own socket/key. Check that another task UID cannot read that config/key
or connect to that socket. A synthetic transport probe is useful for frontend
policy, but only signed Mini reads and mutations prove the native authority
boundary. See [`host-frontend-probe.rs`](host-frontend-probe.rs) for bounded
forbidden-op and partial-frame checks.
