# Provider gateway namespace component gate (2026-09-27)

This is a source-matched **component** gate for the controller's private Unix
provider gateway and worker-local HTTP bridge. It used no Mini Store, custody
key, paid provider key, model call, or live 780x/9301 controller. It does not
establish native reserve/settlement, real Hermes ACP behavior, or a hosted
private-workroom end-to-end result. Those require a fresh native fixture.

## Source closure

The reviewed source and local files at the final Rust gate were:

| File | SHA-256 |
| --- | --- |
| `native/grain-runtime/Cargo.toml` | `c59a58621676309ed7ce61923e59da2c48b0566ff03d6965ff222c65cf3b7f58` |
| `native/grain-runtime/src/main.rs` | `0e895e0cc7a6fd623140fb5c3838c41332015150dad4c77b68efb66a8a0eeff7` |
| `native/grain-runtime/src/provider.rs` | `ca7f5f07ad29d54cac80759cbc16d0053f97afda2f032c498421c155fb6afc28` |
| `native/grain-runtime/src/provider_profile.rs` | `7dea6ed343b9e8b9db4d248749991b1b594af82d783d5ae2aec9d65c555ed3b7` |
| `native/grain-runtime/src/provider_bridge.rs` | `c9db79ef1f90cbbfcd5316313716677881994aab70bb2bf00266ee0ca52f8ce5` |
| `deploy/grain-host/bwrap` | `05010aaa0977c55a1dc1feaf54f622f8473f4dda21817149e5ac90714bd17f1c` |
| `deploy/grain-host/install-controller` | `94dfca819055b06157c44b3a30b91cba165b72d7b053c77d2b3bf3f80e3ead31` |
| `deploy/grain-host/install-operator-stack` | `759bfb697b48116f24e6938d024f89e4d1ecc22b6b6e1c9d4c952cda7537a2d7` |

The Rust command was
`CARGO_BUILD_JOBS=2 cargo nextest run --manifest-path native/grain-runtime/Cargo.toml --status-level fail`:
**69/69 passed**, run ID `9c3b2795-1200-40bc-9284-a22eed2b2ba6`. The
same manifest's `cargo clippy --all-targets -- -D warnings`, `cargo fmt
--check`, `bash -n` and `shellcheck` for the three deploy scripts, and `git
diff --check` passed. Rust tests include the private socket's mode/token and
owned stale-socket checks, exact per-connection bridge delivery acknowledgement
versus missing acknowledgement, lease revocation, and bounded HTTP framing.
An acknowledgement means the bridge completed its local socket write. It does
not prove that Hermes consumed the response.

## Isolated Linux component observations

Persvati scratch `/tmp/mini-provider-egress.HdVYET` contained copied source,
compiled bridge/gate binaries, a dummy Unix provider responder, and a dummy
MCP responder. The bwrap worker had `--unshare-net` and loopback UP. Its direct
HTTP attempt to TEST-NET-2 (`198.51.100.1`) failed with no route. The same
worker reached the mounted provider Unix socket through the local bridge,
received exact body `OK`, and the dummy responder captured 196 request/ack
bytes. A separate mounted MCP Unix socket exchanged `PING`/`PONG` with a Rust
client inside the same namespace layout. A bridge plus sleeping worker stopped
after launcher TERM; the transient unit was inactive with MainPID 0. All seven
scratch worker units were later observed inactive with MainPID 0. The final
launcher source hash `05010aaa...` and bridge source hash `c9db79ef...` were
copied and rechecked in scratch; unit `mini-grain-t999901-o18768` repeated the
isolated HTTP/no-outbound case with 196 request/ack bytes and MainPID 0.

The first MCP probe used Debian's `/usr/bin/nc` alternatives symlink, which
was absent inside the deliberately small mount, and the second used a socket
without the intended private mode. Those harness attempts made no MCP claim.
The final Rust socket client/server probe used a mode-0600 socket and passed.
The scratch provider responder was a raw Unix fixture, so this does not claim
the full controller/provider protocol ran on Linux. The final Rust and bwrap
source hashes above were rechecked against the copied scratch source.

## Remaining gate

Run a fresh synthetic Mini Store with the exact Linux Host/client/controller,
bridge, launcher, and Hermes ACP source images. Use a deterministic local
upstream through the isolated Unix route, verify signed parent/provider
reserve, op17 continuity, metered or fixed settlement, terminal completion,
and hard-EOF cancellation with worker/bridge cgroup teardown and conservative
held uncertainty. No real provider key or paid call is needed for that gate.
