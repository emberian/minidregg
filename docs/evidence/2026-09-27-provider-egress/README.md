# Provider gateway namespace component gate (2026-09-27)

The first gate below is source-matched component evidence for the controller's
private Unix provider gateway and worker-local HTTP bridge. The later native
gate used a fresh, private Mini Store and actual Hermes ACP against a
deterministic loopback provider. Neither gate used a paid provider key or
model, or touched the live 780x/9301 controllers.

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

## Fresh native Hermes/Mini gate

The separate private Persvati deployment
`/tmp/mini-provider-egress.HdVYET/fresh-8211` was born from
`native/grain-runtime/acceptance.sh` with unique controller/tool/provider tasks
8211/8212/8214 and publication resource 8213. Its Store and keys are not in
this evidence directory. The source-certified Linux Host was SHA-256
`30731bb4e35b784ab58fa8f442407ef2bc4fddeed77ab782a5056f107096fc82`
(181-module source manifest
`6a819c8125c5c78031b438beb4592281781b0c974d5338250e06514f0757e7ea`).
The release controller and bridge were built from the source hashes above,
with binary SHA-256 `3fcfa493c6dc60dbed5a60dab88c45826d4bfe10cff49214cf83f9e1e90d14cf`
and `3d1f47ed3c7c216103e3564f5b4a84994e49136f37f1e03db3cb374157e00a8a`.
The Mini client was SHA-256 `fee5bc861d74c9e432db2374ede36b62852a80346a46f1dc89133dfa79bf11eb`.
The SQLite and signature helpers were older source-built images; their exact
hashes, plus the launcher, gate, fixture, private config and runner hashes,
are retained in [images.sha256](native-8211/images.sha256). This is a measured
image set, not a claim that every image came from the latest source revision.

The fixture provider source was copied to private scratch and changed only to
recognize publication resource 8213 instead of the older fixed 7003. The
local provider binary SHA-256 was
`257d22b022520648d6b0c525fb5f54d7cf6d26169f717ecf4b7aed7bf79582df`.
The test key was a nonsecret fixture token in a mode-0600 file directly inside
the controller's private state directory. Worker bwrap used `--network none`;
Hermes connected to `127.0.0.1:18988/v1`, whose listener was the bridge inside
its isolated namespace. The bridge used the private gateway Unix socket to
reach the controller; only the controller's pinned provider transport reached
the fake upstream at `127.0.0.1:18987`. The earlier component probe separately
showed direct non-loopback egress refusal.

[Provider stages](native-8211/provider-stages.log) show three model responses:
read publication, publish using the signed root, and complete. The controller
retained a native tool publication receipt (operation 60, acceptedCount 19),
three metered provider settlements (operations 28/49/80, acceptedCount
11/15/23), and a parent settlement (operation 85, acceptedCount 25). Exact
four-field receipts and operation types are in
[selected-native-receipts.json](native-8211/selected-native-receipts.json).
The [run markers](native-8211/run.log) recorded a cleared parent and provider
hold after the soft turn. Hermes's MCP read and publish completed before its
final text response. This establishes actual native admission and settlement
through the Unix bridge for the soft turn; it does not test paid-provider
transport or a private workroom with two live principals.

A subsequent hard-mode prompt spawned worker unit `mini-grain-t8211-o96`.
Closing the hard connector input stopped that worker; the controller's journal
recorded `connection=fenced`, `child=null`, and no provider attempt or hold.
The [worker](native-8211/hard-worker-unit.txt) and
[controller](native-8211/cleanup.txt) units were inactive with MainPID 0, and
no bridge process remained. The controller's mode and reserve operations
91/94 were natively confirmed, with reserve acceptedCount 28. **The runner
then stopped the controller too early to await the signed interrupt.** A
read-only signed post-stop query shows parent status 3, generation 1,
remaining 96, reserved 3; its durable parent hold remains. The provider is
clean at status 0, generation 6, remaining 41, reserved 0. See
[signed-final-views.json](native-8211/signed-final-views.json) and the
[keyless journal projection](native-8211/final-journal-projection.json).
Accordingly this gate proves physical hard-EOF stop and conservative held
uncertainty, **not** completed hard-fence or post-hard settlement. The private
mode-0600 provider Unix socket inode remained after systemd stopped the
controller, although no bridge process survived; startup's owned stale-socket
reclaim is covered by the Rust component tests, not by this native run.

The retained raw runner marker `full_fixture_pass` predates the signed
post-stop inspection and overstates that runner's coverage. It is preserved
as emitted, not adopted as this record's verdict. The final-view JSON is a
bounded projection obtained through signed queries, not a standalone signed
attestation that a reader can verify without the original query artifacts.

The next native continuation must restart this exact deployment or use a fresh
one, retain the controller until a signed interrupt receipt and final signed
parent state are observed, and perform any required audited settlement. A
real-provider deployment also needs a separately pinned HTTPS origin/model,
operator-custodied key and explicit spending cap before any paid call.
