# Resident launch preparation (2026-09-27)

This is an isolated component gate. It did not start an SPK, Mini Store, service unit, or public listener. The resident entry remains unreachable from `spk-hostd` until native `LIFECYCLE-CLAIM-COMMITTED/v2`, its strict inspector, exact signed SPK descriptor comparison and a current claim handoff are linked.

The existing compatibility smoke and new `PreparedResident` now use the same ordered bwrap argument builder. Preparation preopens the protected read-only image, capped separate `/var`, and one Unix socketpair; the bounded spawn gate maps only their high descriptors to fd3/4/5, pins the bwrap ELF, drops to the app UID/GID and keeps the operator resident process as the unit MainPID. The resident retains the host fd3 endpoint in one `RpcDriver` for the app generation. A child/RPC setup failure leaves the launch journal uncertain for exact recovery; it never grants an automatic restart. The journal checks the current manager MainPID as well as InvocationID/cgroup before launch and before dispatch. The private API custodian's browser bootstrap endpoint now returns 404, and the Host author helper refuses unbounded or nonprivate input before invocation.

Exact source SHA-256:

| File | SHA-256 |
| --- | --- |
| `native/spk-host/src/sandbox.rs` | `109b805d6e5bd0c7a166c72fffa3c5815230fad2873202c792d86f65326e5405` |
| `native/spk-host/src/spawn_gate.rs` (unchanged) | `05aca13dcd8d38dba040a275bbd4dfc76809f743830e354690fdbae4d1411917` |
| `native/spk-host/src/resident_launch.rs` | `faab6bf64bcc38046457800e77c55e2199e5021a00d5867c1f9f4f96166a9bdc` |
| `native/spk-host/src/hostd.rs` | `7502ac544866d0b6395ad733492faa49c891a014b8bd3d2091aaf020c3050635` |
| `native/spk-host/src/http_entrance.rs` | `be16e56662491b1ea1b4b83e1195b19dbfdd9c2a52ce674bb9d9e2392392a52e` |
| `native/spk-host/src/dispatch_native.rs` | `7bebfd2d2b4585c4e3fd4691279d4e52f8d31e611559a4e35dcfd5511690d9de` |
| `native/spk-host/src/lib.rs` | `f9130f05446ecd70c802b830c5c43dc7966e446649a6ca72aca2dd407b4a6cd7` |
| `native/spk-host/Cargo.lock` | `8fc4fc1a81c2ab4da2903c2a4095c620ec647fe7f131cb6176f23e5c1c6b86a3` |

The hbox private copy at `/tmp/mini-spk-http-response-20260927/native/spk-host` used that exact lock, offline dependencies, two Cargo jobs and the pinned private Cap'n Proto compiler. A focused `cargo nextest run --offline --locked --lib -E 'test(sandbox) | test(spawn_gate) | test(hostd)'` passed 24/24 (run `f0783766-3eed-46c7-8244-4009dc6ba31f`). After the MainPID, API bootstrap and author input changes, the focused `test(sandbox) | test(dispatch_native) | test(http_entrance) | test(dispatch_operation_ids_are_fsynced)` set passed 14/14 (run `1d425677-a071-4815-a481-7f495dbd95d0`). The final changed-source selection `test(shared_bwrap_args) | test(resident_refuses_app_uid) | test(private_v2_operator_frame) | test(transport_deadline) | test(dispatch_operation_ids_are_fsynced)` passed 5/5 (run `799c950a-b7ca-4611-aabb-5895609dec96`), followed by `cargo clippy --offline --locked --all-targets -- -D warnings` PASS. These are structural and harmless-process checks; they do not assert real SPK startup or fd3 app readiness under native admission.

Actual application execution still requires a fresh Store with the completion custodian public key pinned at genesis, a source-owned COMMITTED/v2 claim, exact canonical frame comparison, a one-parse signature-verified SPK descriptor match, and a bounded systemd unit run. A Mini op34 callback remains a point-in-time permit; without a coordinated native lease, physical dispatch cannot claim instantaneous revocation across the callback-to-fd3 hop. Agent-origin dispatch remains disabled pending its separate dispatchTask purse and checked v2 permit.
