# Resident shared-app and private agent component check

2026-09-27, isolated hbox source snapshot under
`/tank/chreatures/mini-spk-resident-check-20260927`. This is a Rust
component check, not an accepted Mini START, an event21 delivery, or an app
launch. No Store, signed GitWeb volume, live controller, or public listener was
changed.

One resident MainPID is staged to poll 1–8 separately pinned human entrances
and 0–8 private agent sockets with one fd3 `RpcDriver`. Agent routes have
distinct controller UIDs, socket ACL parents, custody, reverse sockets and
attempt directories. A hard caller EOF leaves its operation one-shot uncertain;
only an exact worker-release witness can clear the shared app's busy slot for
another participant. The worker ACK does not prove the app rolled back an
effect. Success returns the same noncloneable fence so a later response
serialization/retention failure can preserve the uncertain tombstone while
releasing the shared slot. A missing ACK keeps the slot held for audit.

The resident START entry now refuses `source-bound START action selection
unavailable` immediately after validating its private config and before
opening the Journal or contacting Mini. The current BEGIN-v2 claim does not
select GitWeb's signed first-create action versus its continue command for a
retained grain volume. The virgin volume remains untouched. A versioned Mini
descriptor/START claim/report must bind the chosen signed command and stable
volume resource before this guard can be removed. The root may omit the
`resident-run` CLI hunk from the component commit; the snapshot tested here
includes that guarded entry.

## Exact tested source

| Path under `native/spk-host/src/` | SHA-256 |
| --- | --- |
| `resident_service.rs` | `53c738fc27feef0525f56e9d3d7b7e7eab18f305d4a95bbad349a4db0db12080` |
| `http_entrance.rs` | `af9f1f5150876f4f1ab7618cc1586e05a9f02342856d17e94c5975eb06398aad` |
| `rpc_adapter.rs` | `6e26e389bea4989afdf2718a6a4f5fcf6581aea5179eef28353fdc45726655c1` |
| `hostd.rs` | `6cf8f9fd2ca136352c069b4f4043d8030db38401632f7ef15e64b5f2739e261a` |
| `agent_api_custody.rs` | `7e3ddc1d780a20b4f197c5a6eee6c9ad0b91040523c1ff760f573e6e81a55408` |
| `agent_api_native.rs` (current, comment correction) | `49b1e96651eba7b746453968d758c957c795d55ce53d0f5205f1a8930657b955` |
| `agent_api_server.rs` | `ee4b325e432ee6060957e6434854da7943605e0880f110d252da82577af503d4` |
| `agent_api_wire.rs` | `3e4ed3d3476846ea9127f9ca8bc303872bad7296d2de1c3a13be8d00a1787ee1` |
| `lib.rs` | `4346bebf5f09a9febff8d1f567f15ef962b42d9554f1c4653fe45223cae54934` |
| `main.rs` (snapshot, CLI staging) | `5fe0f65d514dd0188b35745a6b944972a835adda6f884858ef14092daa7053ed` |
| `bin/gitweb-session-smoke.rs` | `a7c4be62eb06a66015fe936c0442a0f18630e9008166c099a98432d6e6cae3b2` |

`native/spk-host/Cargo.lock` was
`8fc4fc1a81c2ab4da2903c2a4095c620ec647fe7f131cb6176f23e5c1c6b86a3`.
The isolated hbox copies of the listed source files matched these hashes.
Existing foreign `sandbox.rs` SHA-256
`8922016e35c4cebac6e91cc13c63a153b43a5f55c8e0694e6b37bd6c588af5e2`
and `spawn_gate.rs` SHA-256
`229a4581cff00f4ed3292936bb3a5f68c9eab374b4118e520c2e4d1df6c2603b`
were present in the tested snapshot. They differ from the committed base and
are **not** part of this component's owned source/staging scope.

## Bounded Linux verdict

The source was copied to a private hbox target, with a private `capnp` toolchain
wrapper. Both tests ran in user transient units capped at 4 GiB memory,
200% CPU, 128 tasks and 1200 seconds. Cargo used two jobs and `--locked`.

| Command | Unit | Result |
| --- | --- | --- |
| `cargo nextest run --locked --lib -p minidregg-spk-host` | `mini-spk-resident-nextest-20260927-r11.service` | 104/104 passed, `Result=success`, `ExecMainStatus=0`, inactive/MainPID 0; peak 693.9 MiB |
| `cargo clippy --locked --all-targets -- -D warnings` | `mini-spk-resident-clippy-20260927-r11.service` | PASS, `Result=success`, `ExecMainStatus=0`, inactive/MainPID 0; peak 344.1 MiB |
| `cargo nextest run --locked --lib -p minidregg-spk-host` after native comment correction | `mini-spk-resident-nextest-20260927-r12.service` | 104/104 passed, `Result=success`, `ExecMainStatus=0`, inactive/MainPID 0; peak 791.4 MiB |

Retained [nextest-r11.log](nextest-r11.log) SHA-256
`7ac28923cc77545ea66395fe94cd23062aaeb33dab71d2119308d8427f3b3a23`
and [clippy-r11.log](clippy-r11.log) SHA-256
`87db4f007baa2610e179fec3b1f57b9085a613e56b59971dcd0566a56f17476a`.
R11 used `agent_api_native.rs` SHA-256
`eda81896031121ccc93629dca65d30422f1e521f76a6262542794272456b70de`.
The later native change to `49b1e966...` corrects only the comment about the
per-route active marker; production code and tests are byte-identical. The
exact current-source [nextest-r12.log](nextest-r12.log) SHA-256 is
`d6bb22398019e107f8ce39f99707813ca22410aa9c90545941519524d2fcf058`.
Strict Clippy was not repeated for the comment-only r12 change. The earlier
r8 snapshot passed 103 tests before the full config-loading regression and
new Hello fields. The r9 snapshot passed 104 tests with the new Hello fields,
before the START guard and boxed wire variant. These results are dated
historical checks, not substitutes for the r11/r12 cut.

The tests exercise custody framing, exact reply recovery, ACL refusal,
two-agent polling, config-time socket-parent separation, per-operation
uncertainty and worker-release handling. They do not establish a paid agent
event21 permit, controller hard-EOF journey, physical GitWeb create/wake, or
two-participant Mini-authorized HTTP delivery. Human `RpcDriver::dispatch`
still has its earlier whole-driver timeout behavior; the typed worker-release
path here is for cancellable agent dispatch.
