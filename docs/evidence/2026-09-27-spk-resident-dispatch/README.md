# Resident human dispatch component gate (2026-09-27)

This is a source/component checkpoint, not an authorized GitWeb delivery. No SPK, Mini Store, controller, or public listener was started in this gate. The public `spk-hostd` binary still serves unavailable; the resident call chain is staged behind the native lifecycle-v2 descriptor and current dispatch gates.

The staged chain is fixed-participant HTTP authoring → private Mini op36/37 → one op34 submit with a fsynced no-resend marker → source-owned inspection of the exact captured payload → hostd `DeliveryRequested` tombstone → the resident process's existing fd3 `RpcDriver` → definite response or retained uncertainty. The host journal now fsyncs a monotonic operation ID and per-ID marker under its lock before authoring; IDs may be skipped after a crash but cannot be reused. The private custodian config pins `web` or `api` session kind explicitly, and the signer configuration and physical route must match it. HTTP tokens do not select a Mini subject.

Source SHA-256:

| File | SHA-256 |
| --- | --- |
| `native/spk-host/Cargo.toml` | `eb191c795e4f061297c2f61cad09e975a63bff5640711f5585a7c73d38d038eb` |
| `native/spk-host/Cargo.lock` | `8fc4fc1a81c2ab4da2903c2a4095c620ec647fe7f131cb6176f23e5c1c6b86a3` |
| `native/spk-host/src/bin/spk-hostd.rs` | `d2bacb3eea7721d46816aea691c13a9ba0c44751615ba043c175a0b7c731b8fb` |
| `native/spk-host/src/dispatch_author.rs` | `8bce8953977da01f043f01a6aeed5c372ad5079685a4fb2fe5683985cc9f1380` |
| `native/spk-host/src/dispatch_native.rs` | `e50b3bc322e09ccae35a19d2e08e9a00b09fe7336943b07895b1df4fe55032ac` |
| `native/spk-host/src/dispatch_delivery.rs` | `b2537f156f543a474e3d4dbd77db23041969052256bdc712dfba051b76d4b59a` |
| `native/spk-host/src/dispatch_inspection.rs` | `c16ca1f1cac38824cace02a2ace2ff2b8b7b20700ec35f3547c3b26cd8c8b310` |
| `native/spk-host/src/hostd.rs` | `83175a60dc54b3499310770144816fcab66358c75fc6685e935dc51bd52ac713` |
| `native/spk-host/src/http_entrance.rs` | `2115494dff516a3541ed297b93a12309431bb39278863155b5a8d668d8065213` |
| `native/spk-host/src/lib.rs` | `318c1388ab76b89c2aec3dc7be80c513100f8327a03d9d4dbe24168f834c7a21` |

On hbox, the private source copy at `/tmp/mini-spk-http-response-20260927/native/spk-host` used the exact lock hash above, offline dependencies, `CARGO_BUILD_JOBS=2`, and pinned private Cap'n Proto compiler. `cargo nextest run --offline --locked --lib -E 'test(dispatch_operation_ids_are_fsynced) | test(dispatch_author) | test(dispatch_native) | test(http_entrance)'` passed 14/14 (run `2851da6e-6bb0-4343-95e1-11b253ab77b7`). A final source-only route-kind assertion in `dispatch_author.rs` then passed 1/1 (run `650369bc-af0a-42bb-8c14-1b45cc038767`). `cargo clippy --offline --locked --all-targets -- -D warnings` passed after the 14-test cut; the final assertion was then checked again with the same strict command. The narrow tests cover exact signer slots, API path mapping, private operator framing, one-shot marker, operation ID persistence/reopen, and HTTP token/session-kind boundaries. They do not exercise a linked Mini op34 or actual fd3 delivery.

Remaining gates: source-owned lifecycle `COMMITTED/v2` and exact signed SPK descriptor comparison before app launch; linked private Mini op34/36/37 and strict read-only permit inspector; resident HTTP service caller in the same supervisor as fd3; physical process-generation/current-tip fence and no-resend recovery for uncertain responses. Agent-origin dispatch remains disabled and requires its separate dispatchTask reserve/settle plus v2 checked permit.
