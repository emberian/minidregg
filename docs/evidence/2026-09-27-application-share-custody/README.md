# Application share operator custody checkpoint

This source checkpoint adds a restricted resource-client path for application share issue. `native/resource-client/README.md` documents the operator socket, complete canonical Request approval, ordered signer manifest, and exact lookup recovery commands. The client uses source-owned Host author/inspect/plan/assemble operations, signs only exact Host signing headers with pinned operator keys, and submits the assembled ingress only once. Op32/33 are unavailable on the participant service; an operator service requires an owner-private socket path and matching peer UID, and a service mode pin rejects public-to-operator restart of an existing endpoint.

Focused check on 2026-09-27:

```text
cargo fmt --manifest-path native/resource-client/Cargo.toml --check
PASS
cargo nextest run --manifest-path native/resource-client/Cargo.toml -E 'test(share_issue) | test(unsigned_share_issue_plan_stays_off_public_socket) | test(service_mode_pin_refuses_public_to_operator_restart)'
6 passed, 56 skipped
```

The six tests cover full canonical Request approval (including funding), ordered slot/key/header substitution refusal, lost-submit receipt anchoring and later drift refusal, frame-only crash recovery, public socket op32 refusal, and service mode restart refusal. The earlier full fast crate check passed 60/60 before the final exact-header pin; the focused six tests above and formatting were rerun after that change.

Source SHA-256 at this checkpoint:

| File | SHA-256 |
| --- | --- |
| `native/resource-client/src/share_issue.rs` | `cedeea45c07e61e73a515f46765cccc70a63925df50f25912116c773dc89bfc4` |
| `native/resource-client/src/main.rs` | `a4d779b86e989c2867d542c6e981eccf75217916af7e0ca6ead3cbde84c15ccb` |
| `native/resource-client/src/transport.rs` | `741a4f61b5d064a54a97ec73c3da923a04e4e51882b5795852dba3bdb09b9684` |
| `native/resource-client/README.md` | `7403ba10217e129ce9f852c06d8d3f2495a7a4edd63aba92e4e338c46bed6b3e` |

This is a source and focused-client check. A source-qualified native Host with the final share Plan v2 and physical-root repair was still building; no share issuance or dispatch acceptance is claimed here. Native op28 remains the current authority and policy admission gate.
