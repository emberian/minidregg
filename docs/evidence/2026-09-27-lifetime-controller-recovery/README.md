# Lifetime controller recovery source gate (2026-09-27)

This is a source and Rust test gate for the eight-file grain-runtime v3 controller cut listed in `SHA256SUMS`. It is not a native event26/27 admission, resident fd3 dispatch, same-r3 app journey, or real-provider result. The same-r3 Store had no accepted app birth when this gate ran.

The controller checks the resident's numeric `worker_wall_seconds` against the selected active scoped Hermes command's effective wall before op80. It retains that value and echoes `effectiveWorkerWallSeconds` from both fresh and exact read-only reserve inspection. A mismatched, inactive, or foreground worker is refused; the logical 1800-second reverse RPC maximum does not extend the physical worker lifetime.

For a definite v3 app response, the forward journal now retains the dispatch attempt ID, exact confirmed native `DispatchSettlement`, and response SHA before clearing the dispatch attempt. Recovery fills the same record after exact native lookup. `inspect-settlement-v3` is read-only with respect to Mini admission: it rechecks the saved source/call/outcome, exact native lookup receipt, and signed purse terminal status 1 or 6 with reserved 0. Missing or uncertain evidence returns `dispatch-settlement-uncertain-v3`, never a new app send. A definite `http-v3` reply requires the retained settlement marker.

From `native/grain-runtime`, `cargo nextest run` exited 0 with **129/129 passed**; the complete bounded output is `nextest.log`. `cargo clippy --all-targets -- -D warnings` exited 0 with output in `clippy.log`. `cargo fmt` and `git diff --check` passed. Focused worker-wall mismatch, durable journal reopen/tamper, v3 definite-reply, historical inspection, and full reserve-frame tests are included. There is no native crash-after-settlement fixture in this gate; the positive settlement inspector still requires a qualified Mini/resident journey.

Independent source review at these hashes found no blocking custody or crash-ordering
bypass in the changed paths. `inspect_application_api`'s `recoveredHttp` is a
historical response presentation, not current settlement or delivery authority:
it does not independently re-query native settlement. Physical recovery uses
`inspect-settlement-v3`, which does perform that revalidation. The review did
not independently rerun the reported test suite.
