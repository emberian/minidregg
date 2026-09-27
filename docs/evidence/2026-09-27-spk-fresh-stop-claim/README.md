# Sealed fresh STOP claim source gate

`native/spk-host/src/lifecycle_v3_stop_claim_native.rs` adds a private
`FreshStopClaim` whose only constructor submits the exact retained v3 STOP
claim ingress through pinned operator op26 once. It writes and fsyncs the
retained Plan-v2, BEGIN, ingress and a parent-level one-send marker before
submission. It retains the raw op26 response before decoding. Only the Host's
fresh installed CAS-winner committed-v3 callback can continue; a replayed
op26 response or op27 historical lookup returns a different receipt-only
frame. Uncertain or partial responses leave the attempt for read-only
investigation and cannot be reentered in that journal.

The constructor preflights the source STOP Plan-v2, inspects the exact fresh
committed frame and original claim/BEGIN bytes, and runs the pinned Host's
`inspect-stop-claim` against the current verified image. `StopTarget` checks
the exact Plan, frame, BEGIN, both four-field receipts and prior running
witness. The sealed type retains those original bytes and exposes read-only
accessors, including `target()`. This module never fences or stops a unit;
the separate physical path must join the retained Running journal and volume
witness, persist the STOP fence marker and check the exact target under the
journal lock before manager action. Historical receipt recovery cannot
construct `FreshStopClaim`.

The source was copied into an independent hbox Linux build directory at
`/tank/dregg-build/mini-spk-v3-fresh-stop-claim-fn`, with a separate target
directory and `CARGO_BUILD_JOBS=2`. Focused `cargo nextest` passed 3/3,
covering canonical receipt shape, exact committed source echoes and refusal
of receipt-only/historical callback framing. Strict all-target Clippy passed.
The terminal logs are retained here. This is a source/compile gate, not a
native STOP acceptance or proof that the physical fence has run.
