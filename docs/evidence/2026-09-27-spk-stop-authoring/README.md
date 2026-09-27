# STOP BEGIN and claim assembly source gate

Two new Linux SPK-host modules connect the source-owned STOP operator routes
to the sealed fresh STOP claim. `lifecycle_v3_stop_begin_native.rs` authors a
STOP request from the signed SPK descriptor, invokes the distinct op66
Plan-v2 route, inspects and binds its prior running witness and current
source plan, signs only pinned management headers, assembles op67 and submits
the exact BEGIN ingress once through op22. It retains the raw frames,
detached signatures, source inspections, durable attempt markers and the
four-field installed receipt. An uncertain op22 response leaves the original
attempt; the function does not retry it.

`lifecycle_v3_stop_assembly_native.rs` takes only that confirmed STOP BEGIN,
uses a fresh nonce for the current-image op68 plan, checks the original BEGIN
receipt, descriptor, app, management subject and absent START binding in the
source inspection, signs pinned claim headers, and assembles op69. Its
`submit_fresh_once` consumes the assembly and delegates to the sealed op26
fresh-CAS-winner path. The STOP Plan-v2 and exact BEGIN/claim ingresses remain
retained across those steps. No op27 historical lookup can construct a
physical permit.

The source was copied into the independent hbox Linux build directory
`/tank/dregg-build/mini-spk-v3-fresh-stop-claim-fn` with a separate Cargo
target and `CARGO_BUILD_JOBS=2`. Focused STOP `cargo nextest` passed 7/7,
including the earlier sealed claim and target tests. Strict all-target Clippy
passed. Terminal logs are retained here. This is a source/compile gate:
there has been no signed STOP native acceptance, physical fence, systemd
stop, or post-stop completion. The callable supervisor and checked fence
join are separate integration work.
