# Agent lifetime SPK binding component (2026-09-27)

`native/spk-host/src/agent_api_lifetime_v3.rs` SHA-256
`74ad71b449a544340390f11deaa3c48a7df708a8c2d67869c294c2b869ddac7c`
is a separate v3 transport comparison module. `native/spk-host/src/lib.rs`
registers it on Linux. The module keeps the original event22 session origin
generation, issue index, descriptor digest and exact four-field receipt distinct
from the current app, session, parent and purse coordinates. Stable Hello
fingerprints only this lineage and the app process incarnation. A separate
operation fingerprint commits fresh current coordinates, operation ID and
exact request SHA, so reconnect cannot substitute a new generation into a
retained uncertain request. It also pins the
event27 grant resource, index, digest, initialized root and exact receipt.
It checks source-inspected reserve, paid and committed projections against the
retained HTTP bytes and current observations. The purse root after reserve is
compared as a separate signed coordinate, not reused from the pre-reserve
binding fingerprint.

On hbox, only the new module and lib registration were copied over the private
SPK host source snapshot at
`/tank/dregg-build/mini-spk-runtime-review-v3/native/spk-host`. The source
copy's module SHA-256 matched the local file. With the separate warm target
`/tank/dregg-build/mini-spk-v3-agent/target`, the following bounded checks
passed:

```sh
CARGO_TARGET_DIR=/tank/dregg-build/mini-spk-v3-agent/target CARGO_BUILD_JOBS=2 cargo nextest run --offline --locked --lib -E 'test(agent_api_lifetime_v3::tests::)'
CARGO_TARGET_DIR=/tank/dregg-build/mini-spk-v3-agent/target CARGO_BUILD_JOBS=2 cargo clippy --offline --locked --all-targets -- -D warnings
```

The four focused tests cover historical/current generation separation, the
exact 32-hex systemd invocation ID (with 64-hex refusal), changed
HTTP and roots, a changed paid post-reserve purse root, and changed committed
frame, receipt and original descriptor. Nextest run
`91e680a3-5bf7-4de7-94cb-28988951f75c` passed 4/4; strict Clippy passed.
Exact logs are `nextest.log` and `clippy.log` in this directory, with hashes
listed in `SHA256SUMS`.

This is a source/transport component gate. JSON inspection and historical op77
lookup do not confer delivery authority. The resident v3 wire and fd3 callsite
remain disabled pending a fresh installed native op76 callback, exact source
inspection, signed current task readback, and physical process/lease fence.
