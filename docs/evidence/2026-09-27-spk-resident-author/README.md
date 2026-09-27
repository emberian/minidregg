# Resident current-image authoring and bounded SPK qualification component

`resident_begin_native.rs` stages one private operator path for INSTALL/START
BEGIN and subsequent claim. Op50 derives a BEGIN signing plan from the verified
current Mini image and fixed `residentBeginManagement`; Rust compares the
source inspection to fixed custody and signs exact headers. Op51 assembles,
then a durable marker precedes exactly one op22 submission. A fresh
`confirmed/installed` result retains the four-field receipt and canonical
BEGIN ingress. The claim request uses that accepted BEGIN history index
(`acceptedCount - 1`) and a separately durable query nonce; op52 derives a
current-image plan under fixed `residentClaimManagement`, op53 assembles
canonical ingress, and existing `claim_native::submit_once` remains responsible
for one-shot op26 and committed-v2 inspection. Historical op23/op27 lookup
does not authorize a physical action.

The operation/nonce ledger uses a stable owner-private flock file and an
append-only next-ID record. The first allocation fsyncs `2`; every later
allocation appends and fsyncs its successor before returning the consumed ID.
An existing empty, incomplete-tail, or nonsequential ledger refuses rather
than reinitializing. Focused tests cover interrupted creation/write and 16
concurrent allocations.

`spk-host qualify` signature-parses one bounded signed bridge SPK and returns
raw/member hashes plus the exact decoded signed ViewInfo schema source, without
publishing an image or starting an app. The root-only `spk-qualify` wrapper
pins the Host ELF and inbox custody and runs it in an offline transient unit
with `MemoryMax=1G` and `RuntimeMaxSec=120`; this contains Bread's XZ block
allocation, which the decoded archive size limit alone does not bound. It
checks the unit's explicit success verdict before retaining one root-private
JSON record. The later INSTALL must materialize the same raw digest and
recompare signed members. Mini owns the canonical descriptor/root authoring;
Rust qualification JSON itself is not Mini authority.

These modules are staged but not called by resident service or public app
launch. No actual SPK was qualified in this cut, no image was installed, and no
Mini Store was changed. The current service still reads prebuilt private
BEGIN/CLAIM ingress and stays disabled for the dynamic production route.
The generic Mini descriptor author/inspect route is direct-Lean green but not
in a qualified native binary. INSTALL materialization/completion and START
native acceptance remain separate work.

Private hbox snapshot at `/tmp/mini-spk-http-response-20260927/native/spk-host`
used two Cargo jobs and the pinned offline lock. `cargo nextest run --locked
--offline` passed 80/80; `cargo clippy --locked --offline --all-targets -- -D
warnings` passed. `bash -n` and `shellcheck` passed for `spk-qualify`. The
snapshot retains earlier versions of separately owned `rpc_adapter.rs`,
`sandbox.rs`, and `spawn_gate.rs`.

| File | SHA-256 |
| --- | --- |
| `native/spk-host/src/resident_begin_native.rs` | `8fbeebef8a91c0b815059e511f6701ca387a1615bcc9879e79e6f6561aa2859b` |
| `native/spk-host/src/materialize.rs` | `87f959e8a301fe4f599d0068b9f75584867e83e88039458d98cc5337a86425b2` |
| `native/spk-host/src/main.rs` | `63e9e847d4ea4f1cd3fb7f535163e7fff3b5fde62da432133ea994b49fc166b1` |
| `native/spk-host/src/claim_descriptor.rs` | `c1b5685c9d0864f26d4d91f0a84c3b42d7af7f16a5fdfc019eeeee8a912045af` |
| `native/spk-host/src/claim_native.rs` | `788c90cdba4f86a597b52509171e363a8c0e34f0309ed99ff13aa80467a1b3f3` |
| `native/spk-host/src/lib.rs` | `4b793736142a40be9a5babaea3a030ea4bda1e270c840948d484500020e7c1b7` |
| `deploy/spk-host/spk-qualify` | `808786411e6f019bc18d9793d1a64efe2f3d9df9c6513b7709af0e6a383655f6` |
