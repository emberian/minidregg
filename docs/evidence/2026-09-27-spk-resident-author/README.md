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
launch. No image was installed by this qualification and no Mini Store was
changed. The current service still reads prebuilt private
BEGIN/CLAIM ingress and stays disabled for the dynamic production route.
The generic Mini descriptor author/inspect route is direct-Lean green but not
in the separately certified `bf04c29` Mini Host; the Rust qualification ELF
above is a different executable. INSTALL materialization/completion and START
native acceptance remain separate work.

The actual private GitWeb parse-only run on Persvati returned
`qualification_verified` from unit
`mini-spk-qualify-20260927101452-3756376`; the wrapper checked the named
unit's exact `Finished with result: success` and `status=0/SUCCESS` verdict.
The unit was unloaded after `--collect`. The root-owned 0600 observation at
`/var/lib/minidregg/spk/qualifications/sha256-2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa.json`
is 1,941 bytes, SHA-256
`0610aedad24634f403b4c7e8f53326c59bc4b891cad6c12906b5edfaab137c8a`.
It records the signed GitWeb raw SHA-256
`2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa`,
length `14045864`, AppID
`6va4cjamc21j0znf5h5rrgnv0rpyvh1vaxurkrgknefvj0x63ash`, version `10`,
signed manifest SHA-256
`3ef23992c6ee79e5b684cec632d4552c5b34889348ae63acaaedb42b9616024f`,
and signed bridge SHA-256
`49d196f64ca2ce672a378581a8376ada53b27614bba522bbaec042237f0e70a2`.
Rehashing the retained bridge member bytes reproduced that hash; the decoded
path was `/repo.git/` with `[read, write]` and guest/developer role bits.
The matching content-addressed image directory already had a pre-run mtime
of 00:59 local, so this run does not claim it was absent; qualification has no
package-store write path. No GitWeb app process ran.

The isolated release ELF under
`/opt/minidregg-spk-qualify-20260927/bin/spk-host` is root-owned mode 0755,
SHA-256 `d7084c3d2e08fe507ff8dc77087d2034f03be447a4c512f9f84a88e6352088c1`.
Its source manifest is retained privately at
`/tmp/mini-spk-qualify-source-20260927/source-sha256.txt` (SHA-256
`879437c108b93c8d565d0d446170766fa2e7a2cd989d140edde8bf20a458168a`);
the release build log SHA-256 is
`be8830824da4e2fde9acde9c95b4cddcf5d707ba88cc7c0d7d1d1d04d6b7d25b`.
Hbox's first release attempt failed only because `capnp` was absent there;
the same isolated source compiled on Persvati with `/usr/bin/capnp`.
The JSON record is a recreatable observation; the wrapper does not fsync its
final copy and it is never a durable Mini lifecycle success record.

Private hbox snapshot at `/tmp/mini-spk-http-response-20260927/native/spk-host`
used two Cargo jobs and the pinned offline lock. `cargo nextest run --locked
--offline` passed 80/80 on `main.rs` SHA `63e9e847` and wrapper SHA
`80878641`, before the no-API-path output was normalized from null to the
source codec's empty string. On the final `main.rs` and wrapper hashes in the
table, strict all-target Clippy plus `bash -n` and `shellcheck` passed, and
the physical GitWeb qualification above used those exact final bytes. The
snapshot retains earlier versions of separately owned `rpc_adapter.rs`,
`sandbox.rs`, and `spawn_gate.rs`.

| File | SHA-256 |
| --- | --- |
| `native/spk-host/src/resident_begin_native.rs` | `8fbeebef8a91c0b815059e511f6701ca387a1615bcc9879e79e6f6561aa2859b` |
| `native/spk-host/src/materialize.rs` | `87f959e8a301fe4f599d0068b9f75584867e83e88039458d98cc5337a86425b2` |
| `native/spk-host/src/main.rs` | `cd450ef6019a625c87e155f15fb27474665fbe349b624c529781acefb8d17aea` |
| `native/spk-host/src/claim_descriptor.rs` | `c1b5685c9d0864f26d4d91f0a84c3b42d7af7f16a5fdfc019eeeee8a912045af` |
| `native/spk-host/src/claim_native.rs` | `788c90cdba4f86a597b52509171e363a8c0e34f0309ed99ff13aa80467a1b3f3` |
| `native/spk-host/src/lib.rs` | `4b793736142a40be9a5babaea3a030ea4bda1e270c840948d484500020e7c1b7` |
| `deploy/spk-host/spk-qualify` | `d2d9f52bfdd28dfad29cf93f0508e68befd2d05c67b051c999752a4b3fdd537d` |
