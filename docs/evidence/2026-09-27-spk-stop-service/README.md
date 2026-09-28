# Resident STOP supervisor source gate — 2026-09-27

`spk-host resident-stop PRIVATE_CONFIG` is a callable operator route. Its
owner-private JSON config uses `protocol: "mini-spk-resident-stop-v3"`, an
absolute `residentStartConfig` pointing to the retained v3 START config, and
five distinct, initially absent journal children: `beginAttemptDir`,
`claimAuthorAttemptDir`, `claimAttemptDir`, `reportAttemptDir`, and
`completionAttemptDir`. The START config supplies the pinned Host/config/socket,
signers, completed signed-SPK descriptor, volume identity, custody seed, and
nonce ledgers. HTTP callers cannot choose the STOP target.

On a Running journal with no prior STOP marker, the route submits one
source-authored event23 BEGIN, assembles and submits one event24 claim, accepts
only the sealed fresh installed op26 callback, and durably pins the original
prior-running event25 unit/incarnation before the manager fence. Fenced
recovery reads that exact private attempt and uses only the Fenced-only hostd
method. Stopped recovery performs a read-only under-lock exact manager/cgroup
and volume audit. Neither recovery path submits op26 or invokes the fresh
fence. A partial first attempt on a still-Running journal fails closed.
One owner-private nonblocking `.resident-stop.lock` is held from before attempt
selection through op38 submission or lookup, so a simultaneous invocation
cannot classify an active partial assembly as a crashed attempt.

The checked post-stop audit is source-authored into a V2 stopped physical
report and signed by the distinct physical custodian. Its
`observationDigest` is the canonical decimal Nat formed from the **little-endian
32 raw bytes** of SHA-256 over `DREGG/SPK-STOP-POST-AUDIT/v1` followed by
canonical JSON of the selected app, running generation, image identity, and
the exact manager/cgroup observation. It is an explicit operator attestation;
Mini does not independently observe systemd. The retained report is rederived
with the pinned source Host and its signing frame/signature are checked on
reopen. A crash after report-directory creation or partway through pure report
authoring fills only missing artifacts, comparing every surviving artifact to
the newly source-derived bytes. A partial completion assembly with no op38
send marker is preserved in its original private directory; restart derives a
fresh current-image plan in a bounded `replan` child, even if the old assembly
was complete, since unrelated Mini history may have advanced. The resulting
event25 completion ingress is submitted at op38 once;
later runs use only op39 on the exact retained ingress and compare all four
receipt fields. Once the op38 marker exists, recovery never replans or sends
again. An incomplete op38 response frame is not an anchor.

Isolated hbox source snapshot:
`/tank/dregg-build/mini-spk-v3-stop-service-20260927` with distinct Cargo
target. Exact source SHA-256 values appear in `SHA256SUMS`; local/remote source
hashes matched before the final gates. Commands used `CARGO_BUILD_JOBS=2`:

```sh
cargo nextest run --manifest-path native/spk-host/Cargo.toml -p minidregg-spk-host -E 'test(/stop_service|stopped_audit|checked_stop_audit|source_bound_stop/)'
cargo clippy --locked --manifest-path native/spk-host/Cargo.toml --all-targets -- -D warnings
```

Final source-matched results: focused nextest **8/8 PASS** and strict Clippy
**PASS**. The retained logs are `nextest.log` and `clippy.log`. These are Rust
source/component checks. No live SPK, Mini Store, systemd unit, physical STOP,
or event25 completion was exercised in this cut; the integrated same-Store
INSTALL→create→STOP→continue journey remains the native acceptance gate.
