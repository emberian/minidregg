# Bounded forward-link end-to-end benchmark

This benchmark intentionally preserves the deployed authority split instead
of inventing one native semantic controller.

`scripts/ForwardLinkSemanticBenchmark.lean` measures the actual computable
four-slot production content-page path:

- canonical bounded link-entry submission bytes;
- `Page.admitInsert` validation;
- typed-patch validation, logical installation, and the Lean cSHAKE page root;
- exact state-codec reopen;
- canonical semantic link lookup; and
- retained physical cross-page route lookup.

`native/hyperdocument-link-store/src/bin/forward_link_e2e_bench.rs` measures
the actual opaque `LocalLinkStore` path. Stage, install, restarted read, exact
retry, and reopened read each occur in a fresh child process. The install
response is deliberately ignored before the restarted reader observes the
14-byte Lean-authored recovery fixture.

The combined runner first builds the existing `LinkEndpointController`,
`PageDurableWeld`, `LocalFileStore`, and `ClientLocalFileCutover` proof joins,
then runs both timed surfaces. Those proof modules establish the exact
read-result and bounded-page correspondences. They do not prove the Rust
filesystem implementation refines the Lean model.

Run locally with:

```sh
bash scripts/run-forward-link-e2e-benchmark.sh
```

For quick harness checks, the native sample counts may be reduced with
`MINIDREGG_LINK_BENCH_SAMPLES` and `MINIDREGG_LINK_BENCH_WARMUPS`. Committed
evidence uses the defaults: 31 measured samples and three warmups. The Lean
surface always uses 31 measured samples, three warmups per stage, 16 repeated
operations for ordinary stages, and one operation for the cSHAKE-root stage.

## Interpretation ceiling

- `first_measured_after_warmup` is not a cold-cache measurement.
- Repeated samples are warm-process measurements only for the Lean executable;
  every native stage still pays child-process startup.
- Each native lifecycle uses a fresh directory, but OS page and filesystem
  caches are uncontrolled and are not flushed.
- Rust validates only the 4096-byte bound, same-byte retry, no-overwrite
  conflict, and exact returned bytes. It never parses a link or mints semantic
  acceptance.
- Successful `sync_all` and `hard_link` calls are observations, not proofs of
  POSIX semantics, stable media, power-loss survival, or adversarial-race
  safety.
- Lean timings do not include OS I/O, network delivery, credentials, external
  finality, UI rendering, or agent-runtime delivery.
- No per-stage memory number is reported: neither harness has a reliable,
  comparable allocator/RSS attribution for the selected stage boundary.
- Percentiles are nearest-rank order statistics over the raw measured samples;
  there is no performance threshold or throughput claim.
