# SQLite exact-byte compare-and-swap store

This dependency-free Rust crate is the shared opaque transport for Lean-owned
durable images and the existing Hyperdocument link byte record. It stores one
BLOB through SQLite's rollback-journal transaction boundary. `compare_exchange`
replaces it only when current bytes exactly match the supplied expected image,
or reports `AlreadyPresent` when the exact proposed bytes are already stored.
Physical absence differs from a present empty BLOB. The old `publish` operation
is a thin CAS-from-absent adapter, with the same compatibility type alias.

The native code does not parse links, authorization, receipts, roots, budgets,
or replay data. `Kernel.DurableReceiver` represents a finite genesis and ordered
accepted-intent journal; reopening calls the existing
`DurableDataIntent.execute`. `Compiler.DurableReceiverCodec` supplies canonical
bytes; `Compiler.DurableReceiverIO` performs load, Lean preflight/execution, CAS,
and exact journal readback. It accepts controller-bound `DataIntent` values,
not public unauthenticated wire requests. CAS contention reloads and recomputes;
an ambiguous native response is reported as uncertainty unless readback finds
the exact committed intent. This join proves no application authorization by
itself; the accepted-effect controller is that separate required caller.

The native image bound is 64 MiB, a deployment limit. Metered resource allowance
is separate and is not a token balance or payment. Reopening replays every
intent, including growing journal lookups, so work can grow quadratically with
journal length. Every commit rewrites the whole image. No throughput promise
or compaction proof is made. Opening the original 4096-byte
schema upgrades it transactionally while preserving its exact existing BLOB.
The database filename remains `forward-link.sqlite3` to preserve old clients.

The lifecycle tests exercise rollback after process exit before commit, exact
cold-start reopening after commit, idempotent retry, conflicting concurrent
publication and replacement, malformed/torn database rejection, old-schema
migration, and the image-size bound. Run the joined narrow check from the repo:

```sh
bash scripts/probe-durable-receiver.sh
```

That command runs native tests in release mode and the actual Lean codec,
executor, SQLite CAS, and reopen path together. The joined fixtures cover two
cell writes, repeated commits, old-id retry, payload conflict, stale read/write,
nullifier reuse, metering refusal, lost responses, and a concurrent read-guard
change between preparation and CAS. Fixtures test durable intent settlement;
they do not impersonate controller-authorized resource births.

These observations do not prove SQLite, its C ABI, Rust FFI, host locks,
filesystem ordering, `fsync`, stable media, power-loss behavior, or hostile
directory mutation. Those refinements remain explicit on the Lean side.

On minimal Linux workers that provide `libsqlite3.so.0` without the usual
development symlink, `build.rs` creates a private linker alias in `OUT_DIR`.
It does not bundle or modify SQLite, and the resulting binary still records
the system runtime library's versioned SONAME.
