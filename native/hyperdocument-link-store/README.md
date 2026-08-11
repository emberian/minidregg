# Bounded Hyperdocument link byte store

This crate is a deployment-shaped but deliberately non-authoritative local
filesystem transport for one recovery byte stream.

The Lean module
`Assurance.HyperdocumentLinkLocalFileStore` authors the exact 14-byte fixture,
proves it is the concrete guarded link recovery stream, and proves that the
endpoint accepts only after Lean decoding and replay. The native program never
parses a link, intent, authorization, checksum, or response. Its callable read
boundary returns raw bytes or an error.

The store admits at most 4096 bytes, stages through a fixed filename, syncs the
staging file, installs a second fixed filename with a no-overwrite hard link,
requests directory sync, and rejects a different retry. Tests exercise separate
process invocations for stage/crash, publish/lost-response, restart/read, exact
retry, conflict, corruption transport, and oversize rejection.

These tests establish observed conformance on the tested filesystem. They do
not prove Rust semantics, POSIX contracts, `sync_all` durability, hard-link
atomicity, stable media, power-loss survival, or safety against an adversary
mutating the store directory concurrently.

`forward-link-e2e-bench` exercises the same `LocalLinkStore` through a fresh
child process for each lifecycle stage. It records raw and nearest-rank
p50/p95/p99 timings for stage, no-overwrite install with its response ignored,
restart/read, exact retry, reopen/read, and the complete process lifecycle.
Every sample uses a fresh directory; warmups precede measured samples, but the
OS filesystem cache is uncontrolled. The benchmark reports no per-stage memory
number because child-process peak RSS cannot be attributed reliably with this
dependency-free harness.
