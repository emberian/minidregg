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
