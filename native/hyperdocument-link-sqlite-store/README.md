# SQLite Hyperdocument link byte store

This dependency-free Rust crate is an opaque, fallible transport for the exact
bounded byte record owned by
`Assurance.HyperdocumentLinkSqliteTransactionalStore`. It stores a single BLOB
through SQLite's rollback-journal transaction boundary and deliberately does
not parse or assign semantics to links, authorization, receipts, roots, or
replay data.

The lifecycle tests exercise rollback after process exit before commit, exact
cold-start reopening after commit, idempotent retry, conflicting concurrent
publication, malformed or torn database rejection, and the record-size bound.
These observations do not prove SQLite, its C ABI, Rust FFI, host locks,
filesystem ordering, `fsync`, stable media, power-loss behavior, or hostile
directory mutation. Those refinements remain explicit on the Lean side.
