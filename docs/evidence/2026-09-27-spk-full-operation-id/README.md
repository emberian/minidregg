# Full-width native lifecycle operation identity

Mini derives v3 BEGIN `authorizationOperationId` as the Nat value of a
cSHAKE256 digest of the normalized launch preimage. The physical `VerifiedBegin`
journal now retains that exact canonical decimal string. It no longer parses
the identity as `u64` or maps it to a smaller surrogate. App and generation
remain bounded by the actual Linux unit naming range.

Historical v1 journal records that serialized the operation ID as an unsigned
JSON number still read as the same decimal identity. New records serialize it
as a string; aliases such as `"07"` are refused. The test writes and reopens a
full 256-bit-sized ID and reads a historical numeric record. The isolated
hbox run passed 9/9 focused tests and strict all-targets Clippy, within a
two-job, 4 GiB scope. No Mini Store or physical unit was used.
