# Shared discovery in one admitted observation

The current joined five-member journey exposed a whole-action cost: on the sealed d54cefc2 family, creating the workroom took 161.799 seconds, listing references 22.244 seconds, and the first two shared-name resolutions 5.659 and 5.688 seconds. These are observed journey wall times, not an allocation of CPU to one function.

The client separately queried the invoked capability and its narrowed resource for each discovery target. Resolving one room name therefore required four signed observation handshakes: scope and resource for both the room and its index. Reference listing repeated that pair for every alias in the same room.

## Contract and implementation

The additive `resource-scope` query uses the ordinary authenticated observation receiver and one current resource-local admission. Its reply contains only the invoked grant's kind, identifier and field coverage alongside the already narrowed resource. Both projections come from the same admitted authority/resource context. It does not introduce a client-supplied scope, another authority database, or an authority cache across actions. The client still verifies the narrowed resource's salted root opening before using the reply.

Existing query-view tags 0/1 and resource-view bytes are unchanged. The new query-view tag is 2, with a separate `RESOURCE-SCOPE-VIEW/v1` result frame. Byte and codec lemmas retain the old resource/capability observations needed by saved preparation and exact recovery.

`shared_names::discovery_read` now performs one signed handshake per target. `refs` retains admitted discovery reads only while assembling that one listing, keyed by room discovery chain, kind, target, invoked capability and required field. Room/index reads within each chain must share a world root/height; independent rooms may resolve at different heads. Repeated aliases reuse their chain's immutable request snapshot. Any later target read or write still meets its own current admission and shared-name snapshot binding.

Observation admission also consumes its already resolved `PreparedLaw.admit` through the existing complete-result equality theorem. The original refusal, evidence, current-source and axiom-guard statements remain unchanged.

## Qualification

Rust shared-name tests cover explicit full/narrowed coverage, wrong grant identity, missing scope metadata, moved snapshots, revoked discovery, request-local reuse, independent room chains with different heads, authenticated absence and exact retained recovery. Lean qualification covers additive query bytes, scope-view codec roundtrip, same-admitted-grant projection and the existing observation admission proofs.

Controlled native receiving and useful latency savings still require the new source-qualified Host/client family on the supplied joined Store, with the owner coordinating restart. A copied Store benchmark cannot discharge that joined-world receiving obligation. Before/after checks should use a few shared-name resolutions and one reference listing, count actual query handshakes, and retain wall/Host CPU timing and concurrent-load caveats.
