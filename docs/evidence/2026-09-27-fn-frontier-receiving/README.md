# Selected fn frontier receiving: source cut

This cut adds verifier-backed Mini event17 selected-poll coverage and event19
empty-poll progress submission and receipt-only lookup (native operations
60–63). Private operation 64 asks the configured, pinned fn service to poll and
returns a source-authored plan retaining the exact cursor, report, and source.
Private operation 65 re-polls, checks the whole plan against current Mini
history and authority, then assembles a raw 64-byte gateway signature into
canonical event17 or event19 ingress. The source-owned CLI encodes the op64
request and exports the exact retained plan artifacts; Rust does not encode
either Lean codec.

The separate Rust custody flow keeps its plan and poll artifacts in an
owner-private directory, requires an approval matching the exact plan and
gateway public key, and signs only the source-issued credential header. It
persists a submit marker before one op60 or op62 attempt. After that marker,
reentry uses only op61 or op63 exact-original receipt lookup. An absent lookup
does not authorize an automatic resubmit. ACK is a separate Host action:
selected ACK requires the admitted event13 release and event17 coverage;
empty-page ACK requires admitted event19 progress. Both use the configured fn
service and a fresh, private cursor from a repeated local poll.

The read-only r3 recipient inspection found the intended `selected-mini-gateway`
consumer at ACK 0 and frontier 2 on the second fn node. It is distinct from the
earlier `selected-mini` consumer on the first node. Neither namespace was
reset, posted to, or ACKed by this cut. The next local poll may advance over
neutral records within fn's bounded 16-record first-match scan; the Mini
coverage record makes that observation durable. It is local testimony from a
qualified fn poll, not a proof of remote completeness.

Validation so far is source-only: `cargo fmt --check`, the five focused
`fn_frontier::tests` through nextest, and `cargo clippy --all-targets -- -D
warnings` pass in `native/resource-client`. A broad local Lake attempt stopped
before these new modules on an unrelated stale CanonicalPolicyRegistry closure;
it establishes no Lean verdict. The exact 9746 Host build also stopped at that
baseline proof, and its repair belongs to build_native. Do not invoke native
event14 publication, op60–65, POST, or ACK against an older Host image. Serial
source-matched Lean qualification and a linked native acceptance fixture remain
required after the repaired Host snapshot is available.

The Rust cut was tightened after review: Host-generated artifacts are restricted
and synced before a durable pin, Host/config/request/plan/poll artifact pins are
checked again after external operations, and receipt decimals reject leading
zeroes. The final focused nextest run has five passing tests, including changed
Host/config refusal and marker-driven lookup-only recovery. Exact Rust source
and log hashes are in `RUST-SOURCE-MANIFEST.txt`; the empty fmt log represents a
successful command with no diagnostics. The pre-existing untracked upper
`FnSelectedPollAdmission`, `FnSelectedPollReleaseLink`, and
`FnEmptyPollAdmissionV2` modules are dependencies owned by a separate lane;
their source-matched Lean verdict must be included in the eventual native
closure before this cut can be called qualified.
