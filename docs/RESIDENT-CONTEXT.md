# Resident source context and current-base review

Context is selected from current participant-authorized signed document reads.
It is not a second history store. The original document atoms and source roots
remain the identities behind citations, summaries, and subsequent review.

## Source contract

`mini-context-document-v1` includes source/sourceRoot, ordered atom rows with
revision, parent, predecessor and payload digest, whole-row selection limits,
coverage counts, and authenticated opening availability. The Lean selector
uses actual document order. The client obtains the signed read and opens
private values only with existing participant authority.

`mini-context-summary-v1` is ordinary authored JSON containing text and support
references with exact source/root pins. Each new inference checks those
references with current signed reads. Revocation, rebinding, or source change
invalidates the summary's inference text. Its historical bytes remain data.

`mini-context-bundle-v1` retains full dependency pins. Display height and
read-authority provenance are excluded from the semantic fingerprint; actual
source roots, revisions, placement and support remain included. Briefing can
omit whole oversized text, with explicit coverage, rather than rewriting it.

Already-started requests retain their exact selected context and original
dispatch/custody identity. New preparations read current source. The existing
native request recovery path remains responsible for exactly-once completion.

## Review and landing

`doc context NAME [MAX-ROWS MAX-BYTES]` returns the current document projection.
`doc review ID @CONTEXT @REQUEST` prepares an ordinary proposal against that
bundle. Every write target must be selected; all other cited sources become
native read guards in the same atomic command. Rebound references and
inconsistent pins refuse. Summary support is flattened into read dependencies.

Proposal authoring and storage do not land effects. Existing explicit
submit/approve, current authority, expected roots and exact recovery apply.
External model output is authored prose or a proposal, never proof of truth.

## Qualification at the first source shipment (2026-10-03)

ResidentContextProjection passed scoped Lean compilation with named axiom
gates. Rust resident_context and context_projection each passed three narrow
nextest tests. Those tests cover fingerprint dependencies, schema/brief
handling, and review guards; they do not establish live recovery behavior.

ResidentActivityRevision now passes scoped Lean compilation and named axiom
gates after codec namespace and identity-proof repairs. It models same-author signed append revisions
with exact predecessor revision and stable origin identity, but is not yet
connected to a native stream consumer. Cross-room transfer is not supplied.
Host/ResidentContextInspection also passes its scoped Lean check. These
module checks do not constitute a rebuilt native host or a live receiving run.

The new resident-context-review.py receiving journey is authored and syntax
checked, but has not run against a matched host/participant artifact. No
general Bend-authored selector/lowerer or activity-edit consumer is claimed.
Whole-source-root invalidation is conservative; unrelated changes in the same
cell can invalidate a summary. Embeds/opaque/unavailable rows have explicit
coverage limits. These are honest integration boundaries, not permissions to
use controller journals, ambient host observations, or a shadow memory store.

## Explicit resident reviewed document action

The additive `mini_doc_review` tool accepts only a selected context bundle and
ordinary document targets/actions. The controller chooses the operation and
proposal identities. Selected input files in existing HOME/requests are
immutable per operation; different bytes or symlinks refuse. The existing room
Attempt is retained before the write boundary, and normal hr-operation
proposal/call.bin custody and exact lookup apply. No fleet record or parallel
proposal store is introduced.

Current pinned source reads determine reviewed line coordinates, atom records
and native payload preimages. An earlier editor seen cache does not retarget
this explicit path. All selected support roots join normal preparation and
native landing guards; current laws and participant grants still decide.
Ordinary `mini_doc_append` retains its separate single-document contract.
The new action is authored WIP at this shipment and awaits scoped Rust/native
receiving checks.

## Observation custody pins

Document context now includes the actual selected `readCapability`.
Authored summary support records include `capability` as well as name,
source and root. Missing legacy custody pins or a rebound/revoked observe
capability suppress derived inference text. Source/root equality alone cannot
justify reusing context after a local reference changes its read authority.

Reviewed preparation carries `expectedObserveCapability` alongside source-root
pins. The ordinary preparer compares this at the exact resolved signed-read
reference and retains that capability in its native admission plan. These
identifiers are current-authority dependencies, not caller credentials or
proof that authored prose is true. Current native grant/policy checks remain
necessary at submission. This repair is WIP pending scoped Rust/native checks.

The receiving journey now explicitly submits every named append/edit proposal;
those shell commands prepare only. Birth/move retain their existing native
boundaries. Preparing a proposal is never reported as installing its effects.
