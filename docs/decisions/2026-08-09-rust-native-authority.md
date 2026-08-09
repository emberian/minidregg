# Rust native authority boundary

- Status: accepted
- Date: 2026-08-09
- Updated through: authenticated native catalog `226b7af`, benchmark evidence `4d1f290`

## Decision

Lean is the only source of statements, semantic relations, protocol schedules, security profiles,
and acceptance. Rust has no operational semantics in this repository, so it is neither a second
implementation nor a refinement target.

Rust may contain:

1. mechanically generated artifact constants, DTOs, identifiers, and bytes/error dispatch; and
2. handwritten opaque arithmetic, transform, hash, or MLE candidate computation selected by a
   Lean-owned plan.

A successful native call returns bytes. An error blocks. Neither branch constructs semantic
evidence or an acceptance token.

## Hard invariants

- Native success returns candidate bytes/buffers, never a verdict.
- Native failure may affect availability or completeness only.
- Rust does not parse the authoritative semantic request, construct a receipt/history entry, draw
  protocol challenges, or choose a proof relation.
- Protocol-shaped work requires exact Lean-selected identity, codecs, bounds, and output checking.
- Cross-language vectors and benchmarks are diagnostic evidence, not semantics or refinement.
- Artifact authentication proves which transport/control data was declared; it does not prove the
  native computation correct.

## Authenticated generated surface

The canonical `ArtifactBundle` encoding, content address, JSON, and generated Rust now authenticate
separate `nativeAbiCodecs` and `nativeWorkCatalog` fields. V1 proves:

- native work IDs and ABI codec IDs are unique;
- native ABI codecs are disjoint from semantic manifest codecs;
- the exact work carrier and request/response codecs are closed; and
- the generator consumes only the catalog already contained in the authenticated bundle.

The current catalog contains one work:

| Work | ID | Carrier | Request codec | Response codec | Meaning of closure |
|---|---:|---:|---:|---:|---|
| Tower256 dot product | `9101` | `205` | native ABI `9001` | semantic codec `21` | generated identity/transport selection only |

Standalone JSON and the Rust embedded payload are byte-identical. Generated Rust constants and
dispatch are derived solely from `wire.nativeWorkCatalog`; there is no parallel handwritten work
catalog argument.

## Handwritten opaque compute surface

Current native source is limited to:

- `babybear` and `field6` arithmetic;
- `binary_tower` and `binary_tower_256` arithmetic/encoding;
- `additive_ntt` caller-parameterized transforms;
- `mle_kernels` generic transforms, folds, and dot products;
- `tower256_kernels` generic vector/equality/MLE/rational-pair operations;
- `hash_kernels` raw caller-customized cSHAKE XOF; and
- generated `semantic_artifact_v1` DTO/dispatch data.

The Lean Tower codec, cSHAKE framing, and controller plans are exact formal objects. That does not
prove Rust four-limb, polynomial, transform-order, or raw-XOF correspondence. Those conventions
remain untrusted candidate compute unless the Lean controller decodes or rechecks the exact reply.

## Deleted authority islands

The following are intentionally absent: one-call reference prover/verifier, semantic receipt and
history mirrors, sampled additive-FRI/OOD admission, Rust transcript machines, Ext6 proof/verifier
composition, Tower256 LogUp protocol messages/verifier, descriptor satisfaction, and WGPU FRI.
They must not be reintroduced as handwritten parallel protocol profiles.

## Current controller examples

- The additive-FRI controller accepts arbitrary native bytes/error only after Lean decoding,
  transcript derivation, opening/fold/final-polynomial checks.
- The extension-only clause-404 controller accepts exactly two keyed byte replies and blocks wrong,
  duplicate, or missing reply tables before the existing Lean plan may verify.
- The Ext6 controller fixes descriptor bytes, codecs, cSHAKE challenges, transcript order, and the
  algebraic verifier relation; its PCS/security reductions remain explicit.

These are admission/control results, not Rust correctness theorems.

## Performance evidence boundary

At source `54295c6` with evidence `4d1f290`, generated dispatch for work `9101` produced bytes
identical to direct execution. Dispatch/direct timing ratios for vector lengths 1–16384 were
`0.985–1.040` on hbox and `0.985–1.025` on persvati. This is a narrow empirical dispatch result:
no threshold, semantics, security, or full-prover performance claim follows.

## Rejected alternatives

- Keeping protocol-named helpers because challenges are caller-supplied: the helper can still
  author the relation and message shape.
- Calling vector agreement a formal refinement: no Rust semantics exists here.
- Giving generated dispatch an acceptance Boolean: transport identity is not semantic authority.
- Deleting every native kernel: opaque replaceable compute remains useful after Lean selects and
  checks its bounded work.

## Invalidation trigger

This decision changes only if the project adopts and proves an authoritative operational semantics
for the native language and a cross-language theorem. A more complete generated ABI or stronger
conformance suite does not by itself change the authority boundary.
