# Native compute and proof construction plan

Status: 2026-08-10. [`PROJECT.md`](../PROJECT.md) is the design constitution and
[`GOAL.md`](../GOAL.md) is the evidence ledger. This file tracks the proof-controller/native
boundary and the ordered joins to one honest proof system.

## Maturity labels

- **S** semantic/formal theorem
- **A** Lean-owned controller/admission
- **P** concrete cryptographic reduction/game
- **D** deployed artifact/handler/consumer path
- **B** reproducible matched benchmark

## Authority rule

Rust has no semantics in this project. Lean owns:

- typed requests, authorization, effects, state transition, disclosure, and receipt meaning;
- proof statements, carrier/codec/bridge identity, and manifest clauses;
- phase order, roots-before-challenges, transcript draws, and queries;
- decoding, expected-root/result equality, proof checks, and failure ledgers; and
- the only accepted-turn, release, clause, and history constructors.

Native code receives generated identity plus bounded bytes and returns bytes or an opaque error.
An error blocks. No conformance result or authenticated catalog transfers semantic authority.

## Exact native surface

| Surface | Current role | Boundary |
|---|---|---|
| `babybear`, `field6` | opaque scalar/Ext6 arithmetic | no correspondence theorem |
| `binary_tower`, `binary_tower_256` | opaque Fan–Paar arithmetic/encoding | Lean codec exact; Rust limbs unproved |
| `additive_ntt` | caller-selected additive transforms | no protocol schedule |
| `mle_kernels` | generic transform/fold/dot operations | candidate compute only |
| `tower256_kernels` | generic vector/equality/MLE/rational-pair work | no LogUp statement or verdict |
| `hash_kernels` | raw customized cSHAKE XOF | Lean owns framing/domain/output width |
| generated `semantic_artifact_v1` | authenticated constants, DTOs, catalog dispatch | transport identity, not compute correctness |

Deleted authority islands include the reference prover/verifier, receipt/history mirrors, sampled
FRI/OOD admission, native transcript machines, Ext6 proof composition, LogUp proof/verifier,
descriptor satisfaction, and WGPU fold path.

## Authenticated artifact and live work

The canonical artifact authenticates its manifest, native ABI codec registry, and native work
catalog. The generator takes no parallel catalog argument. Base V1 exposes:

| Work | ID | Carrier | Request codec | Response codec |
|---|---:|---:|---:|---:|
| Tower256 dot product | `9101` | `205` | `9001` | `21` |

Generated Rust dispatch derives solely from that catalog. Standalone JSON and embedded payload are
byte-identical. The clause-406 deployment extension additionally authenticates BabyBear add-1 work
`9102`, request codec `9003`, response codec `9005`, and a 144-byte/36-canonical-word candidate
response. Rust execution remains opaque/fallible and returns bytes/error.

## Lean-owned controller table

| Path | S | A | P | D | B | Exact residual |
|---|---|---|---|---|---|---|
| derived AIR / clause 406 | executor/circuit equality, degree-2 flattening, faithful descriptor | deterministic descriptor controller and Lean decoding/checking of generated candidate bytes | proof-system security not joined | work `9102` deployed through exact artifact/controller/native-catalog join | none | Rust remains opaque; no proof suite/security; broaden beyond one add-1 descriptor |
| Tower256 additive FRI | exact tower/Fan–Paar codec, additive proximity and ideal clause | exact cSHAKE/Merkle transcript, arbitrary bytes/error decoding, openings/folds/final polynomial, one controller coin | literal ideal coin/event, exact UD price, and Lean-derived false-accept cover; transport/CR still conditional | absent from base/deployment | none end-to-end | exact cSHAKE→uniform-ROM transport; raw non-binding Merkle/PCS plus adaptive collision→PositionBinding/CR; proximity; codecs/IDs; executable checker |
| Tower256 indexed LogUp 404 | canonical addresses, exact incidence/indexed evaluation | extension-local exactly-two-reply controller; failures block | conditional only | absent from base/deployment | none | PCS/sampled decider, binding/CR/ROM, mutable RAM, catalog profile, history common game |
| Ext6 gate proof | exact seven-operand descriptor algebra and eta relation | canonical prefix-decodable statement preimage, codecs/cSHAKE transcript, full algebraic checker | eight-event conditional ledger separates challenge sampling from ROM and is registered in the global extensible ledger | absent from base/deployment | none | PCS, subfield, proximity, binding, ROM, sampling-bias price, final LDT, concrete reductions, recursion |
| BFV 901 | pure sealed core and all 384 exact equations | parameterized local buffer recheck only | none | reserved; suite/controller pins zero | none | concrete codecs/digests/patch, controller, confidentiality/knowledge, PCS/CR/ROM, history |
| sealed note spend | exact accepted-core statement and relation | byte/error controller derives statement and challenge in Lean; suite remains `0` | reduction laws only; hiding is a separate failure class with no construction | absent from deployment | none | assign proof suite; concrete PCS/CR/ROM/PoK and hiding; native proof path |
| semantic history | exact retained entries, folding, extraction, BCS reconstruction | exact-head admission; literal retained-history FS failure event; one history/Tower256 `Omega`, ledger, root/schedule join, and four-event bound | actual same-coin event; concrete `PcsCrRomReduction.classify`, uniform realization, MCA/codeExact remain premises | no succinct deployed checkpoint | none | instantiate classifier and concrete PCS/CR/ROM, MCA/codeExact, hiding/sub-UD |

## Ordered construction

### 1. Instantiate the remaining common additive/history reductions

`SemanticHistoryTower256CheckpointGame` puts the landed additive controller and retained-history
BCS boundary on one explicit `Omega`, one existing ledger, exact terminal/initial root and schedule
equalities, and one four-event union bound without independence. The history event is now the
literal retained-history Fiat--Shamir verifier/knowledge failure, not an external proxy. The
additive event and UD price are likewise literal and its false-accept cover is Lean-derived.

Instantiate the remaining protocol seams: exact cSHAKE-to-uniform-ROM transport and a raw
non-binding Merkle/PCS interface whose adaptive framed-XOF collision reduction derives
PositionBinding/CR on the additive side; concrete `PcsCrRomReduction.classify`, common-coin
realization, MCA, code exactness, and hiding on the history side. The structural common game is
**S/A**; these instantiations are the hard **P** step.

### 2. Complete proof/container transport

Define versioned proof, container, domain, level, and query codecs/IDs for Tower256 additive and
lookup. Authenticate their work profiles in the artifact. Emit an executable Lean-owned checker
boundary rather than depending on a noncomputable reflected Tower relation.

### 3. Promote lookup honestly

The clause-404 byte controller fixes dispatch identity only. Add concrete PCS openings, sampled
decider, binding/CR/ROM, mutable-state semantics, common-game history evidence, and a deployment
controller entry before it may leave the gated registry.

### 4. Complete Ext6

Instantiate gate PCS, base-subfield provenance, coherent proximity, binding/ROM, final LDT, and the
concrete reduction laws inside the already-landed global extensible failure ledger. Only then
consider recursion or a 137-bit deployment label.

### 5. Complete sealed BFV, then disclosure

Bind the pure core to concrete versioned codecs, digests, patch adapter, proof suite, and controller.
Prove the cryptographic relation at its ring-native boundary. Disclosure or threshold release is a
later separately authorized causal effect linked to the output commitment.

### 6. Join deployment and consumers

`ComposableDeploymentManifest` prevents gated/reserved clauses from projecting into deployment.
Clause 406 is the narrow positive example: authenticated work `9102` returns error or exactly 144
candidate bytes; Lean decodes 36 canonical BabyBear words and alone checks the descriptor. Clause
404 remains gated and BFV 901 reserved. Add further controller/artifact entries only at their honest
maturity, then migrate one token, reactive agent, Grains history, private-compute, cloud-control,
and hypermedia path through the canonical event and durable handler.

## Performance discipline

Source `54295c6`, evidence `4d1f290` measures only generated dispatch around work 9101. Direct and
generated results are byte-identical; dispatch/direct ratios across lengths 1–16384 are
`0.985–1.040` on hbox and `0.985–1.025` on persvati. No threshold or semantic conclusion is drawn.

The integrated hbox archive `E-20260810T003037-13290-hbox-3f74f634e0e1-lake` built source
`3f74f63` with 8729 jobs, command exit 0, and source-integrity exit 0. Persvati replay is pending
because local Tailscale reports `NeedsLogin`. This is build integration evidence, not a benchmark or
semantic/security result.

The next **B** evidence must measure an admitted end-to-end path: proof size, prover/verifier time,
memory, checkpoint cadence, tail latency, and dense/sparse crossover. Historical deleted-prover and
WGPU numbers remain archived baselines only.
