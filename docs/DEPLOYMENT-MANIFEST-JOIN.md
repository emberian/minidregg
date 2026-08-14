# Deployment manifest/controller join

This note audits the current deployment surface behind
`Compiler.ComposableDeploymentManifest`. It distinguishes structural registry
closure from executable implementation and from cryptographic admission.

## The rule

A `Manifest.WellFormed` value proves unique identifiers and closed references
for codecs, carriers, bridges, and clauses. It does **not** prove that any
controller exists, that a proof suite is implemented, or that native code has
semantics.

An admitted deployment therefore contains four objects joined in Lean:

1. the exact `ArtifactBundle` and its manifest;
2. a `Manifest.WellFormed` proof;
3. a `NativeCatalogWellFormed` proof for the artifact-authenticated native ABI
   codecs and work profiles;
4. a `DialectClauseDispatch.ControllerRegistry.WellFormed` proof for an actual
   list of `ControllerEntry` values.

`ImplementedControllerPack` has no caller-authored clause list. Its manifest
clauses are projected from its controller entries. Packs append their semantic
vocabulary, native-ABI codecs, native work catalog, and controller entries; the
combined manifest, work ID, ABI codec ID, and controller-key uniqueness proofs
reject collisions. Security-gated and reserved candidates are catalog data
only and have no projection into the deployed manifest.

## Current maturity

| Clause/component | Status | Exact evidence | What remains |
|---|---|---|---|
| Base Minidregg V1 | vocabulary only | `MinidreggV1Artifact.manifest_wellFormed`; its dialect list is empty | Add only clauses with actual controller entries and exact semantic/history adapters |
| `406` BabyBear arithmetic work | implemented deterministic controller | `arithmeticController` issues the fixed Lean-selected instruction and returns either rejection or a `CertifiedResponse`; `arithmeticRegistry_wellFormed` joins it to the exact extended artifact | This is the descriptor relation for one arithmetic work item, not a general proof system, semantic-turn receipt, hash/transform kernel, or native refinement theorem. The current authenticated native catalog has no 406 byte-transport work profile, so the controller remains typed Lean control rather than emitted Rust glue |
| `404` Tower256 indexed LogUp | security-premise-gated; not admitted | canonical Tower256 codec; byte decode/recheck boundary; exact controller schedule and verified-run reduction; one shared `Tower256ConcreteBackend` with stable hash/codec/suite pins and concrete Lean cSHAKE; `Tower256LogupControllerAdmission` retains the common-game security premises | Exact dispatch entry and input/reply codecs using that backend; native byte admission throughout the plan; table and checkpoint position binding; PCS opening plus sampled decider; commitment binding/CR; cSHAKE ROM transport; common-game budget; history root-evidence adapter |
| `901` BFV | reserved | Lean checks every returned arithmetic row and the local buffer admission binds a nonzero controller identifier | The portable clause still has an unclosed carrier/statement reservation and zero proof-codec, proof-suite, and controller sentinels. The local admission variant still has an unassigned proof suite and does not establish privacy, knowledge soundness, or a deployed proof system |
| cSHAKE256 | implemented deterministic computation, not a dialect | `Sp800185Cshake256` computes Keccak-f[1600]/SP 800-185 framing and checks exact 32-byte replies; `Tower256ConcreteBackend` fixes algorithm `8400`, codec pins `8401`--`8404`, suite `8600`, and readable separated domains | `Manifest` still has no generic hash-service registry. Clause 404 must bind the shared backend through its exact controller entry. Collision resistance and ROM transport remain security premises |
| Merkle binding | deterministic reduction landed; security boundary open | The Tower256 controller fixes exact-depth paths and recomputation; `Tower256CshakeMerkleBinding` reduces unequal accepted openings to an exact framed cSHAKE/XOF collision event | Do not claim a deployed commitment until the shared backend/domain pins, position binding, collision-resistance probability price, and common-game join are all attached to the exact clause controller |
| Native kernel plans | implemented opaque-compute boundary | `NativeKernelPlan.arbitraryRunner_integrity`: arbitrary fallible runners return bounded data; Lean alone checks registration, shape, public prefix, and descriptor acceptance | Each work item still needs a semantic controller entry and an exact relation/receipt projection; `WorkKind` labels add no semantics |
| Semantic history | implemented semantic fold, consumer-gated | `SemanticHistoryAccumulator` consumes the same manifest and resolved controller registry and retains proof-relevant turns/fold traces | Registry closure is not clause evidence. Each statement/proof-root pair needs a `ClauseEvidenceFamily` adapter; deployed header hashing, code membership, PCS/BCS, ROM/binding, recursion, and privacy remain separate named boundaries. ⛑ Proximity is NOT one of them for the characteristic-two path: `additiveProximityGap_UD` proves the additive gap unconditionally on δ < (1−ρ)/3. The Ext6/BabyBear and Johnson-regime proximity residuals are the ones still open, and they should be named as such rather than as a bare "proximity" |

## Why clause 404 is not in base V1

The local LogUp manifest proves that clause 404's carrier and codecs resolve.
That is useful shape evidence, but it is not an implementation theorem. The
accepted-run theorem is parameterized by an exact controller execution, and
the admission theorem deliberately retains PCS, binding, position-binding,
and ROM judgments from one common security game. Until a deployment packages
those conditions with a concrete dispatch controller and history evidence,
adding 404 to base V1 would turn a reservation into an apparent runtime claim.

The machine-checked negative teeth are:

- `tower256Logup_absent_from_base`;
- `tower256Logup_absent_from_deployment`;
- `candidate_projection_exact`, which projects only clause 406 from the mixed
  implemented/gated/reserved catalog.

## Next deployment closures

1. Use the landed shared Tower256/cSHAKE/Merkle backend pins to build the exact
   clause-404 dispatch entry—without copying backend constants.
2. Join the landed Merkle collision reduction and its priced common-game
   premises to that entry.
3. Define clause-404 statement/reply codecs and its exact
   `ClauseEvidenceFamily` history adapter.
4. Only then construct a pack containing 404 and prove the combined manifest
   and controller registry collision-free.
5. Give BFV nonzero proof-codec/proof-suite pins and a real privacy/knowledge
   proof boundary before moving it from `reserved`.
