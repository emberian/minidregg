/-
# Compiler.MinidreggV1ArithmeticWork -- first concrete Lean-owned native work join

This module binds one generated arithmetic request to a local extension of the
v1 semantic artifact: a BabyBear arithmetic clause, the `addKernelCall 1 1`
descriptor and layout, and the arithmetic dispatch branch are all selected by
Lean declarations.  The base v1 dialect pins are not treated as implemented
controllers.  The native
boundary is opaque and fallible.  It returns either an error or the descriptor's
bounded `KernelResponse`; it cannot return a certificate or an acceptance bit.

On a native error, evaluation stops before `checkInstruction`.  On a buffer,
Lean runs the existing executable checker, and only its successful branch carries
the existing `CertifiedResponse`.  The native-failure and honest-certificate
theorems therefore assume no native semantics or refinement theorem; generic
arbitrary-runner integrity remains owned by `NativeKernelPlan`.

Two current boundaries are deliberately exposed rather than papered over:

* `DialectClauseDecl` has no `WorkKind` field.  This module pins arithmetic in
  its Lean work declaration, but manifest lookup alone cannot recover that pin.
* `KernelCall` currently schemas only constraint-descriptor witness calls
  (`add` and `scalarMulConst`).  This join emits arithmetic only; it does not
  treat the otherwise available `hash` and `transform` labels as implemented.
-/
import Compiler.MinidreggV1Artifact
import Compiler.NativeKernelPlan

namespace Minidregg.Compiler.MinidreggV1ArithmeticWork

open Minidregg.Compiler.BignumKernelABI
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.SemanticArtifactBundle
open Minidregg.Compiler.SemanticManifest
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## Lean-owned declaration and artifact surface -/

/-- A local degree-one BabyBear carrier for the descriptor relation.  This is a
manifest profile, not a claim about any native representation. -/
def babyBearArithmeticCarrier : CarrierProfile :=
  .residueRing (MinidreggV1Artifact.id 206) 1
    Minidregg.Compiler.babyBearP [Minidregg.Compiler.babyBearP]
    (MinidreggV1Artifact.id 221) (MinidreggV1Artifact.id 222)

/-- The local clause identifier is distinct from the historical base v1 pins
(401--403), the LogUp extension (404), and the additive checkpoint extension
(405).  Its low-level work acceptance is
checked below by the existing Lean `KernelCall.Accepts` relation; the numeric
fields are content pins, not native semantics. -/
def arithmeticClause : DialectClauseDecl where
  clauseId := MinidreggV1Artifact.id 406
  relationId := MinidreggV1Artifact.id 416
  carrierProfileId := babyBearArithmeticCarrier.id
  statementCodecId := MinidreggV1Artifact.dialectStatementCodec.codecId
  proofCodecId := MinidreggV1Artifact.dialectProofCodec.codecId
  proofSuiteId := MinidreggV1Artifact.id 426
  verifierControllerDigest := MinidreggV1Artifact.manifest.transcriptControllerDigest
  requiredBridgeIds := []

/-- The first concrete native operation is the smallest nontrivial generated
addition: one 1-bit limb. -/
def arithmeticCall : KernelCall := addKernelCall 1 1

/-- Closed Lean declaration tying the clause, work kind, call, and public layout
together.  This is the missing pin that `DialectClauseDecl` cannot express by
itself. -/
structure ArithmeticControllerDeclaration where
  clause : DialectClauseDecl
  kind : WorkKind
  call : KernelCall
  publicInputs : List BabyBear

def controllerDeclaration : ArithmeticControllerDeclaration where
  clause := arithmeticClause
  kind := .arithmetic
  call := arithmeticCall
  publicInputs := []

/-- Projection of the authoritative Lean declaration into the existing plan
instruction type. -/
def arithmeticInstruction : Instruction :=
  { kind := controllerDeclaration.kind
    clauseId := controllerDeclaration.clause.clauseId
    call := controllerDeclaration.call
    publicInputs := controllerDeclaration.publicInputs }

/-- Local manifest extension.  The base profile registries are reused, while
the concrete BabyBear carrier and arithmetic work clause are appended.
No shared v1 registry is mutated. -/
def manifest : Manifest :=
  { MinidreggV1Artifact.manifest with
    carriers := MinidreggV1Artifact.manifest.carriers ++
      [babyBearArithmeticCarrier]
    dialectClauses := MinidreggV1Artifact.manifest.dialectClauses ++
      [arithmeticClause] }

private theorem find?_append_of_some {α : Type} (test : α → Bool)
    {items suffix : List α} {value : α}
    (found : items.find? test = some value) :
    (items ++ suffix).find? test = some value := by
  have characterized := (List.find?_eq_some_iff_append).mp found
  apply (List.find?_eq_some_iff_append).mpr
  refine ⟨characterized.1, ?_⟩
  rcases characterized.2 with ⟨before, after, split, misses⟩
  exact ⟨before, after ++ suffix, by simp [split], misses⟩

private theorem base_lookupCarrier_preserved {profileId}
    {profile : CarrierProfile}
    (found : MinidreggV1Artifact.manifest.lookupCarrier profileId =
      some profile) :
    manifest.lookupCarrier profileId = some profile := by
  exact find?_append_of_some _ found

/-- The local extension preserves all base registry invariants and closes the
new clause against its new BabyBear carrier and the existing dialect codecs. -/
theorem manifest_wellFormed : manifest.WellFormed where
  codecIdsUnique := MinidreggV1Artifact.manifest_wellFormed.codecIdsUnique
  carrierIdsUnique := by
    apply MinidreggV1Artifact.manifest_wellFormed.carrierIdsUnique.append
    · simp
    · rw [List.disjoint_left]
      intro profileId old fresh
      simp only [List.mem_cons, List.map_nil, List.not_mem_nil, or_false] at fresh
      subst profileId
      exact (by decide : babyBearArithmeticCarrier.id ∉
        MinidreggV1Artifact.manifest.carriers.map CarrierProfile.id) old
  bridgeIdsUnique := MinidreggV1Artifact.manifest_wellFormed.bridgeIdsUnique
  dialectClauseIdsUnique := by
    apply MinidreggV1Artifact.manifest_wellFormed.dialectClauseIdsUnique.append
    · simp
    · rw [List.disjoint_left]
      intro clauseId old fresh
      simp only [List.mem_cons, List.map_nil, List.not_mem_nil, or_false] at fresh
      subst clauseId
      exact (by decide : arithmeticClause.clauseId ∉
        MinidreggV1Artifact.manifest.dialectClauses.map
          DialectClauseDecl.clauseId) old
  receiptCodecClosed := by
    simpa [manifest, Manifest.lookupCodec] using
      MinidreggV1Artifact.manifest_wellFormed.receiptCodecClosed
  mpcBasesClosed := by
    intro profile member
    simp only [manifest, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · cases profile with
      | gf2Tower => trivial
      | ext6 => trivial
      | residueRing => trivial
      | mpcShared profileId baseCarrierId protocolId federationId partyCount
          threshold transcriptAuthenticationId =>
          rcases MinidreggV1Artifact.manifest_wellFormed.mpcBasesClosed
              (.mpcShared profileId baseCarrierId protocolId federationId
                partyCount threshold transcriptAuthenticationId) old with
            ⟨base, found⟩
          exact ⟨base, base_lookupCarrier_preserved found⟩
    · trivial
  bridgeEndpointsClosed := by
    intro bridge member
    have old : bridge ∈ MinidreggV1Artifact.manifest.bridges := by
      simpa [manifest] using member
    rcases MinidreggV1Artifact.manifest_wellFormed.bridgeEndpointsClosed bridge old with
      ⟨⟨source, sourceFound⟩, ⟨target, targetFound⟩,
       ⟨sourceCodec, sourceCodecFound⟩, ⟨targetCodec, targetCodecFound⟩⟩
    exact
      ⟨⟨source, base_lookupCarrier_preserved sourceFound⟩,
       ⟨target, base_lookupCarrier_preserved targetFound⟩,
       ⟨sourceCodec, by simpa [manifest] using sourceCodecFound⟩,
       ⟨targetCodec, by simpa [manifest] using targetCodecFound⟩⟩
  dialectClausesClosed := by
    intro clause member
    simp only [manifest, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · rcases MinidreggV1Artifact.manifest_wellFormed.dialectClausesClosed clause old with
        ⟨⟨carrier, carrierFound⟩, ⟨statementCodec, statementCodecFound⟩,
         ⟨proofCodec, proofCodecFound⟩, bridgesClosed⟩
      refine
        ⟨⟨carrier, base_lookupCarrier_preserved carrierFound⟩,
         ⟨statementCodec, by simpa [manifest] using statementCodecFound⟩,
         ⟨proofCodec, by simpa [manifest] using proofCodecFound⟩, ?_⟩
      intro bridgeId bridgeMember
      simpa [manifest] using bridgesClosed bridgeId bridgeMember
    · refine
        ⟨⟨babyBearArithmeticCarrier, by decide⟩,
         ⟨MinidreggV1Artifact.dialectStatementCodec, by decide⟩,
         ⟨MinidreggV1Artifact.dialectProofCodec, by decide⟩, ?_⟩
      intro bridgeId member
      simp [arithmeticClause] at member

/-- Local artifact projection consumed by `NativeGlueGen`. -/
def artifactBundle : ArtifactBundle :=
  { MinidreggV1Artifact.bundle with manifest := manifest }

/-- The structural canonical manifest encoding and instruction order are fixed
by Lean.  No unbounded Gödel numeral is materialized by this plan. -/
def arithmeticPlan : Plan where
  manifestEncoding := manifest.canonicalEncoding
  instructions := [arithmeticInstruction]

/-- The canonical artifact which supplies the manifest used by the request. -/
def artifactEncoding : ArtifactBundleEncoding :=
  artifactBundle.canonicalEncoding

/-- The declaration fixes the work class, clause, call, public layout, and plan
order definitionally.  In particular, no native response selects any of them. -/
theorem declaration_exact :
    arithmeticInstruction.kind = .arithmetic ∧
    arithmeticInstruction.clauseId = arithmeticClause.clauseId ∧
    arithmeticInstruction.call = addKernelCall 1 1 ∧
    arithmeticInstruction.publicInputs = [] ∧
    arithmeticPlan.instructions = [arithmeticInstruction] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem plan_manifest_exact :
    arithmeticPlan.manifestEncoding = manifest.canonicalEncoding := by
  rfl

theorem artifact_manifest_exact :
    artifactBundle.manifest = manifest := by
  rfl

theorem arithmetic_clause_registered :
    manifest.lookupClause arithmeticInstruction.clauseId =
      some arithmeticClause := by
  decide

/-- Positive closure witness for the local extension.  This does not rely on
any base v1 clause being admitted. -/
theorem arithmetic_clause_registry_closed :
    manifest.lookupCarrier arithmeticClause.carrierProfileId =
        some babyBearArithmeticCarrier ∧
    manifest.lookupCodec arithmeticClause.statementCodecId =
        some MinidreggV1Artifact.dialectStatementCodec ∧
    manifest.lookupCodec arithmeticClause.proofCodecId =
        some MinidreggV1Artifact.dialectProofCodec ∧
    arithmeticClause.requiredBridgeIds = [] := by
  decide

theorem arithmetic_call_fullyWellFormed :
    arithmeticCall.FullyWellFormed := by
  exact addKernelCall_fullyWellFormed 1 1

/-! ## A positive honest response -/

/-- The all-zero assignment is the concrete witness for `0 + 0 = 0`, including
zero bit decompositions and zero boundary carries. -/
def zeroAssignment : Fin (addWireCount 1 1) → BabyBear := fun _ => 0

theorem zeroAssignment_accepts :
    systemAccepts zeroAssignment
      (AirBignum.addGadget (addWires 1 1)) := by
  apply (AirBignum.addGadget_correct zeroAssignment (addWires 1 1)).mpr
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · intro limb
    apply (rangeGadget_correct zeroAssignment
      ((addWires 1 1).x limb) ((addWires 1 1).xBit limb)).mpr
    constructor
    · intro bit
      left
      rfl
    · simp [zeroAssignment]
  · intro limb
    apply (rangeGadget_correct zeroAssignment
      ((addWires 1 1).y limb) ((addWires 1 1).yBit limb)).mpr
    constructor
    · intro bit
      left
      rfl
    · simp [zeroAssignment]
  · intro limb
    apply (rangeGadget_correct zeroAssignment
      ((addWires 1 1).z limb) ((addWires 1 1).zBit limb)).mpr
    constructor
    · intro bit
      left
      rfl
    · simp [zeroAssignment]
  · intro carry
    left
    rfl
  · intro limb
    simp [zeroAssignment]

/-- The existing emitter theorem constructs all forced auxiliary gate wires for
the honest source assignment. -/
theorem existsHonestTotalWires :
    ∃ wireValues : Nat → BabyBear,
      (∀ index, wireValues index.val = zeroAssignment index) ∧
      arithmeticCall.Accepts wireValues := by
  exact (addKernelCall_accepts_iff 1 1 zeroAssignment).mpr
    zeroAssignment_accepts

private theorem dWire_read_eq_of_bounded
    {bound : Nat} {left right : Nat → BabyBear} {wire : DWire BabyBear}
    (bounded : wire.bounded bound)
    (agree : ∀ index, index < bound → left index = right index) :
    wire.read left = wire.read right := by
  cases wire with
  | cnst value => rfl
  | wire index => exact agree index bounded

/-- A well-formed descriptor observes only its declared bounded response. -/
private theorem descriptorHolds_of_bounded_agreement
    {descriptor : ConstraintDescriptor BabyBear}
    {left right : Nat → BabyBear}
    (wellFormed : descriptor.WellFormed)
    (agree : ∀ index, index < descriptor.nWires →
      left index = right index)
    (holds : descriptorHolds descriptor left) :
    descriptorHolds descriptor right := by
  rcases holds with ⟨gatesHold, zerosHold⟩
  constructor
  · intro gate member
    rcases wellFormed.gates_in gate member with
      ⟨leftBounded, rightBounded, _, outputBounded⟩
    unfold DGate.holds
    rw [← dWire_read_eq_of_bounded leftBounded agree,
      ← dWire_read_eq_of_bounded rightBounded agree,
      ← agree gate.out outputBounded]
    exact gatesHold gate member
  · intro wire member
    rw [← dWire_read_eq_of_bounded (wellFormed.zeros_in wire member) agree]
    exact zerosHold wire member

/-- A bounded honest response exists.  Keeping the emitter's auxiliary witness
inside this proof avoids compiling a `Classical.choose`-backed runtime object. -/
theorem existsHonestResponse :
    ∃ response : KernelResponse arithmeticInstruction,
      PublicPrefixExact arithmeticInstruction response ∧
      arithmeticInstruction.call.Accepts response.totalWires := by
  rcases existsHonestTotalWires with ⟨wireValues, _, accepts⟩
  let response : KernelResponse arithmeticInstruction :=
    { wires := fun index => wireValues index.val }
  have agrees (index : Nat)
      (inBounds : index < arithmeticInstruction.call.descriptor.nWires) :
      response.totalWires index = wireValues index := by
    simp [response, KernelResponse.totalWires, inBounds]
  have fullyWellFormed : arithmeticInstruction.call.FullyWellFormed := by
    change arithmeticCall.FullyWellFormed
    exact arithmetic_call_fullyWellFormed
  have responseAccepts :
      arithmeticInstruction.call.Accepts response.totalWires := by
    apply descriptorHolds_of_bounded_agreement
      fullyWellFormed.1.descriptor
      (fun index inBounds => (agrees index inBounds).symm)
    change arithmeticCall.Accepts wireValues
    exact accepts
  refine ⟨response, ?_, responseAccepts⟩
  constructor
  · rfl
  · intro index
    exact Fin.elim0 index

/-! ## Fallible opaque execution, with Lean-owned checking -/

/-- The generated Rust trait returns `Result<KernelBufferDto, NativeErrorDto>`.
This type is its Lean boundary shape with an arbitrary opaque error payload.
The success branch contains bounded response data only. -/
abbrev FalliblePlanRunner (Error : Type) :=
  (instruction : Instruction) → Except Error (KernelResponse instruction)

/-- Concrete controller result.  Native failure is distinct from Lean rejection,
and only the Lean-checked branch can carry `CertifiedResponse`. -/
inductive Outcome (Error : Type)
  | nativeFailure (error : Error)
  | rejected (failure : NativeKernelPlan.Failure)
  | verified {response : KernelResponse arithmeticInstruction}
      (certificate : CertifiedResponse manifest
        arithmeticInstruction response)

def Outcome.IsVerified {Error : Type} : Outcome Error → Prop
  | .nativeFailure _ => False
  | .rejected _ => False
  | .verified _ => True

/-- Run exactly the declared arithmetic work.  A native error returns
immediately; only a bounded buffer is passed to the existing Lean checker. -/
def run {Error : Type} (runner : FalliblePlanRunner Error) : Outcome Error :=
  match runner arithmeticInstruction with
  | .error error => .nativeFailure error
  | .ok response =>
      match checkInstruction manifest arithmeticInstruction response with
      | .inl failure => .rejected failure
      | .inr certificate => .verified certificate

/-- Completeness for any response satisfying the declared relation: executable
reflection reduces the established facts to a Lean certificate. -/
theorem response_checked (response : KernelResponse arithmeticInstruction)
    (prefixExact : PublicPrefixExact arithmeticInstruction response)
    (accepted : arithmeticInstruction.call.Accepts response.totalWires) :
    ∃ certificate,
      checkInstruction manifest arithmeticInstruction response =
        .inr certificate := by
  have callCheck :
      kernelCallFullyWellFormedCheck arithmeticInstruction.call = true :=
    (kernelCallFullyWellFormedCheck_eq_true_iff _).mpr (by
      change arithmeticCall.FullyWellFormed
      exact arithmetic_call_fullyWellFormed)
  have prefixCheck :
      publicPrefixExactCheck arithmeticInstruction response = true :=
    (publicPrefixExactCheck_eq_true_iff _ _).mpr
      prefixExact
  have acceptsCheck :
      kernelCallAcceptsCheck arithmeticInstruction response = true :=
    (kernelCallAcceptsCheck_eq_true_iff _ _).mpr accepted
  unfold checkInstruction
  split
  · rename_i hlookup
    have impossible : (none : Option DialectClauseDecl) = some arithmeticClause :=
      hlookup.symm.trans arithmetic_clause_registered
    cases impossible
  · rename_i clause hlookup
    split
    · exact ⟨_, rfl⟩
    · rename_i rejected
      exact (rejected callCheck).elim

/-- Positive nonvacuity tooth: the honest bounded response reaches the existing
Lean checker's certificate branch.  No dependent total runner or fabricated
responses for unrelated instructions are needed to state this fact. -/
theorem existsHonestCertifiedResponse :
    ∃ response : KernelResponse arithmeticInstruction,
      ∃ certificate,
        checkInstruction manifest arithmeticInstruction response =
          .inr certificate := by
  rcases existsHonestResponse with ⟨response, prefixExact, accepted⟩
  rcases response_checked response prefixExact accepted with
    ⟨certificate, checked⟩
  exact ⟨response, certificate, checked⟩

/-- A native error cannot be reinterpreted as a magic response buffer and cannot
reach the certificate-bearing branch. -/
theorem nativeFailure_stops {Error : Type}
    (runner : FalliblePlanRunner Error) (error : Error)
    (failed : runner arithmeticInstruction = .error error) :
    run runner = .nativeFailure error := by
  unfold run
  rw [failed]

theorem nativeFailure_not_verified {Error : Type}
    (runner : FalliblePlanRunner Error) (error : Error)
    (failed : runner arithmeticInstruction = .error error) :
    ¬ (run runner).IsVerified := by
  intro reached
  rw [nativeFailure_stops runner error failed] at reached
  exact reached

/-! ## Explicit residuals

`DialectClauseDecl` currently contains relation/carrier/codec/proof/controller
identifiers, but no `WorkKind`.  Consequently `arithmetic_clause_registered`
cannot itself imply `instruction.kind = .arithmetic`; `declaration_exact` is the
Lean-owned pin for this emitted work.  Likewise, this module intentionally has
no hash or transform constructor: those labels have no corresponding generated
`KernelCall` schema/checker today.  This module also does not register a
`DialectClauseDispatch.ControllerEntry`: binding its checked response into a
semantic-turn clause controller is the next integration seam, so manifest
registration here must not be read as semantic-turn admission.
-/

#print axioms nativeFailure_not_verified
#print axioms existsHonestCertifiedResponse

end Minidregg.Compiler.MinidreggV1ArithmeticWork
