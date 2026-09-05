/-
# Compiler.EvmStage0NativeDeployment -- Stage 0 (EVM u256 add) routed through the native seam

Lane B of `zkml-research/notes/descriptor-reader-scout.md` §4.  The August deletions
(`d55ef32`) removed the hand-written Rust descriptor reader, trace generator and
`descriptor_holds` mirror, and the decision record forbids their return: "Rust does not parse
the authoritative semantic request ... Deleted authority islands: ... descriptor
satisfaction ... They must not be reintroduced as handwritten parallel protocol profiles."
This module is the lawful shape.  The Stage-0 descriptor's gate rows are EMITTED by
`NativeGlueGen` as generated Rust constants beside a new authenticated work item; Rust
evaluates the rows over Lean-supplied variable words and returns 4,131 candidate words; Lean
alone decodes them and runs the existing `checkInstruction` -- clause lookup, call shape,
public prefix, `descriptorHoldsCheck`.

What is here:
* work `9103` on the BabyBear carrier `206`, request codec `9007` (833 words) and response
  codec `9009` (4,131 words), kernel tag `evmStage0AddAux`; the shape word counts are proved
  equal to the emitted descriptor's `nVars`/`nWires`;
* the `KernelCall` (abi 1, `constraintDescriptorV1`, the seven segments of `evmAddWires`, no
  witness calls, `evmAddDescriptor`) proved `FullyWellFormed`, and the `Instruction` whose
  public inputs are `encodeBoundary X Y Z` as a 48-list;
* clause `407`, the byte controller (`issue` = the 833 honest variables, `check` = decode +
  `checkInstruction`), the extended manifest and artifact with their closure theorems, the
  registry, the deployment join, and the `BuildTarget` writing
  `prover/generated/evm_stage0_add_aux.rs`;
* statement-first witness and falsifiers: the honest response is certified for every in-range
  operand pair (`honest_certified`); the claimed-`Z` forgery is refused at the public prefix
  with the descriptor still satisfied (`forged_claim_refused`); an unregistered clause id is
  refused before any descriptor check (`unregistered_clause_refused`); the catalog pins
  `9103` exactly (`work_9103_pinned`) and answers to no `9104` (`work_9104_absent`);
* compiled exhibits with teeth (the tree's idiom: an `#eval` that THROWS fails elaboration)
  on Lane A's five anvil vectors at the byte controller, plus the forged claim, a single-wire
  tamper of the reply, and a short reply.

No Rust proposition, semantic verdict, or refinement theorem exists here.  The Rust reply is
compared against Lane A's Lean-written words only in `prover/tests/evm_stage0_dispatch.rs`,
as vector agreement.
-/
import Compiler.ArithmeticNativeDeployment
import Compiler.DescriptorEval

namespace Minidregg.Compiler.EvmStage0NativeDeployment

open Minidregg.Compiler.BignumKernelABI
open Minidregg.Compiler.ComposableDeploymentManifest
open Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.EvmAddAir
open Minidregg.Compiler.NativeGlueGen
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.SemanticArtifactBundle
open Minidregg.Compiler.SemanticManifest
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false
set_option maxRecDepth 4096

/-! ## The artifact-authenticated Stage-0 work -/

/-- Request: the 833 descriptor variables as canonical u32 LE words (3,332 bytes). -/
def requestCodec : ByteCodecProfile where
  registry := .nativeAbi
  codecId := 9007
  valueTypeId := 9008
  version := 1
  shape := .evmStage0AddVarsU32LE

/-- Response: the 4,131 total wires as canonical u32 LE words (16,524 bytes). -/
def responseCodec : ByteCodecProfile where
  registry := .nativeAbi
  codecId := 9009
  valueTypeId := 9010
  version := 1
  shape := .evmStage0AddWiresU32LE

/-- Work `9103`: the Stage-0 auxiliary fill on the BabyBear carrier `206`. -/
def workProfile : WorkProfile where
  workId := 9103
  carrierProfileId := MinidreggV1ArithmeticWork.babyBearArithmeticCarrier.id.value
  requestCodec := requestCodec
  responseCodec := responseCodec
  kernel := .evmStage0AddAux

theorem work_profile_pins_exact :
    workProfile.workId = 9103 ∧ workProfile.carrierProfileId = 206 ∧
    workProfile.requestCodec.codecId = 9007 ∧ workProfile.responseCodec.codecId = 9009 ∧
    workProfile.kernel = .evmStage0AddAux :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The byte shapes agree with the emitted descriptor -/

theorem descriptor_nPublic : evmAddDescriptor.nPublic = 48 := rfl
theorem descriptor_nVars : evmAddDescriptor.nVars = evmStage0RequestWords := rfl
theorem descriptor_nWires : evmAddDescriptor.nWires = evmStage0ResponseWords :=
  evmAddDescriptor_shape.2.1

/-! ## The call and the instruction -/

/-- The seven segments of `evmAddWires`: limbs public, bits and carries witness. -/
def segments : List WireSegment :=
  [{ name := "x", offset := 0, length := 16,
     visibility := .publicInput, encoding := .radixLimbs 16 },
   { name := "y", offset := 16, length := 16,
     visibility := .publicInput, encoding := .radixLimbs 16 },
   { name := "z", offset := 32, length := 16,
     visibility := .publicInput, encoding := .radixLimbs 16 },
   { name := "x_bits", offset := 48, length := 256, visibility := .witness, encoding := .bits },
   { name := "y_bits", offset := 304, length := 256, visibility := .witness, encoding := .bits },
   { name := "z_bits", offset := 560, length := 256, visibility := .witness, encoding := .bits },
   { name := "carry", offset := 816, length := 17,
     visibility := .witness, encoding := .fieldElement }]

/-- The Stage-0 kernel call: the generic descriptor entry over the EMITTED descriptor, no
witness calls -- the 785 witness variables are supplied, and `evmAddAsg` is their only
author. -/
def call : KernelCall where
  abiVersion := 1
  entry := .constraintDescriptorV1
  segments := segments
  calls := []
  descriptor := evmAddDescriptor

theorem call_wellFormed : call.WellFormed := by
  constructor
  · exact evmAddDescriptor_wellFormed
  · show segmentsCoverFrom 48 0 segments 833
    simp [segments, segmentsCoverFrom, WireSegment.visibilityFits]

theorem call_fullyWellFormed : call.FullyWellFormed :=
  ⟨call_wellFormed, fun _ member => by simp [call] at member⟩

/-- The plan's public inputs: `encodeBoundary X Y Z` as the 48-list. -/
def publicInputs (X Y Z : ℕ) : List BabyBear :=
  (List.finRange 48).map (encodeBoundary X Y Z)

theorem publicInputs_length (X Y Z : ℕ) : (publicInputs X Y Z).length = 48 := by
  simp [publicInputs]

theorem publicInputs_getD (X Y Z : ℕ) (i : Fin 48) :
    (publicInputs X Y Z).getD i.1 0 = encodeBoundary X Y Z i := by
  simp [publicInputs, List.getD_eq_getElem?_getD]
  all_goals exact congrArg _ (Fin.ext rfl)

/-- The Stage-0 clause: distinct from base v1 (401--403), LogUp (404), additive (405) and
add-1 (406); the same BabyBear carrier and dialect codecs as 406. -/
def clause : DialectClauseDecl where
  clauseId := MinidreggV1Artifact.id 407
  relationId := MinidreggV1Artifact.id 417
  carrierProfileId := MinidreggV1ArithmeticWork.babyBearArithmeticCarrier.id
  statementCodecId := MinidreggV1Artifact.dialectStatementCodec.codecId
  proofCodecId := MinidreggV1Artifact.dialectProofCodec.codecId
  proofSuiteId := MinidreggV1Artifact.id 427
  verifierControllerDigest := MinidreggV1Artifact.manifest.transcriptControllerDigest
  requiredBridgeIds := []

/-- **The registered instruction** for the claim `X + Y ≡ Z (mod 2²⁵⁶)`. -/
def instruction (X Y Z : ℕ) : Instruction :=
  Instruction.arithmetic clause.clauseId call (publicInputs X Y Z)

theorem instruction_call (X Y Z : ℕ) : (instruction X Y Z).call = call := rfl
theorem call_descriptor : call.descriptor = evmAddDescriptor := rfl

/-- The response width, reached only through the kernel-decided shape theorem: nothing here
evaluates the 3,298-gate flattening at elaboration time. -/
theorem instruction_nWires (X Y Z : ℕ) :
    (instruction X Y Z).call.descriptor.nWires = evmStage0ResponseWords := by
  rw [instruction_call, call_descriptor, descriptor_nWires]

theorem instruction_nPublic (X Y Z : ℕ) : (instruction X Y Z).call.descriptor.nPublic = 48 :=
  rfl

/-! ## Manifest -/

/-- The clause-406 manifest with clause 407 appended; carriers, codecs, bridges unchanged. -/
def manifest : Manifest :=
  { MinidreggV1ArithmeticWork.manifest with
    dialectClauses := MinidreggV1ArithmeticWork.manifest.dialectClauses ++ [clause] }

theorem clause_registered : manifest.lookupClause clause.clauseId = some clause := by
  decide

theorem manifest_wellFormed : manifest.WellFormed where
  codecIdsUnique := MinidreggV1ArithmeticWork.manifest_wellFormed.codecIdsUnique
  carrierIdsUnique := MinidreggV1ArithmeticWork.manifest_wellFormed.carrierIdsUnique
  bridgeIdsUnique := MinidreggV1ArithmeticWork.manifest_wellFormed.bridgeIdsUnique
  dialectClauseIdsUnique := by
    show (manifest.dialectClauses.map DialectClauseDecl.clauseId).Nodup
    decide
  receiptCodecClosed := MinidreggV1ArithmeticWork.manifest_wellFormed.receiptCodecClosed
  mpcBasesClosed := MinidreggV1ArithmeticWork.manifest_wellFormed.mpcBasesClosed
  bridgeEndpointsClosed :=
    MinidreggV1ArithmeticWork.manifest_wellFormed.bridgeEndpointsClosed
  dialectClausesClosed := by
    intro c member
    simp only [manifest, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact MinidreggV1ArithmeticWork.manifest_wellFormed.dialectClausesClosed c old
    · exact ⟨⟨MinidreggV1ArithmeticWork.babyBearArithmeticCarrier, by decide⟩,
        ⟨MinidreggV1Artifact.dialectStatementCodec, by decide⟩,
        ⟨MinidreggV1Artifact.dialectProofCodec, by decide⟩,
        fun _ member => by simp [clause] at member⟩

/-! ## Bytes: the request the controller issues, the reply Lean decodes -/

/-- The request for `(X, Y)`: the 833 variables of the honest assignment (Lean's witness-gen
`evmAddAsg`, the only author of the 785 witness words), u32 LE. -/
def requestBytes (X Y : ℕ) : List UInt8 :=
  (List.ofFn (evmAddAsg X Y)).flatMap ArithmeticNativeDeployment.encodeWord

theorem length_flatMap_encodeWord (words : List BabyBear) :
    (words.flatMap ArithmeticNativeDeployment.encodeWord).length = 4 * words.length := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
      simp only [List.flatMap_cons, List.length_append, ih,
        ArithmeticNativeDeployment.encodeWord, NativeWorkProfiles.encodeU32LE_length,
        List.length_cons]
      omega

theorem requestBytes_length (X Y : ℕ) :
    (requestBytes X Y).length = 4 * evmStage0RequestWords := by
  rw [requestBytes, length_flatMap_encodeWord, List.length_ofFn]
  rfl

def responseOfList (X Y Z : ℕ) (wires : List BabyBear)
    (lengthExact : wires.length = evmStage0ResponseWords) :
    KernelResponse (instruction X Y Z) where
  wires := fun index => wires.get ⟨index.val,
    lt_of_lt_of_eq (lt_of_lt_of_eq index.isLt (instruction_nWires X Y Z)) lengthExact.symm⟩

/-- Decode exactly 16,524 bytes as 4,131 canonical words; anything else is `none`. -/
def decodeResponse (X Y Z : ℕ) (bytes : List UInt8) :
    Option (KernelResponse (instruction X Y Z)) :=
  if bytes.length = 4 * evmStage0ResponseWords then
    match ArithmeticNativeDeployment.decodeWords evmStage0ResponseWords bytes with
    | none => none
    | some wires =>
        if lengthExact : wires.length = evmStage0ResponseWords then
          some (responseOfList X Y Z wires lengthExact)
        else none
  else none

/-! ## The honest response: Lane A's candidate in the bounded buffer -/

theorem evmAddCandidate_size (X Y : ℕ) :
    (evmAddCandidate X Y).size = evmAddDescriptor.nWires :=
  fillAux_size evmAddDescriptor _ evmAddDescriptor_wellFormed Array.size_ofFn

/-- A response read from an array of exactly the descriptor's width. -/
def responseOfArray (instr : Instruction) (c : Array BabyBear) : KernelResponse instr where
  wires := fun index => c.getD index.val 0

/-! The two response lemmas are stated over a VARIABLE instruction and array: nothing here
is a closed term the elaborator could try to evaluate (the Stage-0 descriptor's flattening
is a 3,298-gate computation that must only ever be reached through the kernel-decided
`evmAddDescriptor_shape`).  The Stage-0 instances below are term-mode chains of syntactic
equalities. -/

theorem responseOfArray_totalWires (instr : Instruction) (c : Array BabyBear)
    (hsize : c.size = instr.call.descriptor.nWires) :
    (responseOfArray instr c).totalWires = fun index => c.getD index 0 := by
  funext index
  unfold KernelResponse.totalWires
  split
  · rfl
  · rename_i outside
    rw [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by rw [hsize]; exact Nat.le_of_not_lt outside)]
    rfl

theorem responseOfArray_prefix (instr : Instruction) (c : Array BabyBear)
    (hsize : c.size = instr.call.descriptor.nWires)
    (hlen : instr.publicInputs.length = instr.call.descriptor.nPublic)
    (hpins : ∀ i : Fin instr.call.descriptor.nPublic,
      c.getD i.val 0 = instr.publicInputs.getD i.val 0) :
    PublicPrefixExact instr (responseOfArray instr c) :=
  ⟨hlen, fun i => by rw [responseOfArray_totalWires instr c hsize]; exact hpins i⟩

/-- **The honest response**: `evmAddCandidate`, a theorem-satisfying vector
(`evmAddCandidate_holds`), read into the bounded response buffer.  `Z` enters only through
the instruction's type: the reply does not depend on what is claimed. -/
def honestResponse (X Y Z : ℕ) : KernelResponse (instruction X Y Z) :=
  responseOfArray (instruction X Y Z) (evmAddCandidate X Y)

theorem honestResponse_size (X Y Z : ℕ) :
    (evmAddCandidate X Y).size = (instruction X Y Z).call.descriptor.nWires :=
  (evmAddCandidate_size X Y).trans (descriptor_nWires.trans (instruction_nWires X Y Z).symm)

theorem honestResponse_totalWires (X Y Z : ℕ) :
    (honestResponse X Y Z).totalWires = fun index => (evmAddCandidate X Y).getD index 0 :=
  responseOfArray_totalWires (instruction X Y Z) (evmAddCandidate X Y)
    (honestResponse_size X Y Z)

theorem honestResponse_accepts (X Y Z : ℕ) (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256) :
    (instruction X Y Z).call.Accepts (honestResponse X Y Z).totalWires := by
  rewrite [honestResponse_totalWires]
  exact evmAddCandidate_holds X Y hX hY

theorem honestResponse_prefix (X Y : ℕ) :
    PublicPrefixExact (instruction X Y ((X + Y) % 2 ^ 256))
      (honestResponse X Y ((X + Y) % 2 ^ 256)) :=
  responseOfArray_prefix (instruction X Y ((X + Y) % 2 ^ 256)) (evmAddCandidate X Y)
    (honestResponse_size X Y _) (publicInputs_length X Y _) fun i =>
      let j : Fin 48 := ⟨i.val, lt_of_lt_of_eq i.isLt (instruction_nPublic X Y _)⟩
      (evmAddCandidate_pins X Y j).trans (publicInputs_getD X Y _ j).symm

/-! ## Witness and falsifiers at the Lean checker -/

/-- Completeness: any response with the exact public prefix that satisfies the descriptor
reaches the checker's certificate branch. -/
theorem response_checked (X Y Z : ℕ) (response : KernelResponse (instruction X Y Z))
    (prefixExact : PublicPrefixExact (instruction X Y Z) response)
    (accepted : (instruction X Y Z).call.Accepts response.totalWires) :
    ∃ certificate,
      checkInstruction manifest (instruction X Y Z) response = .inr certificate := by
  have callCheck : kernelCallFullyWellFormedCheck (instruction X Y Z).call = true :=
    (kernelCallFullyWellFormedCheck_eq_true_iff _).mpr call_fullyWellFormed
  have prefixCheck : publicPrefixExactCheck (instruction X Y Z) response = true :=
    (publicPrefixExactCheck_eq_true_iff _ _).mpr prefixExact
  have acceptsCheck : kernelCallAcceptsCheck (instruction X Y Z) response = true :=
    (kernelCallAcceptsCheck_eq_true_iff _ _).mpr accepted
  unfold checkInstruction
  split
  · rename_i hlookup
    have impossible : (none : Option DialectClauseDecl) = some clause :=
      hlookup.symm.trans clause_registered
    cases impossible
  · rename_i c hlookup
    split
    · exact ⟨_, rfl⟩
    · rename_i rejected
      exact (rejected callCheck).elim

/-- **Witness**: for every in-range operand pair, the registered instruction with the honest
reply is certified. -/
theorem honest_certified (X Y : ℕ) (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256) :
    ∃ certificate,
      checkInstruction manifest (instruction X Y ((X + Y) % 2 ^ 256))
        (honestResponse X Y ((X + Y) % 2 ^ 256)) = .inr certificate :=
  response_checked X Y _ _ (honestResponse_prefix X Y)
    (honestResponse_accepts X Y _ hX hY)

/-- **Falsifier at the public prefix**: the honest reply for `(X, Y)` under a CLAIMED `Z`
that is not the wrapped sum is refused as `publicPrefixMismatch` -- before the descriptor
check, and with the descriptor still satisfied.  The forgery shape of
`evmAdd_forged_refused`, at the plan. -/
theorem forged_claim_refused (X Y Z : ℕ) (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256)
    (hZ : Z < 2 ^ 256) (forged : Z ≠ (X + Y) % 2 ^ 256) :
    checkInstruction manifest (instruction X Y Z) (honestResponse X Y Z) =
      .inl (.publicPrefixMismatch clause.clauseId) := by
  have callCheck : kernelCallFullyWellFormedCheck (instruction X Y Z).call = true :=
    (kernelCallFullyWellFormedCheck_eq_true_iff _).mpr call_fullyWellFormed
  have prefixNot : ¬ publicPrefixExactCheck (instruction X Y Z) (honestResponse X Y Z) = true := by
    intro exact
    have pins := ((publicPrefixExactCheck_eq_true_iff _ _).mp exact).2
    apply forged
    have same : encodeBoundary X Y ((X + Y) % 2 ^ 256) = encodeBoundary X Y Z := by
      funext i
      have pin := pins ⟨i.1, lt_of_lt_of_eq i.isLt (instruction_nPublic X Y Z).symm⟩
      have total := congrFun (honestResponse_totalWires X Y Z) i.1
      exact (evmAddCandidate_pins X Y i).symm.trans
        (total.symm.trans (pin.trans (publicInputs_getD X Y Z i)))
    exact (encodeBoundary_injective hX hY (Nat.mod_lt _ (by positivity)) hX hY hZ same).2.2.symm
  unfold checkInstruction
  split
  · rename_i hlookup
    have impossible : (none : Option DialectClauseDecl) = some clause :=
      hlookup.symm.trans clause_registered
    cases impossible
  · rename_i c hlookup
    split
    · rfl
    · rename_i rejected
      exact (rejected callCheck).elim

/-- **Falsifier at the clause**: the same call and public inputs under a clause id the manifest
does not register are refused before any descriptor check runs. -/
theorem unregistered_clause_refused (X Y Z : ℕ)
    (response : KernelResponse
      (Instruction.arithmetic (MinidreggV1Artifact.id 408) call (publicInputs X Y Z))) :
    checkInstruction manifest
        (Instruction.arithmetic (MinidreggV1Artifact.id 408) call (publicInputs X Y Z))
        response =
      .inl (.unregisteredClause (MinidreggV1Artifact.id 408)) := by
  have absent : manifest.lookupClause (MinidreggV1Artifact.id 408) = none := by decide
  unfold checkInstruction
  split
  · rfl
  · rename_i c found
    have impossible : (none : Option DialectClauseDecl) = some c := absent.symm.trans found
    cases impossible

/-! ## Controller, pack, artifact, registry, deployment -/

inductive ByteControllerOutcome (X Y Z : ℕ)
  | malformedResponse (bytes : List UInt8)
  | rejected (bytes : List UInt8) (failure : NativeKernelPlan.Failure)
  | certified (bytes : List UInt8) (response : KernelResponse (instruction X Y Z))
      (certificate : CertifiedResponse manifest (instruction X Y Z) response)

/-- The controller's input: the operands the request is built from, and the CLAIMED result
the plan pins as public inputs. -/
structure Claim where
  X : ℕ
  Y : ℕ
  Z : ℕ

/-- The byte controller for clause 407: issue the 833 honest variable words; on reply, decode
exactly 4,131 words and run the existing Lean checker.  Rust's bytes never become
acceptance without the `CertifiedResponse` this constructs. -/
def byteController : DialectController.{0, 0, 0, 0} clause where
  Input := Claim
  Query := fun _ => List UInt8
  Reply := fun _ _ => List UInt8
  Outcome := fun claim => ByteControllerOutcome claim.X claim.Y claim.Z
  issue := fun claim => requestBytes claim.X claim.Y
  check := fun claim bytes =>
    match decodeResponse claim.X claim.Y claim.Z bytes with
    | none => .malformedResponse bytes
    | some response =>
        match checkInstruction manifest (instruction claim.X claim.Y claim.Z) response with
        | .inl failure => .rejected bytes failure
        | .inr certificate => .certified bytes response certificate

def entry : ControllerEntry.{0, 0, 0, 0} where
  declaration := clause
  controller := byteController

/-- The Stage-0 pack: two transport codecs, one work item, one controller entry; the carrier
`206` and the dialect codecs are already in the base. -/
def pack : ImplementedControllerPack.{0, 0, 0, 0} where
  nativeAbiCodecs := [requestCodec, responseCodec]
  nativeWorkCatalog := [workProfile]
  entries := [entry]

/-- The deployed artifact: the clause-406 deployment extended by the Stage-0 pack.  Catalog
order `[9101, 9102, 9103]` is the generated `WORK_0/1/2` order. -/
def artifact : ArtifactBundle :=
  pack.extendArtifact ArithmeticNativeDeployment.artifact

theorem artifact_manifest : artifact.manifest = manifest := by
  rfl

theorem artifact_nativeAbiCodecs :
    artifact.nativeAbiCodecs =
      [MinidreggV1Artifact.tower256DotProductRequestCodec,
        ArithmeticNativeDeployment.requestCodec, ArithmeticNativeDeployment.responseCodec,
        requestCodec, responseCodec] := by
  rfl

theorem artifact_nativeWorkCatalog :
    artifact.nativeWorkCatalog =
      [MinidreggV1Artifact.tower256DotProductWork, ArithmeticNativeDeployment.workProfile,
        workProfile] := by
  rfl

/-- **Membership**: work `9103` and its two transport codecs are in the authenticated
catalog. -/
theorem artifact_contains_exact_native_surface :
    requestCodec ∈ artifact.nativeAbiCodecs ∧ responseCodec ∈ artifact.nativeAbiCodecs ∧
    workProfile ∈ artifact.nativeWorkCatalog := by
  rw [artifact_nativeAbiCodecs, artifact_nativeWorkCatalog]
  simp

/-- The catalog pins `9103` exactly: any entry answering to that id IS this profile -- same
carrier, codecs and kernel tag. -/
theorem work_9103_pinned :
    ∀ work ∈ artifact.nativeWorkCatalog, work.workId = 9103 → work = workProfile := by
  rw [artifact_nativeWorkCatalog]
  decide

/-- **Falsifier at the catalog**: nothing answers to an unregistered work id. -/
theorem work_9104_absent : ∀ work ∈ artifact.nativeWorkCatalog, work.workId ≠ 9104 := by
  rw [artifact_nativeWorkCatalog]
  decide

theorem artifact_nativeCatalogWellFormed :
    NativeCatalogWellFormed artifact.manifest artifact.nativeAbiCodecs
      artifact.nativeWorkCatalog := by
  rw [artifact_manifest, artifact_nativeAbiCodecs, artifact_nativeWorkCatalog]
  constructor
  · decide
  · decide
  · intro codec member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro codec member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro work member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨MinidreggV1Artifact.gf2Tower256Carrier, by decide⟩
    · exact ⟨MinidreggV1ArithmeticWork.babyBearArithmeticCarrier, by decide⟩
    · exact ⟨MinidreggV1ArithmeticWork.babyBearArithmeticCarrier, by decide⟩
  · intro work member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · show lookupNativeAbiCodec _ 9001 = some MinidreggV1Artifact.tower256DotProductRequestCodec
      decide
    · show lookupNativeAbiCodec _ 9003 = some ArithmeticNativeDeployment.requestCodec
      decide
    · show lookupNativeAbiCodec _ 9007 = some requestCodec
      decide
  · intro work member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · show manifest.lookupCodec MinidreggV1Artifact.tower256ValueCodec.codecId =
        some MinidreggV1Artifact.tower256ValueCodec
      decide
    · show lookupNativeAbiCodec _ 9005 = some ArithmeticNativeDeployment.responseCodec
      decide
    · show lookupNativeAbiCodec _ 9009 = some responseCodec
      decide

/-- The registry: clause 406's byte controller and clause 407's, in pack order. -/
def registry : ControllerRegistry.{0, 0, 0, 0} :=
  (ArithmeticNativeDeployment.bytePack.append pack).controllerRegistry

theorem registry_entries :
    registry.entries = [ArithmeticNativeDeployment.byteControllerEntry, entry] := by
  rfl

theorem registry_wellFormed : registry.WellFormed artifact.manifest := by
  rw [artifact_manifest]
  constructor
  · show ([ArithmeticNativeDeployment.byteControllerEntry.key, entry.key] :
      List ControllerKey).Nodup
    decide
  · intro e member
    rw [registry_entries] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · decide
    · exact clause_registered
  · intro c member
    change c ∈ [MinidreggV1ArithmeticWork.arithmeticClause, clause] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨ArithmeticNativeDeployment.byteControllerEntry, by
        simp [ControllerRegistry.lookup, registry_entries, ControllerEntry.key,
          clauseControllerKey, ArithmeticNativeDeployment.byteControllerEntry, entry,
          clause, MinidreggV1ArithmeticWork.arithmeticClause, MinidreggV1Artifact.id]⟩
    · exact ⟨entry, by
        simp [ControllerRegistry.lookup, registry_entries, ControllerEntry.key,
          clauseControllerKey, ArithmeticNativeDeployment.byteControllerEntry, entry,
          clause, MinidreggV1ArithmeticWork.arithmeticClause, MinidreggV1Artifact.id]⟩

def deployment : DeploymentJoin.{0, 0, 0, 0} where
  artifact := artifact
  registry := registry
  manifestWellFormed := by
    rw [artifact_manifest]
    exact manifest_wellFormed
  nativeCatalogWellFormed := artifact_nativeCatalogWellFormed
  controllerRegistryWellFormed := registry_wellFormed

noncomputable def resolved :
    ResolvedClause deployment.artifact.manifest deployment.registry clause.clauseId :=
  resolveRegistered deployment.manifestWellFormed deployment.controllerRegistryWellFormed
    clause_registered

theorem resolved_controller_exact : resolved.controllerEntry.declaration = clause :=
  resolved.controllerExact.trans
    (deployment.artifact.manifest.lookupClause_unique
      deployment.manifestWellFormed.dialectClauseIdsUnique
      resolved.clauseFound clause_registered)

theorem malformed_bytes_cannot_certify (claim : Claim) {bytes : List UInt8}
    (wrongWidth : bytes.length ≠ 4 * evmStage0ResponseWords) :
    ¬ ∃ response certificate,
      byteController.check claim bytes = .certified bytes response certificate := by
  intro certified
  rcases certified with ⟨response, certificate, exact⟩
  have decodedNone : decodeResponse claim.X claim.Y claim.Z bytes = none := by
    simp [decodeResponse, wrongWidth]
  simp [byteController, decodedNone] at exact

/-- Generic dispatch transport failure blocks before the byte checker runs. -/
theorem native_error_blocks
    (input : resolved.Input) (oracle : NativeOracle resolved input)
    (failure : NativeFailure)
    (failed : oracle (resolved.controllerEntry.controller.issue input) = .error failure) :
    DialectClauseDispatch.run resolved input oracle = .blocked failure :=
  run_nativeFailure resolved input oracle failure failed

/-! ## The generated Rust surface -/

/-- Writes `prover/generated/evm_stage0_add_aux.rs`: the catalog `[9101, 9102, 9103]` as
`WORK_0/1/2` constants, the Stage-0 gate rows and zero-checks as `WORK_2_ROWS` /
`WORK_2_ZEROS`, the DTOs, and the one byte/error dispatch.  Data and transport only. -/
def rustBuildTarget : NativeGlueGen.BuildTarget where
  path := "prover/generated/evm_stage0_add_aux.rs"
  bundle := artifact
  nativeCatalogWellFormed := artifact_nativeCatalogWellFormed

#eval rustBuildTarget.run

/-! ## Exhibits -- compiled, with teeth

Lane A's five anvil vectors through the byte controller on Lean's own honest bytes (the
words the Rust test compares its reply against), then the claimed-`Z` forgery, a
single-wire tamper of the reply, and a short reply.  Each `#eval` THROWS on a deviation, so
the file cannot elaborate wrong.  These are non-vacuity witnesses of `honest_certified` /
`forged_claim_refused` / `malformed_bytes_cannot_certify` at the COMPILED controller on
concrete data -- computed checks, confessed as such, not theorems. -/

/-- The honest reply bytes for `(X, Y)`: `evmAddCandidate` as 4,131 u32 LE words. -/
def honestBytes (X Y : ℕ) : List UInt8 :=
  ((List.range evmStage0ResponseWords).map fun i => (evmAddCandidate X Y).getD i 0).flatMap
    ArithmeticNativeDeployment.encodeWord

/-- The honest reply with ONE aux word -- wire `833`, the first aux wire, gate 0's output --
bumped by `+1`: the shape of a native reply returning one wrong word. -/
def tamperedBytes (X Y : ℕ) : List UInt8 :=
  ((List.range evmStage0ResponseWords).map fun i =>
      let w := (evmAddCandidate X Y).getD i 0
      if i = evmStage0RequestWords then w + 1 else w).flatMap
    ArithmeticNativeDeployment.encodeWord

inductive Expected
  | certified
  | malformed
  | prefixMismatch
  | descriptorRejected

def Expected.name : Expected → String
  | .certified => "certified"
  | .malformed => "malformedResponse"
  | .prefixMismatch => "rejected (publicPrefixMismatch)"
  | .descriptorRejected => "rejected (descriptorRejected)"

def outcomeName {X Y Z : ℕ} : ByteControllerOutcome X Y Z → String
  | .malformedResponse _ => "malformedResponse"
  | .rejected _ failure => s!"rejected ({repr failure})"
  | .certified _ _ _ => "certified"

def outcomeMatches {X Y Z : ℕ} : Expected → ByteControllerOutcome X Y Z → Bool
  | .certified, .certified _ _ _ => true
  | .malformed, .malformedResponse _ => true
  | .prefixMismatch, .rejected _ (.publicPrefixMismatch _) => true
  | .descriptorRejected, .rejected _ (.descriptorRejected _) => true
  | _, _ => false

def expectOutcome (name : String) (claim : Claim) (bytes : List UInt8) (expected : Expected) :
    IO Unit := do
  let outcome := byteController.check claim bytes
  unless outcomeMatches expected outcome do
    throw <| IO.userError s!"{name}: byte controller returned {outcomeName outcome}, \
      expected {expected.name}"
  IO.println s!"{name}: {expected.name}"

/-- Honest exhibit: the issued request is the reply's variable prefix (what the Rust test
feeds in), and the honest reply is certified. -/
def exhibitHonest (v : AnvilVector) : IO Unit := do
  let reply := honestBytes v.X v.Y
  unless reply.length = 4 * evmStage0ResponseWords do
    throw <| IO.userError s!"{v.name}: honest reply has {reply.length} bytes"
  unless reply.take (4 * evmStage0RequestWords) = requestBytes v.X v.Y do
    throw <| IO.userError s!"{v.name}: the issued request is not the reply's variable prefix"
  expectOutcome s!"{v.name} honest reply" ⟨v.X, v.Y, v.Z⟩ reply .certified

#eval anvilVectors.forM exhibitHonest

/-! *Teeth, forged claim*: V3's inputs with the claimed `Z = 5` (the semantics say `4`) on the
HONEST reply -- refused at the public prefix, before the descriptor check. -/
#eval expectOutcome "claimed Z = 5 on (2^256 - 1, 5)" ⟨2 ^ 256 - 1, 5, 5⟩
  (honestBytes (2 ^ 256 - 1) 5) .prefixMismatch

/-! *Teeth, single-wire tamper*: V1's reply with wire 833 bumped -- the mutation is asserted
first, then the descriptor check must refuse it. -/
#eval do
  let honest := honestBytes 1 2
  let tampered := tamperedBytes 1 2
  unless tampered ≠ honest do
    throw <| IO.userError "tamper: the mutation is vacuous (tampered = honest)"
  unless tampered.length = honest.length do
    throw <| IO.userError "tamper: the mutation changed the width"
  expectOutcome "V1 wire 833 + 1" ⟨1, 2, 3⟩ tampered .descriptorRejected

/-! *Teeth, short reply*: one word missing is malformed, never checked. -/
#eval expectOutcome "V1 reply minus one word" ⟨1, 2, 3⟩ ((honestBytes 1 2).drop 4) .malformed

/-! ## Axiom accounting -/

/-- info: 'Minidregg.Compiler.EvmStage0NativeDeployment.honest_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honest_certified
/-- info: 'Minidregg.Compiler.EvmStage0NativeDeployment.forged_claim_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms forged_claim_refused
/-- info: 'Minidregg.Compiler.EvmStage0NativeDeployment.unregistered_clause_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unregistered_clause_refused
/-- info: 'Minidregg.Compiler.EvmStage0NativeDeployment.call_fullyWellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms call_fullyWellFormed
/-- info: 'Minidregg.Compiler.EvmStage0NativeDeployment.manifest_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms manifest_wellFormed
/-- info: 'Minidregg.Compiler.EvmStage0NativeDeployment.artifact_nativeCatalogWellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms artifact_nativeCatalogWellFormed
/-- info: 'Minidregg.Compiler.EvmStage0NativeDeployment.registry_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms registry_wellFormed
/-- info: 'Minidregg.Compiler.EvmStage0NativeDeployment.work_9103_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms work_9103_pinned
/-- info: 'Minidregg.Compiler.EvmStage0NativeDeployment.work_9104_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms work_9104_absent
/-- info: 'Minidregg.Compiler.EvmStage0NativeDeployment.malformed_bytes_cannot_certify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformed_bytes_cannot_certify
/-- info: 'Minidregg.Compiler.EvmStage0NativeDeployment.resolved_controller_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_controller_exact

end Minidregg.Compiler.EvmStage0NativeDeployment
