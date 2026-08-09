/-
# Compiler.SemanticTurnReceiptDescriptor — Lean-authoritative receipt artifact

The semantic relation already exists in `Assurance.SemanticReceiptRelation`:
`ReceiptWitness.residual` is the sole Boolean-mask/frame semantics.  The exact
runtime reindexing already exists in `Assurance.SemanticReceiptRuntimeCodec`.
This module does not introduce another receipt relation.  It compiles the
existing `ConstraintKind` declaration into the existing `Air` term language,
passes that system through the existing proved `emit`, and exposes one
first-order JSON artifact for the Rust descriptor reader.

The artifact is parameterized by a positive state width because the current
Rust receipt uses vectors while `ConstraintDescriptor` is fixed-shape.  A
deployment chooses a width in Lean and emits that instance; Rust does not
construct its gates or residual schedule.
-/
import Assurance.SemanticReceiptRuntimeCodec
import Compiler.EmitSerialize
import Theory.IndexedProgram

namespace Minidregg.Compiler.SemanticTurnReceiptDescriptor

open Lean (Json toJson)
open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.SemanticTurnReceipt
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ReactiveReceipt
open Minidregg.Theory.TypedAuthorization

/-! ## 1. The declaration and its exact first-order tag codecs -/

/-- The only deployment choice: a nonempty fixed semantic-state width. -/
structure Declaration where
  keyCount : Nat
  keyCount_pos : 0 < keyCount

/-- The generated descriptor's original-variable space is the already-proved
bound runtime word: sixteen header-binding cells followed by three cells/key. -/
abbrev Declaration.WireIx (decl : Declaration) := Fin (16 + decl.keyCount * 3)

/-- ABI version authored on the Lean side. -/
def semanticReceiptVersion : Nat := 1

/-- Numeric tag of an existing Lean resource constructor. -/
def resourceKindTag : ResourceKind → UInt8
  | .object => 1
  | .account => 2
  | .program => 3

/-- Exact one-byte resource-kind codec for the existing Lean constructors. -/
def resourceKindCodec : LawfulCodec ResourceKind where
  encode kind := [resourceKindTag kind]
  decode
    | [1] => some .object
    | [2] => some .account
    | [3] => some .program
    | _ => none
  decode_encode := by intro kind; cases kind <;> rfl

/-- Existential packaging of the existing kind-indexed `Verb`; this erases only
the index for a first-order wire tag and does not erase it in the semantics. -/
abbrev SomeVerb := Σ kind : ResourceKind, Verb kind

/-- Numeric tag of an existing dependent Lean verb constructor. -/
def verbTag : SomeVerb → UInt8
  | ⟨.object, .observeObject⟩ => 1
  | ⟨.object, .mutateObject⟩ => 2
  | ⟨.object, .delegateObject⟩ => 3
  | ⟨.account, .observeAccount⟩ => 4
  | ⟨.account, .transfer⟩ => 5
  | ⟨.account, .delegateAccount⟩ => 6
  | ⟨.program, .observeProgram⟩ => 7
  | ⟨.program, .installProgram⟩ => 8
  | ⟨.program, .delegateProgram⟩ => 9

/-- Exact one-byte verb codec projected from the existing dependent constructors. -/
def verbCodec : LawfulCodec SomeVerb where
  encode verb := [verbTag verb]
  decode
    | [1] => some ⟨.object, .observeObject⟩
    | [2] => some ⟨.object, .mutateObject⟩
    | [3] => some ⟨.object, .delegateObject⟩
    | [4] => some ⟨.account, .observeAccount⟩
    | [5] => some ⟨.account, .transfer⟩
    | [6] => some ⟨.account, .delegateAccount⟩
    | [7] => some ⟨.program, .observeProgram⟩
    | [8] => some ⟨.program, .installProgram⟩
    | [9] => some ⟨.program, .delegateProgram⟩
    | _ => none
  decode_encode := by
    rintro ⟨kind, verb⟩
    cases verb <;> rfl

/-- First-order names of the three authorization constructors that actually
exist in `TypedAuthorization.Evidence`.  There is deliberately no threshold
tag: the Lean authorization declaration has no threshold constructor. -/
inductive AuthorizationMode
  | signature
  | proof
  | capability
deriving DecidableEq, Repr

/-- Numeric tag for an authorization constructor that exists in Lean. -/
def AuthorizationMode.tag : AuthorizationMode → UInt8
  | .signature => 1
  | .proof => 2
  | .capability => 3

def authorizationModeCodec : LawfulCodec AuthorizationMode where
  encode mode := [mode.tag]
  decode
    | [1] => some .signature
    | [2] => some .proof
    | [3] => some .capability
    | _ => none
  decode_encode := by intro mode; cases mode <;> rfl

/-! ## 2. Compile the existing semantic declaration to `Air` -/

/-- Existing bound-word coordinate as an `Air` variable.  The index comes from
`boundReceiptIxEquivRuntime`; no second layout calculation appears here. -/
def receiptCell (decl : Declaration) (ix : BoundReceiptIx decl.keyCount) :
    Term (AirSig BabyBear decl.WireIx) :=
  vr (boundReceiptIxEquivRuntime decl.keyCount ix)

/-- Core pre/post/touched coordinate inside the exact bound runtime word. -/
def coreCell (decl : Declaration) (key : Fin decl.keyCount) (slot : ReceiptSlot) :
    Term (AirSig BabyBear decl.WireIx) :=
  receiptCell decl (.inr (key, slot))

/-- Compiler for one constructor of the existing semantic `ConstraintKind`.
This is an arithmetization of `ReceiptWitness.residual`, not a new semantics;
`eval_compileConstraint` below proves the equation constructor-by-constructor. -/
def compileConstraint (decl : Declaration) :
    Fin decl.keyCount × ConstraintKind → Term (AirSig BabyBear decl.WireIx)
  | (key, .boolean) =>
      let touched := coreCell decl key .touched
      mul' touched (add' touched (cst (-1)))
  | (key, .frame) =>
      let pre := coreCell decl key .pre
      let post := coreCell decl key .post
      let touched := coreCell decl key .touched
      mul' (add' (cst 1) (mul' (cst (-1)) touched))
        (add' post (mul' (cst (-1)) pre))

/-- The authoritative finite declaration order: both existing constraint kinds
for every key, key-major.  This order is emitted, never reconstructed in Rust. -/
def declaredConstraints (decl : Declaration) :
    List (Fin decl.keyCount × ConstraintKind) :=
  (List.finRange decl.keyCount).flatMap fun key =>
    [(key, .boolean), (key, .frame)]

/-- Projection of the semantic declaration into the existing AIR system. -/
def system (decl : Declaration) : ConstraintSystem BabyBear decl.WireIx :=
  (declaredConstraints decl).map (compileConstraint decl)

theorem mem_declaredConstraints (decl : Declaration)
    (ix : Fin decl.keyCount × ConstraintKind) :
    ix ∈ declaredConstraints decl := by
  rcases ix with ⟨key, kind⟩
  cases kind <;> simp [declaredConstraints]

@[simp] theorem eval_receiptCell (decl : Declaration)
    (witness : BoundReceiptWitness decl.keyCount BabyBear)
    (ix : BoundReceiptIx decl.keyCount) :
    eval (boundRuntimeEncode witness) (receiptCell decl ix) = witness.encode ix := by
  simp [receiptCell, boundRuntimeEncode]

@[simp] theorem eval_coreCell (decl : Declaration)
    (witness : BoundReceiptWitness decl.keyCount BabyBear)
    (key : Fin decl.keyCount) (slot : ReceiptSlot) :
    eval (boundRuntimeEncode witness) (coreCell decl key slot) =
      witness.core.encode (key, slot) := by
  simp [coreCell, BoundReceiptWitness.encode]

/-- The compiler reads each generated AIR term as the pre-existing semantic
residual on the exact runtime encoding. -/
theorem eval_compileConstraint (decl : Declaration)
    (witness : BoundReceiptWitness decl.keyCount BabyBear)
    (ix : Fin decl.keyCount × ConstraintKind) :
    eval (boundRuntimeEncode witness) (compileConstraint decl ix) =
      witness.core.residual ix := by
  rcases ix with ⟨key, kind⟩
  cases kind <;>
    simp [compileConstraint, ReceiptWitness.encode,
      ReceiptWitness.residual, sub_eq_add_neg]

/-- The generated AIR system is exactly the existing semantic receipt
satisfaction judgment, with no extra or missing constraint. -/
theorem systemAccepts_iff (decl : Declaration)
    (witness : BoundReceiptWitness decl.keyCount BabyBear) :
    Minidregg.Compiler.systemAccepts (boundRuntimeEncode witness) (system decl) ↔
      witness.core.Satisfies := by
  constructor
  · intro h ix
    have hmem : compileConstraint decl ix ∈ system decl :=
      List.mem_map.mpr ⟨ix, mem_declaredConstraints decl ix, rfl⟩
    have haccept := h _ hmem
    simpa [accepts, eval_compileConstraint] using haccept
  · intro h term hmem
    obtain ⟨ix, -, rfl⟩ := List.mem_map.mp hmem
    show accepts (boundRuntimeEncode witness) (compileConstraint decl ix)
    simpa [accepts, eval_compileConstraint] using h ix

/-! ## 3. Existing emit path and end-to-end semantic theorem -/

/-- The only descriptor: the declared system passed through the repository's
existing flatten/emit path.  The 16 binding cells are the public prefix; the
semantic core cells remain witness coordinates. -/
def descriptor (decl : Declaration) : ConstraintDescriptor BabyBear :=
  emit Fin.val 16 (16 + decl.keyCount * 3) (system decl)

theorem descriptor_wellFormed (decl : Declaration) :
    (descriptor decl).WellFormed := by
  apply emit_wellFormed Fin.val 16 (16 + decl.keyCount * 3)
  · omega
  · intro index
    exact index.isLt

/-- **Authority-inversion theorem.** Satisfying the emitted first-order
descriptor at the exact generated word is equivalent to the authoritative
Lean semantic receipt relation. -/
theorem descriptor_accepts_iff (decl : Declaration)
    (witness : BoundReceiptWitness decl.keyCount BabyBear) :
    (∃ wireValues : Nat → BabyBear,
        (∀ index : decl.WireIx,
          wireValues index.val = boundRuntimeEncode witness index) ∧
        descriptorHolds (descriptor decl) wireValues) ↔
      witness.core.Satisfies := by
  rw [descriptor, emit_accepts_iff_fin, systemAccepts_iff]

/-- Equivalent formulation at the accumulated bound-receipt relation itself. -/
theorem descriptor_accepts_iff_boundRelation (decl : Declaration)
    (witness : BoundReceiptWitness decl.keyCount BabyBear) :
    (∃ wireValues : Nat → BabyBear,
        (∀ index : decl.WireIx,
          wireValues index.val = boundRuntimeEncode witness index) ∧
        descriptorHolds (descriptor decl) wireValues) ↔
      BoundSemanticReceiptRelation witness.encode := by
  rw [descriptor_accepts_iff]
  constructor
  · intro h
    exact ⟨witness, h, rfl⟩
  · rintro ⟨other, hother, hencode⟩
    have : other = witness := by
      apply boundRuntimeEncode_injective
      funext index
      have heq := congrFun hencode.symm
        ((boundReceiptIxEquivRuntime decl.keyCount).symm index)
      simpa [boundRuntimeEncode] using heq
    simpa [this] using hother

/-! ## 4. Projection from the actual typed semantic turn -/

section CommittedProjection

universe uEffect uDisclosure

variable
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {Effect : Type uEffect} {Disclosure : Type uDisclosure}
    {stateCommitment : StateCommitment (Fin n) BabyBear}
    {effectSemantics : EffectSemantics (Fin n) BabyBear Effect}
    {disclosurePolicy : DisclosurePolicy Disclosure}
    {request : Request kind} {pre : Store (Fin n) BabyBear}

/-- The descriptor witness is a projection of `CommittedTurn.coreClaim`; only
the already-computed typed-header binding cells are added. -/
def ofCommittedTurn (binding : BindingIx → BabyBear)
    (commit : CommittedTurn portal authState request stateCommitment
      effectSemantics disclosurePolicy pre) :
    BoundReceiptWitness n BabyBear where
  binding := binding
  core := commit.coreClaim.witness

@[simp] theorem ofCommittedTurn_core (binding : BindingIx → BabyBear)
    (commit : CommittedTurn portal authState request stateCommitment
      effectSemantics disclosurePolicy pre) :
    (ofCommittedTurn binding commit).core = commit.coreClaim.witness :=
  rfl

/-- Every typed committed turn projects to a satisfying descriptor witness by
the existing `coreClaim.valid`; no handwritten downstream equation schedule is
authoritative. -/
theorem committedTurn_descriptor_accepts (decl : Declaration)
    (hwidth : decl.keyCount = n)
    (binding : BindingIx → BabyBear)
    (commit : CommittedTurn portal authState request stateCommitment
      effectSemantics disclosurePolicy pre) :
    ∃ wireValues : Nat → BabyBear,
      (∀ index : decl.WireIx,
        wireValues index.val = boundRuntimeEncode
          (hwidth ▸ ofCommittedTurn binding commit) index) ∧
      descriptorHolds (descriptor decl) wireValues := by
  apply (descriptor_accepts_iff decl (hwidth ▸ ofCommittedTurn binding commit)).mpr
  subst n
  exact commit.coreClaim.valid

end CommittedProjection

/-! ## 5. Exact generated surface for downstream unverified compute -/

/-- The first-order artifact contains all layout numbers downstream code
previously reconstructed and the actual Lean-emitted descriptor it executes.
It is generated glue into unverified compute, not a Rust semantic model and not
the subject of a Rust-refinement theorem. -/
structure RustArtifactSurface where
  semanticVersion : Nat
  fieldModulus : Nat
  bindingBytes : Nat
  bindingCellBits : Nat
  bindingCells : Nat
  coreOffset : Nat
  keyCount : Nat
  keyStride : Nat
  slotNames : List String
  residualNames : List String
  constraintDescriptor : ConstraintDescriptor BabyBear

/-- Projection of one Lean declaration to the complete Rust-facing surface. -/
def rustArtifact (decl : Declaration) : RustArtifactSurface where
  semanticVersion := semanticReceiptVersion
  fieldModulus := babyBearP
  bindingBytes := 32
  bindingCellBits := 16
  bindingCells := 16
  coreOffset := 16
  keyCount := decl.keyCount
  keyStride := 3
  slotNames := ["pre", "post", "touched"]
  residualNames := ["boolean", "frame"]
  constraintDescriptor := descriptor decl

def taggedValue (name : String) (tag : Nat) : Json :=
  Json.mkObj [("name", Json.str name), ("tag", toJson tag)]

def resourceKindName : ResourceKind → String
  | .object => "object"
  | .account => "account"
  | .program => "program"

def verbName : SomeVerb → String
  | ⟨.object, .observeObject⟩ => "observe_object"
  | ⟨.object, .mutateObject⟩ => "mutate_object"
  | ⟨.object, .delegateObject⟩ => "delegate_object"
  | ⟨.account, .observeAccount⟩ => "observe_account"
  | ⟨.account, .transfer⟩ => "transfer"
  | ⟨.account, .delegateAccount⟩ => "delegate_account"
  | ⟨.program, .observeProgram⟩ => "observe_program"
  | ⟨.program, .installProgram⟩ => "install_program"
  | ⟨.program, .delegateProgram⟩ => "delegate_program"

def someVerbKind : SomeVerb → ResourceKind
  | ⟨kind, _⟩ => kind

/-- The erased verb ABI retains the constructor's original dependent kind. -/
def taggedVerbValue (verb : SomeVerb) : Json :=
  Json.mkObj
    [ ("name", Json.str (verbName verb)),
      ("tag", toJson (verbTag verb).toNat),
      ("resourceKindTag", toJson (resourceKindTag (someVerbKind verb)).toNat) ]

def AuthorizationMode.name : AuthorizationMode → String
  | .signature => "signature"
  | .proof => "proof"
  | .capability => "capability"

def allResourceKinds : List ResourceKind := [.object, .account, .program]

def allVerbs : List SomeVerb :=
  [ ⟨.object, .observeObject⟩, ⟨.object, .mutateObject⟩,
    ⟨.object, .delegateObject⟩, ⟨.account, .observeAccount⟩,
    ⟨.account, .transfer⟩, ⟨.account, .delegateAccount⟩,
    ⟨.program, .observeProgram⟩, ⟨.program, .installProgram⟩,
    ⟨.program, .delegateProgram⟩ ]

def allAuthorizationModes : List AuthorizationMode :=
  [.signature, .proof, .capability]

def rustArtifactToJson (decl : Declaration) : Json :=
  let artifact := rustArtifact decl
  Json.mkObj
    [ ("schema", Json.str "minidregg/semantic-turn-receipt-descriptor/v1"),
      ("semanticVersion", toJson artifact.semanticVersion),
      ("fieldModulus", toJson artifact.fieldModulus),
      ("bindingBytes", toJson artifact.bindingBytes),
      ("bindingCellBits", toJson artifact.bindingCellBits),
      ("bindingCells", toJson artifact.bindingCells),
      ("coreOffset", toJson artifact.coreOffset),
      ("keyCount", toJson artifact.keyCount),
      ("keyStride", toJson artifact.keyStride),
      ("slots", Json.arr
        ([taggedValue "pre" 0, taggedValue "post" 1,
          taggedValue "touched" 2] : List Json).toArray),
      ("residuals", Json.arr
        ([taggedValue "boolean" 0, taggedValue "frame" 1] : List Json).toArray),
      ("resourceKinds", Json.arr
        (allResourceKinds.map fun kind =>
          taggedValue (resourceKindName kind) (resourceKindTag kind).toNat).toArray),
      ("verbs", Json.arr
        (allVerbs.map taggedVerbValue).toArray),
      ("authorizationModes", Json.arr
        (allAuthorizationModes.map fun mode =>
          taggedValue mode.name mode.tag.toNat).toArray),
      ("descriptor", descriptorToJson artifact.constraintDescriptor) ]

/-- Write one generated deployment artifact for generic downstream readers.
There is intentionally no
hard-coded `#eval`: selecting the deployed width and path is an integration
decision, while this module remains a reusable Lean declaration projection. -/
def writeRustArtifact (path : System.FilePath) (decl : Declaration) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path ((rustArtifactToJson decl).pretty ++ "\n")

/-! ## 6. Computed shape witnesses and negative teeth -/

def fourKeyDeclaration : Declaration := ⟨4, by decide⟩

example : (rustArtifact fourKeyDeclaration).constraintDescriptor.nPublic = 16 := rfl

example : (rustArtifact fourKeyDeclaration).constraintDescriptor.nVars = 28 := by decide

example : (rustArtifact fourKeyDeclaration).constraintDescriptor.zeros.length = 8 := by decide

/-- A native `touched = 0` claim cannot change the corresponding post cell in
the generated descriptor: this is decided on the authoritative semantic
relation and transferred through `descriptor_accepts_iff`. -/
def ghostCore : ReceiptWitness (Fin 1) BabyBear where
  pre := fun _ => 1
  post := fun _ => 2
  touched := fun _ => 0

def ghostBound : BoundReceiptWitness 1 BabyBear where
  binding := fun _ => 1
  core := ghostCore

def oneKeyDeclaration : Declaration := ⟨1, by decide⟩

example : ¬ ∃ wireValues : Nat → BabyBear,
    (∀ index : oneKeyDeclaration.WireIx,
      wireValues index.val = boundRuntimeEncode ghostBound index) ∧
    descriptorHolds (descriptor oneKeyDeclaration) wireValues := by
  intro hex
  have h := (descriptor_accepts_iff oneKeyDeclaration ghostBound).mp hex
  have hframe := h (⟨0, by decide⟩, .frame)
  norm_num [ghostBound, ghostCore, ReceiptWitness.residual] at hframe

#print axioms descriptor_accepts_iff_boundRelation
#print axioms committedTurn_descriptor_accepts

end Minidregg.Compiler.SemanticTurnReceiptDescriptor
