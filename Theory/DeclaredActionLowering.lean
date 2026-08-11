/-
# Theory.DeclaredActionLowering -- one first-order action batch, one semantic patch

This module closes the declaration half of the legacy-effect migration without
introducing an executor callback.  A batch is closed data: `create`, guarded
`write`, and exact account `move`.  Its lawful bytes, typed writes, footprint,
full-width balance postings, eager nullifier, request commitment, and resource
charge are all projections of that one value.

`run` is only the guard checker for the same ordered checked writes used by the
canonical `CellState.Patch`; it does not compute an alternative post-state.
`Accepted` retains the equality between that checker result and the sole
validator-minted post.  Thus a host may submit bytes and authority evidence,
but cannot substitute a callback or a separately interpreted replacement.

The state schema is deliberately the deployed `DeclaredTurn.effectSchema`.
This is a bounded lowering for that effect vocabulary, not a claim that every
future language can be encoded by these three constructors.
-/
import Theory.AcceptedCellEffect
import Theory.DeclaredTurn
import Theory.ResourceCost

namespace Minidregg.Theory.DeclaredActionLowering

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

local instance fieldValueDecidableEq
    (key : DeclaredTurn.effectSchema.{0, 0}.Field) :
    DecidableEq (DeclaredTurn.effectSchema.{0, 0}.FieldType key) :=
  inferInstanceAs (DecidableEq Int)

/-! ## Closed action syntax and exact checked writes -/

/-- One action in the bounded declared language.  `move` retains both exact
representation-level expected values; absence and a stored zero are therefore
not conflated at the lowering boundary. -/
inductive Action where
  | create (key : StateKey) (initial : Int)
  | write (key : StateKey) (expected : Option Int) (replacement : Int)
  | move (source destination : ResourceId .account) (resource : Digest)
      (sourceExpected destinationExpected : Option Int) (amount : Int)
  deriving DecidableEq, Repr

/-- The one guarded mutation carrier. -/
structure CheckedWrite where
  key : StateKey
  expected : Option Int
  replacement : Option Int
  deriving DecidableEq, Repr

def Action.checkedWrites : Action -> List CheckedWrite
  | .create key initial =>
      [{ key := key, expected := none, replacement := some initial }]
  | .write key expected replacement =>
      [{ key := key, expected := expected, replacement := some replacement }]
  | .move source destination resource sourceExpected destinationExpected amount =>
      [{ key := .accountBalance source resource
         expected := sourceExpected
         replacement := some (sourceExpected.getD 0 - amount) },
       { key := .accountBalance destination resource
         expected := destinationExpected
         replacement := some (destinationExpected.getD 0 + amount) }]

def CheckedWrite.toFieldWrite (write : CheckedWrite) :
    FieldWrite DeclaredTurn.effectSchema.{0, 0} where
  field := write.key
  value := write.replacement

/-- Guard and application are one ordered fold over `CheckedWrite`.  The
successful branch uses `FieldStore.assign`, exactly as `applyFieldWrites` does. -/
def runCheckedWrites : List CheckedWrite ->
    FieldStore DeclaredTurn.effectSchema.{0, 0} ->
      Option (FieldStore DeclaredTurn.effectSchema.{0, 0})
  | [], fields => some fields
  | write :: rest, fields =>
      if fields write.key = write.expected then
        runCheckedWrites rest (fields.assign write.key write.replacement)
      else none

/-- A full-width posting is derived only for a move. -/
structure Posting where
  account : ResourceId .account
  resource : Digest
  amount : Int
  deriving DecidableEq, Repr

def Action.postings : Action -> List Posting
  | .move source destination resource _ _ amount =>
      [{ account := source, resource := resource, amount := -amount },
       { account := destination, resource := resource, amount := amount }]
  | _ => []

def postingSum (postings : List Posting) (resource : Digest) : Int :=
  (postings.map fun posting =>
    if posting.resource = resource then posting.amount else 0).sum

@[simp] theorem Action.postingSum_zero (action : Action) (resource : Digest) :
    postingSum action.postings resource = 0 := by
  cases action with
  | create => simp [Action.postings, postingSum]
  | write => simp [Action.postings, postingSum]
  | move source destination moved sourceExpected destinationExpected amount =>
      by_cases same : moved = resource
      · simp [Action.postings, postingSum, same]
      · simp [Action.postings, postingSum, same]

/-! ## Lawful first-order bytes -/

def decodeInt : Nat -> Int
  | n => if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)

@[simp] theorem decodeInt_encodeInt (value : Int) :
    decodeInt (EffectDeclaration.encodeInt value) = value := by
  cases value with
  | ofNat value => simp [decodeInt, EffectDeclaration.encodeInt]
  | negSucc value => simp [decodeInt, EffectDeclaration.encodeInt]; omega

def keyCode : StateKey -> Nat
  | .objectField object field =>
      Nat.pair 0 (Nat.pair object.value field.value)
  | .accountBalance account resource =>
      Nat.pair 1 (Nat.pair account.value resource.value)
  | .programCode program => Nat.pair 2 program.value

def keyOfCode (code : Nat) : Option StateKey :=
  let tagged := Nat.unpair code
  match tagged.1 with
  | 0 =>
      let parts := Nat.unpair tagged.2
      some (.objectField ⟨parts.1⟩ ⟨parts.2⟩)
  | 1 =>
      let parts := Nat.unpair tagged.2
      some (.accountBalance ⟨parts.1⟩ ⟨parts.2⟩)
  | 2 => some (.programCode ⟨tagged.2⟩)
  | _ => none

@[simp] theorem keyOfCode_keyCode (key : StateKey) :
    keyOfCode (keyCode key) = some key := by
  cases key <;> simp [keyCode, keyOfCode]

def optionIntCode : Option Int -> Nat
  | none => 0
  | some value => EffectDeclaration.encodeInt value + 1

def optionIntOfCode : Nat -> Option (Option Int)
  | 0 => some none
  | code + 1 => some (some (decodeInt code))

@[simp] theorem optionIntOfCode_optionIntCode (value : Option Int) :
    optionIntOfCode (optionIntCode value) = some value := by
  cases value <;> simp [optionIntCode, optionIntOfCode]

def Action.code : Action -> Nat
  | .create key initial =>
      Nat.pair 0 (Nat.pair (keyCode key) (EffectDeclaration.encodeInt initial))
  | .write key expected replacement =>
      Nat.pair 1 (Nat.pair (keyCode key)
        (Nat.pair (optionIntCode expected)
          (EffectDeclaration.encodeInt replacement)))
  | .move source destination resource sourceExpected destinationExpected amount =>
      Nat.pair 2
        (Nat.pair source.value
          (Nat.pair destination.value
            (Nat.pair resource.value
              (Nat.pair (optionIntCode sourceExpected)
                (Nat.pair (optionIntCode destinationExpected)
                  (EffectDeclaration.encodeInt amount))))))

def actionOfCode (code : Nat) : Option Action := do
  let tagged := Nat.unpair code
  match tagged.1 with
  | 0 =>
      let parts := Nat.unpair tagged.2
      let key <- keyOfCode parts.1
      pure (.create key (decodeInt parts.2))
  | 1 =>
      let keyRest := Nat.unpair tagged.2
      let expectedReplacement := Nat.unpair keyRest.2
      let key <- keyOfCode keyRest.1
      let expected <- optionIntOfCode expectedReplacement.1
      pure (.write key expected (decodeInt expectedReplacement.2))
  | 2 =>
      let sourceRest := Nat.unpair tagged.2
      let destinationRest := Nat.unpair sourceRest.2
      let resourceRest := Nat.unpair destinationRest.2
      let sourceExpectedRest := Nat.unpair resourceRest.2
      let destinationExpectedAmount := Nat.unpair sourceExpectedRest.2
      let sourceExpected <- optionIntOfCode sourceExpectedRest.1
      let destinationExpected <- optionIntOfCode destinationExpectedAmount.1
      pure (.move ⟨sourceRest.1⟩ ⟨destinationRest.1⟩ ⟨resourceRest.1⟩
        sourceExpected destinationExpected (decodeInt destinationExpectedAmount.2))
  | _ => none

@[simp] theorem actionOfCode_code (action : Action) :
    actionOfCode action.code = some action := by
  cases action <;> simp [Action.code, actionOfCode]

def actionsCode : List Action -> Nat
  | [] => 0
  | action :: rest => Nat.pair action.code (actionsCode rest) + 1

def actionsOfCode : Nat -> Option (List Action)
  | 0 => some []
  | code + 1 => do
      let parts := Nat.unpair code
      let action <- actionOfCode parts.1
      let rest <- actionsOfCode parts.2
      pure (action :: rest)
termination_by code => code
decreasing_by exact Nat.lt_succ_of_le (Nat.unpair_right_le _)

@[simp] theorem actionsOfCode_actionsCode (actions : List Action) :
    actionsOfCode (actionsCode actions) = some actions := by
  induction actions with
  | nil => simp [actionsCode, actionsOfCode]
  | cons action rest induction =>
      simp [actionsCode, actionsOfCode, induction]

def resourceKindTag : ResourceKind -> Nat
  | .object => 0
  | .account => 1
  | .program => 2

/-- One exact authority target owns a batch.  Its bytes include that target,
kind, pre-root, nonce, and the complete ordered action list. -/
structure Declaration {kind : ResourceKind} (target : ResourceId kind) where
  schemaVersion : Nat
  expectedPreRoot : Digest
  nonce : Nat
  actions : List Action
  deriving DecidableEq, Repr

def Declaration.code {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : Nat :=
  Nat.pair (resourceKindTag kind)
    (Nat.pair target.value
      (Nat.pair declaration.schemaVersion
        (Nat.pair declaration.expectedPreRoot.value
          (Nat.pair declaration.nonce (actionsCode declaration.actions)))))

def declarationOfCode {kind : ResourceKind} (target : ResourceId kind)
    (code : Nat) : Option (Declaration target) := do
  let kindRest := Nat.unpair code
  let targetRest := Nat.unpair kindRest.2
  if kindRest.1 != resourceKindTag kind then none
  else if targetRest.1 != target.value then none
  else
    let schemaRest := Nat.unpair targetRest.2
    let rootRest := Nat.unpair schemaRest.2
    let nonceActions := Nat.unpair rootRest.2
    let actions <- actionsOfCode nonceActions.2
    pure
      { schemaVersion := schemaRest.1
        expectedPreRoot := ⟨rootRest.1⟩
        nonce := nonceActions.1
        actions := actions }

@[simp] theorem declarationOfCode_code {kind : ResourceKind}
    {target : ResourceId kind} (declaration : Declaration target) :
    declarationOfCode target declaration.code = some declaration := by
  cases kind <;> simp [Declaration.code, declarationOfCode, resourceKindTag]

def declarationCodec {kind : ResourceKind} (target : ResourceId kind) :
    LawfulCodec (Declaration target) where
  encode := fun declaration => List.replicate (declaration.code + 1) 0
  decode := fun bytes =>
    if bytes.all fun byte => byte == 0 then
      declarationOfCode target (bytes.length - 1)
    else none
  decode_encode := by
    intro declaration
    simp only [List.all_eq_true, List.mem_replicate, beq_iff_eq,
      forall_eq, List.length_replicate, Nat.add_sub_cancel]
    simpa using declarationOfCode_code declaration

/-! ## The sole semantic lowering -/

def Declaration.checkedWrites {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : List CheckedWrite :=
  declaration.actions.flatMap Action.checkedWrites

def Declaration.fieldWrites {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) :
    List (FieldWrite DeclaredTurn.effectSchema.{0, 0}) :=
  declaration.checkedWrites.map CheckedWrite.toFieldWrite

def Declaration.patch {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) :
    Patch DeclaredTurn.effectSchema.{0, 0} Digest where
  expectedPreRoot := declaration.expectedPreRoot
  fieldWrites := declaration.fieldWrites
  resourceWrites := []
  fieldFootprint := (declaration.fieldWrites.map FieldWrite.field).toFinset
  resourceFootprint := ∅

def Declaration.run {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target)
    (fields : FieldStore DeclaredTurn.effectSchema.{0, 0}) :
    Option (FieldStore DeclaredTurn.effectSchema.{0, 0}) :=
  runCheckedWrites declaration.checkedWrites fields

def Declaration.postings {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : List Posting :=
  declaration.actions.flatMap Action.postings

theorem postingSum_append (left right : List Posting) (resource : Digest) :
    postingSum (left ++ right) resource =
      postingSum left resource + postingSum right resource := by
  simp [postingSum, List.map_append, List.sum_append]

/-- Every complete resource namespace is conserved by construction. -/
theorem Declaration.postingSum_zero {kind : ResourceKind}
    {target : ResourceId kind} (declaration : Declaration target)
    (resource : Digest) :
    postingSum declaration.postings resource = 0 := by
  change postingSum (declaration.actions.flatMap Action.postings) resource = 0
  induction declaration.actions with
  | nil => rfl
  | cons action rest induction =>
      rw [List.flatMap_cons, postingSum_append,
        Action.postingSum_zero, induction, add_zero]

/-- Domain-separated model commitment to the complete lawful bytes. -/
def digestDeclaration {kind : ResourceKind} {target : ResourceId kind}
    (domain : Nat) (declaration : Declaration target) : Digest :=
  ⟨Nat.pair domain declaration.code⟩

def argsDigest {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : Digest :=
  digestDeclaration 30 declaration

def effectDigest {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : Digest :=
  digestDeclaration 31 declaration

/-- Every charged coordinate is determined from the same declaration. -/
def exactCharge {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : Charge :=
  fun lane =>
    match lane with
    | .incidences => 1
    | .turnBytes => (declarationCodec target).encode declaration |>.length
    | .memoryTouches =>
        (declaration.patch : Patch DeclaredTurn.effectSchema.{0, 0} Digest)
          |>.fieldFootprint.card
    | .storageBytes => declaration.fieldWrites.length
    | .sideEffectCount => declaration.actions.length
    | .feeDebit => declaration.actions.foldl (fun total action =>
        match action with
        | .move _ _ _ _ _ amount => total + amount.natAbs
        | _ => total) 0
    | _ => 0

def unitCodec : LawfulCodec Unit where
  encode := fun _ => []
  decode := fun bytes => if bytes = [] then some () else none
  decode_encode := by simp

def family {kind : ResourceKind} (target : ResourceId kind)
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest} :
    SemanticEffectFamily DeclaredTurn.effectSchema.{0, 0} M Nat where
  Declaration := Declaration target
  declarationCodec := declarationCodec target
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun _ _ => Unit
  effectDigest := effectDigest
  patch := fun declaration _ => declaration.patch
  nullifier := fun declaration _ => some declaration.nonce
  Release := fun _ _ => PEmpty
  DeclassificationAuthority := fun _ _ => PEmpty
  ReleaseAuthorization := fun _ _ release => release.elim
  DisclosureAllowed := fun _ _ decision => decision = .sealed

/-! ## Complete request and accepted lowering -/

structure RequestContext where
  domain : Digest
  semantics : Digest
  federation : FederationId
  subject : SubjectId
  subjectKeyEpoch : Epoch
  height : Height
  policyId : PolicyId
  policyEpoch : Epoch

def RequestContext.request {kind : ResourceKind} {target : ResourceId kind}
    (context : RequestContext) (declaration : Declaration target) : Request kind where
  domain := context.domain
  semantics := context.semantics
  federation := context.federation
  subject := context.subject
  subjectKeyEpoch := context.subjectKeyEpoch
  target := target
  verb := match kind with
    | .object => .mutateObject
    | .account => .transfer
    | .program => .installProgram
  argsDigest := argsDigest declaration
  effectsDigest := effectDigest declaration
  nonce := declaration.nonce
  height := context.height
  preStateRoot := declaration.expectedPreRoot
  policyId := context.policyId
  policyEpoch := context.policyEpoch
  cost := exactCharge declaration .feeDebit

/-- Guard success is tied to the exact sparse pre-state and to the same field
writes installed by the family patch. -/
structure ValidAt {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    (pre : Materialized M) (declaration : Declaration target) : Prop where
  rootExact : declaration.expectedPreRoot = pre.root
  guardsAndPost : declaration.run pre.logical.fields =
    some (applyFieldWrites declaration.fieldWrites pre.logical.fields)

theorem patch_validated {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {pre : Materialized M} {declaration : Declaration target}
    (valid : ValidAt pre declaration) :
    Nonempty (ValidatedPatch M pre declaration.patch) := by
  have accepted : ∃ validated : ValidatedPatch M pre declaration.patch,
      validate M pre declaration.patch = ValidationOutcome.accepted validated := by
    unfold validate
    have rootExact : declaration.patch.expectedPreRoot = pre.root := by
      simpa [Declaration.patch] using valid.rootExact
    rw [dif_pos rootExact]
    rw [dif_pos (show declaration.patch.fieldFootprint =
      declaration.patch.namedFields from rfl)]
    rw [dif_pos (show declaration.patch.resourceFootprint =
      declaration.patch.namedResources from rfl)]
    exact ⟨_, rfl⟩
  exact ⟨accepted.choose⟩

/-- Positive lowering carrier.  It adds only the guard/post equality that the
generic accepted-effect type intentionally leaves family-specific. -/
structure Accepted {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    (portal : Portal) (authState : AuthState)
    (context : RequestContext) (pre : Materialized M)
    (declaration : Declaration target) : Type where
  valid : ValidAt pre declaration
  cellEffect : AcceptedCellEffect (portal := portal) (authState := authState)
    (family target) (context.request declaration) pre declaration ()

noncomputable def accept {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M}
    {declaration : Declaration target}
    (authorization : Authorized portal authState (context.request declaration))
    (valid : ValidAt pre declaration) :
    Accepted portal authState context pre declaration where
  valid := valid
  cellEffect :=
    { authorization := authorization
      effectsDigestBound := rfl
      preRootBound := valid.rootExact.trans rfl
      modeEvidence := ()
      validated := Classical.choice (patch_validated valid)
      disclosure := .sealed
      disclosureAllowed := rfl }

theorem no_accepted_of_guard_mismatch {kind : ResourceKind}
    {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : Declaration target}
    (mismatch : declaration.run pre.logical.fields = none) :
    IsEmpty (Accepted portal authState context pre declaration) :=
  ⟨fun accepted => by
    have exactPost := accepted.valid.guardsAndPost
    rw [mismatch] at exactPost
    simp at exactPost⟩

theorem no_cellEffect_of_wrong_digest {kind : ResourceKind}
    {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState}
    {pre : Materialized M} {declaration : Declaration target}
    (request : Request kind)
    (wrong : request.effectsDigest ≠ effectDigest declaration) :
    IsEmpty (AcceptedCellEffect (portal := portal) (authState := authState)
      (family target) request pre declaration ()) :=
  ⟨fun accepted => wrong accepted.effectsDigestBound⟩

theorem no_cellEffect_of_stale_root {kind : ResourceKind}
    {target : ResourceId kind}
    {M : Materializer DeclaredTurn.effectSchema.{0, 0} Digest}
    {portal : Portal} {authState : AuthState}
    {pre : Materialized M} {declaration : Declaration target}
    (request : Request kind) (stale : request.preStateRoot ≠ pre.root) :
    IsEmpty (AcceptedCellEffect (portal := portal) (authState := authState)
      (family target) request pre declaration ()) :=
  ⟨fun accepted => stale accepted.preRootBound⟩

/-! ## A narrow, checked legacy correspondence -/

/-- A legacy account move lowers to the same two full-width postings.  This is
the meaningful old path this bounded language subsumes; it does not claim an
adapter for arbitrary host languages. -/
def ofLegacyMove (source destination : ResourceId .account) (resource : Digest)
    (sourceExpected destinationExpected : Option Int) (amount : Int) : Action :=
  .move source destination resource sourceExpected destinationExpected amount

@[simp] theorem ofLegacyMove_postings
    (source destination : ResourceId .account) (resource : Digest)
    (sourceExpected destinationExpected : Option Int) (amount : Int) :
    (ofLegacyMove source destination resource sourceExpected
      destinationExpected amount).postings =
      [{ account := source, resource := resource, amount := -amount },
       { account := destination, resource := resource, amount := amount }] := rfl

end Minidregg.Theory.DeclaredActionLowering
