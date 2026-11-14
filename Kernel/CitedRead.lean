/-
# `Kernel/CitedRead.lean` — the cited read, DECLARED (registry code 9, JSON `fieldRead`)

A turn reads a declared cell it does not write by citing fields and the values it read. The
check is `Theory.PlanBinding.Footprint.admitAll` at the declared-effect layout: currency is by
value, the refusal is the whole stale list (`citedMoved`), and nothing about the cell's root is
signed.

This file is the whole effect: its operation and codec, its refusals and their detail, its
semantics (`citedRead`), what a law sees of the cited cell (`citedProject`), its JSON face and
its display, and the one declaration `citedEffect` that the registry binds at code 9
(`Kernel/ResourceEffectRegistry.lean`). No function outside this file names it: the controller,
the compilers and the Host reach it through `Payload.registered`.

It pins no root, writes nothing and advances no ratchet: the declaration commutes (so the
dispatcher never compares the signed root), emits the empty patch and has no rotate. Its verb is
the kind's observe verb, so its one authorization is its observation.
-/
module

public import Kernel.ResourceEffect
public import Theory.PlanBinding
public import Kernel.ResourceObservationAdmission

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic

@[expose] public section

namespace Minidregg.Kernel.DeclaredResourceController
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Effects
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

/-- One cited read of a declared cell: a field's key and the value the signer read there
(`none` = the field was absent). A list of them is the signed footprint of a cited read (`Theory.PlanBinding.Footprint` at the declared-effect layout, `citedFootprint`). -/
abbrev FieldRead := EffectDeclaration.StateKey × Option Int

def fieldReadStream : StreamCodec FieldRead :=
  StreamCodec.product DeclaredEffectCell.stateKeyStream (StreamCodec.option IntStream.intStream)

/-! ## The footprint

A turn reads a declared cell it does not write by citing fields and the values it read. The
check is `Theory.PlanBinding.Footprint.admitAll` at the declared-effect layout: currency is by
value, the refusal is the whole stale list (`citedMoved`), and nothing about the cell's root is signed. -/

/-- The cited reads as a `PlanBinding` footprint. -/
def citedFootprint (reads : List FieldRead) : PlanBinding.Footprint EffectDeclaration.effectLayout :=
  reads.map fun read => ⟨read.1.address, read.2⟩

/-- The cited fields whose value the store no longer holds, in the order cited. -/
def citedMoved (store : Store EffectDeclaration.effectLayout) (reads : List FieldRead) :
    List EffectDeclaration.StateKey :=
  (reads.filter fun read => !decide (store read.1.address = read.2)).map (·.1)

/-- **`citedMoved` is exactly the stale set**: a key is named iff it was cited and its value
is not the cited one. -/
theorem mem_citedMoved {store : Store EffectDeclaration.effectLayout} {reads : List FieldRead}
    {key : EffectDeclaration.StateKey} :
    key ∈ citedMoved store reads ↔ ∃ read ∈ reads, read.1 = key ∧ store read.1.address ≠ read.2 := by
  simp only [citedMoved, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨read, ⟨member, stale⟩, rfl⟩
    exact ⟨read, member, rfl, by simpa using stale⟩
  · rintro ⟨read, member, rfl, stale⟩
    exact ⟨read, ⟨member, by simpa using stale⟩, rfl⟩

/-- No cited field is stale exactly when the cited footprint holds at the store
(`PlanBinding.Footprint.Holds`, so `no_toctou_cited` and `moved_back_admits` apply). -/
theorem citedMoved_eq_nil_iff (store : Store EffectDeclaration.effectLayout) (reads : List FieldRead) :
    citedMoved store reads = [] ↔ PlanBinding.Footprint.Holds store (citedFootprint reads) := by
  simp only [citedMoved, citedFootprint, PlanBinding.Footprint.Holds, List.map_eq_nil_iff,
    List.filter_eq_nil_iff, List.mem_map]
  constructor
  · rintro held r ⟨read, member, rfl⟩
    simpa using held read member
  · intro holds read member
    simpa using holds ⟨read.1.address, read.2⟩ ⟨read, member, rfl⟩

/-- Currency is by value: two stores that agree at the cited fields name the same stale fields,
whatever else differs between them (other fields, the blinding, hence the root). -/
theorem citedMoved_congr {s s' : Store EffectDeclaration.effectLayout} {reads : List FieldRead}
    (same : ∀ read ∈ reads, s read.1.address = s' read.1.address) :
    citedMoved s reads = citedMoved s' reads := by
  unfold citedMoved
  congr 1
  apply List.filter_congr
  intro read member
  rw [same read member]

/-! ## Refusals -/

/-- What a cited read refuses with, beside the dispatcher's own header refusals (an account:
`wrongRole`, balances are the Book's; a schema version other than 1: `unsupportedVersion`). -/
inductive CitedRefusal where
  /-- The target carries an audience binding: a cited read has none. -/
  | audience
  /-- The target's capability is not its observe capability. -/
  | observationRequired
  /-- A cited key is not a field of the cell it reads. -/
  | citedKey
  /-- The authority cell does not hold the observe capability. -/
  | observationRejected
  /-- The observe capability's scope does not name every cited field. -/
  | fieldNotNamed
  /-- The footprint does not hold at the loaded cell: every cited field whose value moved, in
  the order cited. It names fields and no value, cited or current; it is returned only after the
  read's observe capability was found to name every cited field (`fieldNotNamed` before it), so
  it tells the requester nothing its grant does not. -/
  | citedStale (moved : List EffectDeclaration.StateKey)
  deriving DecidableEq, Repr

def CitedRefusal.name : CitedRefusal → String
  | .audience => "audience"
  | .observationRequired => "observationRequired"
  | .citedKey => "citedKey"
  | .observationRejected => "observationRejected"
  | .fieldNotNamed => "fieldNotNamed"
  | .citedStale _ => "citedStale"

/-- The codec of a stale refusal's detail: the moved keys. -/
abbrev movedStream : StreamCodec (List EffectDeclaration.StateKey) :=
  StreamCodec.list DeclaredEffectCell.stateKeyStream

/-- A refusal's structured detail: the moved keys of `citedStale`, nothing for the rest. -/
def CitedRefusal.detail : CitedRefusal → List UInt8
  | .citedStale moved => movedStream.encode moved
  | _ => []

/-- The detail of a stale refusal decodes to exactly its moved keys. -/
theorem citedStale_detail (moved : List EffectDeclaration.StateKey) :
    movedStream.toLawful.decode (CitedRefusal.detail (.citedStale moved)) = some moved :=
  movedStream.toLawful.decode_encode moved

/-! ## The read -/

/-- Whether an observe capability's scope names every cited field. A cited read is a read of
each field it names: a read outside the grant would be an equality oracle on that field. -/
def citedScope (snapshot : AuthoritySnapshot) (kind : ResourceKind) (capability : CapabilityId)
    (reads : List FieldRead) : Option CitedRefusal :=
  match CredentialAuthorityState.readCapability snapshot.cell kind capability with
  | none => some .observationRejected
  | some stored =>
      if reads.all fun read =>
          decide (CellField.NamedBy stored.head.scope.fields
            (ResourceObservationAdmission.declaredField read.1))
      then none else some .fieldNotNamed

/-- **The cited read**: the declaration's whole semantics. It is given no root and no schema
version (`EffectCtx` holds neither), returns the loaded store unchanged, and refuses, in order:
an audience binding, a capability that is not the target's observe capability, a key that is
not a field of this cell (`citedKey`), a grant that does not name every cited field
(`citedScope`), and last a footprint that does not hold (`citedStale`, every moved field). -/
def citedRead (snapshot : AuthoritySnapshot) (kind : ResourceKind) (id : Nat)
    (capability : CapabilityId) (observe : Option CapabilityId) (audience : Bool)
    (reads : List FieldRead) (store : Store EffectDeclaration.effectLayout) :
    Except CitedRefusal (Store EffectDeclaration.effectLayout) :=
  if audience then .error .audience
  else if observe ≠ some capability then .error .observationRequired
  else if (reads.all fun read =>
      DeclaredActionLowering.writableKeyCheck (⟨id⟩ : ResourceId kind) read.1) = false then
    .error .citedKey
  else match citedScope snapshot kind capability reads with
    | some reason => .error reason
    | none =>
        if citedMoved store reads = [] then .ok store
        else .error (.citedStale (citedMoved store reads))

/-- **K1/K3, the accepting pole.** An admitted cited read returns the loaded store itself (it
writes nothing, so no field, no blinding and no root moves), its footprint holds there, its
one authorization is its observe capability, and that capability's scope names every cited
field. -/
theorem citedRead_ok {snapshot : AuthoritySnapshot} {kind : ResourceKind} {id : Nat}
    {capability : CapabilityId} {observe : Option CapabilityId} {audience : Bool}
    {reads : List FieldRead} {store post : Store EffectDeclaration.effectLayout}
    (ok : citedRead snapshot kind id capability observe audience reads store = .ok post) :
    post = store ∧ PlanBinding.Footprint.Holds store (citedFootprint reads) ∧
      observe = some capability ∧ citedScope snapshot kind capability reads = none := by
  unfold citedRead at ok
  split at ok; · cases ok
  split at ok; · cases ok
  split at ok; · cases ok
  rename_i observed _
  split at ok
  · cases ok
  · rename_i named
    split at ok
    · rename_i current
      cases ok
      exact ⟨rfl, (citedMoved_eq_nil_iff _ _).1 current, Decidable.not_not.mp observed, named⟩
    · cases ok

/-- **An admitted footprint's keys are the read cell's own.** Every key an admitted cited read
names is a field (or the program code) of the very cell it was checked against: a key of another
cell refuses `citedKey`. The signed bytes of a read are its keys and values (`fieldReadStream`),
and a key spells its cell's id, so the footprint's digest (`citedDigest`) binds the id of the
cell that was read: a law that compares `cited/digest` with a recorded read set (the branch
law's position 2) pins that cell by id, up to a collision of the digest. -/
theorem citedRead_keys_own {snapshot : AuthoritySnapshot} {kind : ResourceKind} {id : Nat}
    {capability : CapabilityId} {observe : Option CapabilityId} {audience : Bool}
    {reads : List FieldRead} {store post : Store EffectDeclaration.effectLayout}
    (ok : citedRead snapshot kind id capability observe audience reads store = .ok post) :
    ∀ read ∈ reads, DeclaredActionLowering.writableKeyCheck (⟨id⟩ : ResourceId kind) read.1 = true := by
  unfold citedRead at ok
  split at ok; · cases ok
  split at ok; · cases ok
  split at ok; · cases ok
  rename_i keys
  intro read member
  have every : (reads.all fun read =>
      DeclaredActionLowering.writableKeyCheck (⟨id⟩ : ResourceId kind) read.1) = true := by
    simpa using keys
  exact List.all_eq_true.mp every read member

/-- **K3, the refusing pole: the refusal names every moved field and nothing else.** Under a
grant that names the cited fields, a `citedStale` refusal is exactly `citedMoved` (so, by
`mem_citedMoved`, exactly the cited keys whose value is not the cited one), and it is not empty.
It carries keys only. -/
theorem citedRead_stale {snapshot : AuthoritySnapshot} {kind : ResourceKind} {id : Nat}
    {capability : CapabilityId} {observe : Option CapabilityId} {audience : Bool}
    {reads : List FieldRead} {store : Store EffectDeclaration.effectLayout}
    {moved : List EffectDeclaration.StateKey}
    (granted : citedScope snapshot kind capability reads = none)
    (refused : citedRead snapshot kind id capability observe audience reads store =
      .error (.citedStale moved)) :
    moved = citedMoved store reads ∧ moved ≠ [] := by
  unfold citedRead at refused
  split at refused; · cases refused
  split at refused; · cases refused
  split at refused; · cases refused
  split at refused
  · rename_i reason found
    rw [granted] at found
    cases found
  · split at refused
    · cases refused
    · rename_i stale
      cases refused
      exact ⟨rfl, stale⟩

/-- **A guard is a read: a grant that does not name the cited fields learns nothing.** When the
scope check refuses (the capability is not held, or some cited field is outside it), the
result is the same at every store, so the requester cannot use a cited value as an equality
oracle on a field its grant does not name. -/
theorem citedRead_scope_blind {snapshot : AuthoritySnapshot} {kind : ResourceKind} {id : Nat}
    {capability : CapabilityId} {observe : Option CapabilityId} {audience : Bool}
    {reads : List FieldRead} {reason : CitedRefusal}
    (unnamed : citedScope snapshot kind capability reads = some reason)
    (s s' : Store EffectDeclaration.effectLayout) :
    citedRead snapshot kind id capability observe audience reads s =
      citedRead snapshot kind id capability observe audience reads s' := by
  unfold citedRead
  simp only [unnamed]

/-- **Currency is by value.** Two loaded cells that agree at the cited fields are admitted or
refused alike: a cited value that moved and moved back is current again, and a cell whose root
moved for any other reason (another field written, the ratchet advanced) is still current. -/
theorem citedRead_value_current {snapshot : AuthoritySnapshot} {kind : ResourceKind} {id : Nat}
    {capability : CapabilityId} {observe : Option CapabilityId} {audience : Bool}
    {reads : List FieldRead} {s s' : Store EffectDeclaration.effectLayout}
    (same : ∀ read ∈ reads, s read.1.address = s' read.1.address) :
    (citedRead snapshot kind id capability observe audience reads s).toOption.isSome =
      (citedRead snapshot kind id capability observe audience reads s').toOption.isSome := by
  unfold citedRead
  rw [citedMoved_congr same]
  repeat' split
  all_goals rfl

/-! ## What a law sees -/

/-- The cited fields' present values in the loaded cell, as declared values (`resource/field/…`). -/
def citedValues (id : Nat) (reads : List FieldRead) (store : Store EffectDeclaration.effectLayout) :
    DeclaredResourceProjection.Values :=
  (DeclaredResourceProjection.values id store).filter fun entry =>
    reads.any fun read => decide (read.1 = .objectField ⟨id⟩ ⟨entry.1⟩)

/-- The digest of a cited footprint: the canonical bytes of its reads, keys and values. A law
can require it to equal a field of another participant (a verdict's read set), which binds
the turn's cited reads of this cell to the ones that verdict recorded. -/
def citedDigest (reads : List FieldRead) : Digest :=
  (Sp800185Cshake256.hash "DREGG.RESOURCE.TRANSACTION.CITED/v1".toUTF8.toList
    ((StreamCodec.list fieldReadStream).encode reads)).digest

/-- What a law sees of a cited cell: exactly the cited fields that are present, under the
declared names (`before` and `after` are the one loaded value: a read writes nothing), then
the footprint's size and digest. A field the turn did not cite is not projected. -/
def citedProject (id : Nat) (reads : List FieldRead) (store : Store EffectDeclaration.effectLayout) :
    List (String × Int) :=
  DeclaredResourceProjection.scalarSlots (citedValues id reads store) (citedValues id reads store) ++
    [("cited/count", Int.ofNat reads.length), ("cited/digest", Int.ofNat (citedDigest reads).value)]

/-! ## The faces -/

/-- A cited key as the request spells it: an object field or a program's code, by number. -/
def citedKeyJson : EffectDeclaration.StateKey → Lean.Json
  | .objectField object field => .mkObj [("type", .str "object"),
      ("resource", EffectJson.decimal object.value), ("field", EffectJson.decimal field.value)]
  | .programCode program => .mkObj [("type", .str "program"),
      ("resource", EffectJson.decimal program.value), ("field", EffectJson.decimal 0)]
  | _ => .mkObj [("type", .str "unsupported")]

def citedToJson (reads : List FieldRead) : List (String × Lean.Json) :=
  [("reads", .arr (reads.toArray.map fun read => .mkObj
    [("key", citedKeyJson read.1),
     ("observed", (read.2.map EffectJson.signedDecimal).getD .null)]))]

def citedOfJson (path : String) (json : Lean.Json) : Except String (List FieldRead) := do
  let obj ← EffectJson.exactObject path ["type", "reads"] json
  EffectJson.list (path ++ ".reads") (fun path json => do
    let read ← EffectJson.exactObject path ["key", "observed"] json
    let keyObj ← EffectJson.exactObject (path ++ ".key") ["type", "resource", "field"]
      (← EffectJson.field path "key" read)
    let keyType ← EffectJson.string (path ++ ".key.type") (← EffectJson.field (path ++ ".key") "type" keyObj)
    let resource ← EffectJson.nat (path ++ ".key.resource") (← EffectJson.field (path ++ ".key") "resource" keyObj)
    let fieldId ← EffectJson.nat (path ++ ".key.field") (← EffectJson.field (path ++ ".key") "field" keyObj)
    unless keyType = "object" ∨ keyType = "program" do
      throw s!"{path}.key.type: expected object or program"
    let key := if keyType = "program"
      then EffectDeclaration.StateKey.programCode ⟨resource⟩
      else EffectDeclaration.StateKey.objectField ⟨resource⟩ ⟨fieldId⟩
    let observed ← EffectJson.optional (path ++ ".observed") EffectJson.int (← EffectJson.field path "observed" read)
    pure (key, observed)) (← EffectJson.field path "reads" obj)

/-- A cited key in words: the field's number, or the program's code. -/
def citedKeyText : EffectDeclaration.StateKey → String
  | .objectField _ field => s!"field {field.value}"
  | .programCode _ => "program code"
  | other => reprStr other

/-- What a member is shown of a cited read before signing: that it writes nothing, and every
cited field with the value the signature binds it to. The signed bytes are exactly these keys
and values (`fieldReadStream`), so the display commits to the whole footprint. -/
def citedDisplay (reads : List FieldRead) : List String :=
  s!"cited read of {reads.length} field(s), bound by value; no resource write" ::
    reads.map fun read =>
      match read.2 with
      | some value => s!"  {citedKeyText read.1} = {value}"
      | none => s!"  {citedKeyText read.1} absent"

/-- A refusal's detail in words: the moved fields of `citedStale`, as the display names them. -/
def citedRefusalText (_name : String) (detail : List UInt8) : String :=
  match movedStream.toLawful.decode detail with
  | some moved => "[" ++ ", ".intercalate (moved.map citedKeyText) ++ "]"
  | none => ""

/-! ## The declaration -/

/-- The semantics as a descriptor: the cited read, emitting the empty patch. -/
def citedSem (ctx : EffectCtx) (reads : List FieldRead) (store : Store EffectDeclaration.effectLayout) :
    Except CitedRefusal (Patch EffectDeclaration.effectLayout) :=
  (citedRead ctx.snapshot ctx.kind ctx.target ctx.capability ctx.observe
    (ctx.audienceEpoch.isSome || ctx.audienceRoster.isSome) reads store).map fun _ => []

theorem citedSem_ok {ctx : EffectCtx} {reads : List FieldRead}
    {store : Store EffectDeclaration.effectLayout} {ps : Patch EffectDeclaration.effectLayout}
    (ok : citedSem ctx reads store = .ok ps) : ps = [] := by
  unfold citedSem at ok
  cases read : citedRead ctx.snapshot ctx.kind ctx.target ctx.capability ctx.observe
      (ctx.audienceEpoch.isSome || ctx.audienceRoster.isSome) reads store with
  | error reason => rw [read] at ok; cases ok
  | ok post => rw [read] at ok; exact (Except.ok.inj ok).symm

/-- An admitted descriptor is an admitted cited read, at the loaded store. -/
theorem citedSem_read {ctx : EffectCtx} {reads : List FieldRead}
    {store : Store EffectDeclaration.effectLayout} {ps : Patch EffectDeclaration.effectLayout}
    (ok : citedSem ctx reads store = .ok ps) :
    citedRead ctx.snapshot ctx.kind ctx.target ctx.capability ctx.observe
      (ctx.audienceEpoch.isSome || ctx.audienceRoster.isSome) reads store = .ok store := by
  unfold citedSem at ok
  cases read : citedRead ctx.snapshot ctx.kind ctx.target ctx.capability ctx.observe
      (ctx.audienceEpoch.isSome || ctx.audienceRoster.isSome) reads store with
  | error reason => rw [read] at ok; cases ok
  | ok post => rw [(citedRead_ok read).1]

/-- **The cited read's declaration.** Any role but an account, schema version 1; it commutes
(no root is compared), has no rotate and an empty frame; its verb is the kind's observe verb;
the law's view is `citedProject` of the loaded cell. -/
def citedSpec : Revival.EffectSpec EffectCtx (Revival.storeSubstrate EffectDeclaration.effectLayout)
    (List FieldRead) CitedRefusal where
  opStream := StreamCodec.list fieldReadStream
  refusalName := CitedRefusal.name
  refusalDetail := CitedRefusal.detail
  accepts := fun kind => kind != .account
  version := 1
  sem := citedSem
  rotate := fun _ _ => []
  rotated := fun _ => false
  field := fun (address : Address EffectDeclaration.effectLayout) =>
    ResourceObservationAdmission.declaredField address.2
  amount := fun _ _ => 0
  frame := fun _ => ∅
  verb := fun kind _ => observeVerb kind
  view := fun site reads before _ => citedProject site.target reads before
  commutes := fun _ => true

theorem citedProject_unjoint (id : Nat) (reads : List FieldRead)
    (store : Store EffectDeclaration.effectLayout) : JointSlots.Unjoint (citedProject id reads store) := by
  unfold citedProject
  refine JointSlots.unjoint_append _ _ (JointSlots.scalarSlots_unjoint _ _) ?_
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> dsimp only <;> decide

/-- **The cited read, as the registry binds it.** -/
def citedEffect : Effect where
  name := "fieldRead"
  L := EffectDeclaration.effectLayout
  wire := DeclaredEffectCell.wire
  O := List FieldRead
  R := CitedRefusal
  decO := inferInstance
  spec := citedSpec
  pack := DeclaredResourceScalar.packDeclared
  unpack := unpackDeclared
  toJson := citedToJson
  ofJson := citedOfJson
  display := citedDisplay
  refusalText := citedRefusalText
  unpack_pack := unpackDeclared_pack
  pack_unpack := packDeclared_unpack
  observes_silent := by
    intro ctx reads store ps _ emitted
    unfold Revival.EffectSpec.emitted at emitted
    cases sem : citedSem ctx reads store with
    | error reason =>
        rw [show citedSpec.sem ctx reads store = citedSem ctx reads store from rfl, sem] at emitted
        cases emitted
    | ok descriptor =>
        rw [show citedSpec.sem ctx reads store = citedSem ctx reads store from rfl, sem] at emitted
        have empty := citedSem_ok sem
        subst empty
        exact (Except.ok.inj emitted).symm
  complete := by
    intro ctx reads store ps ok
    have empty : ps = [] := citedSem_ok ok
    subst empty
    exact ⟨fun loc member => absurd member (Finset.notMem_empty loc), rfl⟩
  view_unjoint := fun site reads before _ => citedProject_unjoint site.target reads before

/-- A cited read is observe-only, whatever it cites. -/
theorem cited_observeOnly (reads : List FieldRead) : citedEffect.observeOnly reads = true := rfl

end Minidregg.Kernel.DeclaredResourceController
