/-
# `Kernel/ResourceEffect.lean` — a declared-resource effect as ONE declaration

The deployed write path's effect vocabulary is `DeclaredResourceController.Payload`
(`Kernel/ResourceTransaction.lean`). A hand-written payload kind costs one arm in every function
that matches a payload (`docs/EFFECTS-REVIVAL.md` §1). `Effect` is the open alternative: one
record from which every one of those arms is read.

* its typed cell: `L`, `wire` (so the materializer and the salted root are the wire's), and how
  that cell sits in the controller's cell universe (`pack`, `unpack`; selection adds the
  deployment's cell law, the same for every effect);
* its declaration: `spec`, an `Effects.Revival.EffectSpec` over the store substrate. The
  operation codec, the refusal names and their structured detail, the accepted roles and schema
  version, the semantics (a guarded patch or a named refusal), the kernel's rotate, the field
  classification, the declared frame, the verb, the law's view and whether the operation commutes
  are all there;
* its faces: `name` (the JSON `type`), `toJson`, `ofJson`, `display` (what a member is shown
  before signing, and what `mini inspect` prints) and `refusalText` (a refusal's detail in words);
* its openings (`opens`): what an operation claims of other cells its transaction reads.

Derived here, with nothing authored per effect: the computation (`compute`: the header the
declaration's `accepts`/`version`/`commutes` determine, then the engine's checked executor
`Effect.run`, which is `EffectSpec.exec`), the patch (`patch`: the emitted descriptor), whether it is observe-only
(`observeOnly`: its verb is the kind's observe verb), and the engine handler (`handler`) that
`Effects.Revival.Dispatches` is stated over.

What a semantics may read is `EffectCtx`. The signed `expectedTargetRoot` and the schema version
are not in it: the header owns both, so no declaration can compare a root by hand.
-/
module

public import Effects.Revival.Engine
public import Kernel.DeclaredResourceScalar
public import Compiler.ObjectAudienceRoster
public import Lean.Data.Json
public import Theory.Eval

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

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev AuthoritySnapshot := CredentialAuthorityDomain.Snapshot
abbrev Ambient := DeclaredResourceScalar.Ambient

def observeVerb : (kind : ResourceKind) → Verb kind
  | .object => .observeObject
  | .account => .observeAccount
  | .program => .observeProgram

/-- Whether a verb is its kind's observe verb. -/
def observes : {kind : ResourceKind} → Verb kind → Bool
  | _, .observeObject | _, .observeAccount | _, .observeProgram => true
  | _, _ => false

@[simp] theorem observes_observeVerb (kind : ResourceKind) : observes (observeVerb kind) = true := by
  cases kind <;> rfl

/-! ## Joint keys (the part of `Kernel.JointSlots` a declaration's view is held to) -/

namespace JointSlots

/-- The first character of a key; every joint key begins with `j`. -/
def Unjoint (xs : List (String × Int)) : Prop := ∀ p ∈ xs, p.1.toList.head? ≠ some 'j'

theorem head_append (stem rest : String) (c : Char) (h : stem.toList.head? = some c) :
    (stem ++ rest).toList.head? = some c := by
  simp only [String.toList_append]
  cases hs : stem.toList with
  | nil => simp [hs] at h
  | cons d ds => simp [hs] at h ⊢; exact h

theorem unjoint_append (xs ys : List (String × Int)) (hx : Unjoint xs) (hy : Unjoint ys) :
    Unjoint (xs ++ ys) := by
  intro p hp; rcases List.mem_append.mp hp with h | h
  · exact hx p h
  · exact hy p h

theorem scalarSlots_unjoint (before after : DeclaredResourceProjection.Values) :
    Unjoint (DeclaredResourceProjection.scalarSlots before after) := by
  have field : ∀ n v, (DeclaredResourceProjection.fieldName n v).toList.head? ≠ some 'j' := by
    intro n v
    show ("resource/field/" ++ toString n ++ "/" ++ v).toList.head? ≠ some 'j'
    simp only [String.append_assoc]
    rw [head_append _ _ 'r' (by decide)]; decide
  have pair : ∀ a b, (DeclaredResourceProjection.pairName a b).toList.head? ≠ some 'j' := by
    intro a b
    show ("resource/pair/" ++ toString a ++ "/" ++ toString b ++ "/delta").toList.head? ≠ some 'j'
    simp only [String.append_assoc]
    rw [head_append _ _ 'r' (by decide)]; decide
  intro p hp
  unfold DeclaredResourceProjection.scalarSlots at hp
  rcases List.mem_append.mp hp with hp | hp
  rcases List.mem_append.mp hp with hp | hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp; exact field _ _
  · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp; exact field _ _
  · obtain ⟨q, _, h⟩ := List.mem_filterMap.mp hp
    obtain ⟨old, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact field _ _
  · obtain ⟨a, _, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨b, _, h⟩ := List.mem_filterMap.mp hp
    cases ha : DeclaredResourceProjection.get before a.1 with
    | none => simp [ha] at h
    | some oldA =>
      cases hb : DeclaredResourceProjection.get before b.1 with
      | none => simp [ha, hb] at h
      | some oldB =>
        simp only [ha, hb, Option.bind_some, Option.some.injEq, bind, pure] at h
        subst h; exact pair _ _

end JointSlots

/-- What a registered effect's semantics consumes of its transaction: the authority snapshot,
the profile and the height, the signer and nonce, the target's header but its schema version
and expected root (the dispatcher's, `Effect.compute`), and two facts of the whole command: its
operation id and the cells it reads observe-only. -/
structure EffectCtx where
  snapshot : AuthoritySnapshot
  semantics : Digest
  ambient : Ambient
  subject : SubjectId
  nonce : Nat
  kind : ResourceKind
  target : Nat
  capability : CapabilityId
  observe : Option CapabilityId
  audienceEpoch : Option Nat
  audienceRoster : Option Minidregg.Theory.ObjectAudienceRoster.Roster
  /-- The transaction's operation id: a digest of the whole command under the domain and the
  profile, computed when a semantics asks for it. -/
  operation : Unit → Digest
  /-- The observe capability of the cell this transaction reads observe-only at an id, if it
  reads one there: what a write that cites that cell's content is checked against. -/
  sourceRead : Nat → Option CapabilityId

/-- **What a member signs of an effect's context**: the signer and nonce of the command, and
the target's role, id and capability. Every field is in the signed command; none is the
receiver's (no authority snapshot, no height, no operation id, no other cell). A declaration's
member patch (`Effect.member`) reads this and nothing else of its transaction. -/
structure MemberCtx where
  subject : SubjectId
  nonce : Nat
  kind : ResourceKind
  target : Nat
  capability : CapabilityId

/-- The signed part of an effect's context. -/
def EffectCtx.signed (ctx : EffectCtx) : MemberCtx :=
  ⟨ctx.subject, ctx.nonce, ctx.kind, ctx.target, ctx.capability⟩

/-- **One declared-resource effect.** Every arm the controller, the compilers and the Host run
for a registered payload is read from this record (`Payload.registered`). -/
structure Effect : Type 1 where
  /-- The effect's name: the `type` of its JSON face. -/
  name : String
  L : Layout.{0, 0, 0}
  wire : StoreCodec.Wire L
  O : Type
  R : Type
  decO : DecidableEq O
  spec : Revival.EffectSpec EffectCtx (Revival.storeSubstrate L) O R
  /-- The typed cell in the controller's universe, under the transaction's role. -/
  pack : ResourceKind → Materialized (StoreCodec.materializer wire) → PackedCell Registry
  unpack : ResourceKind → PackedCell Registry → Option (Materialized (StoreCodec.materializer wire))
  /-- The operation's JSON fields beside `type`. -/
  toJson : O → List (String × Lean.Json)
  /-- The operation read from its JSON object (`path` names it in a refusal). -/
  ofJson : String → Lean.Json → Except String O
  /-- What the operation is shown as before it is signed: one line per fact it commits to. -/
  display : O → List String
  /-- A refusal's structured detail in words: `detail` is `spec.refusalDetail`'s bytes of the
  refusal `name`. Empty when the name says it all. -/
  refusalText : String → ByteArray → String := fun _ _ => ""
  /-- The operation's openings: what it claims of OTHER cells of its transaction. Each names a
  cell the transaction must read observe-only and what must hold of that cell as loaded; the
  controller refuses a command one of whose openings does not hold (`openingsRefusal`). -/
  opens : O → List (Nat × (PackedCell Registry → Bool)) := fun _ => []
  /-- **The fields the operation's guards read**, when its guards are reads the authorizing
  capability must name: a guard tells its requester whether the guarded field holds the value it
  named, so a guard over a field the capability does not name would be an equality oracle on
  that field. `some fields`: the dispatcher's header refuses, before the schema version and the
  root and before any guard runs, a capability the authority cell does not hold
  (`capabilityRejected`) and one whose scope does not name every field (`fieldNotNamed`);
  `Effect.scopeRefusal`. `none` (the default): the header asks nothing of the capability. -/
  guardFields : O → Option (List CellField) := fun _ => none
  /-- The law's view restricted to the slots a demand names. A declaration whose view is costly
  computes only what is named (a content cell's summaries; a declared cell's pair deltas, which
  `leads` gates by their leading field); the default filters the whole view. -/
  viewDemand : (String → Bool) → (Nat → Bool) → Revival.Site → O → Store L → Store L →
      List (String × Int) :=
    fun want _ site op before after => (spec.view site op before after).filter fun slot => want slot.1
  viewDemand_eq : ∀ (want : String → Bool) (leads : Nat → Bool),
    (∀ a b, want (DeclaredResourceProjection.pairName a b) = true → leads a = true) →
    ∀ site op before after, viewDemand want leads site op before after =
      (spec.view site op before after).filter fun slot => want slot.1 := by intros; rfl
  /-- **The member patch**: the operation's patch as a member computes it before signing, from
  the signed part of the context and the store the Host served at the signed root. `none` (the
  default) says this effect's patch reads something that is neither signed nor served (a
  content write reads the authority's policy coordinates and the height); a member is then never
  shown a post for it. `some f` with `f … = none` says the operation does not apply to that
  store. `member_exact` holds it to the semantics. -/
  member : Option (MemberCtx → O → Store L → Option (Patch L)) := none
  /-- Whether the member patch reads the store. One that does is computed only from a served
  store that hides no entry (`member_blind` is what `false` asserts). -/
  memberReadsStore : Bool := true
  /-- The member patch is the semantics' patch wherever both answer: a member is never shown a
  patch the receiver would not emit. -/
  member_exact : ∀ f, member = some f → ∀ (ctx : EffectCtx) (op : O) (s : Store L)
      (ps patch : Patch L), f ctx.signed op s = some patch → spec.sem ctx op s = .ok ps →
      ps = patch := by
    intro _ stated; cases stated
  /-- What the kernel appends to a member patch (the rotate) writes only rotated addresses. -/
  member_tail : ∀ f, member = some f → ∀ (ctx : EffectCtx) (s store : Store L)
      (address : Address L), spec.rotated address = false →
      Patch.run store (spec.rotate ctx s) address = store address := by
    intro _ stated; cases stated
  /-- A member patch declared not to read the store is the same over any two stores. -/
  member_blind : memberReadsStore = false → ∀ f, member = some f →
      ∀ (ctx : MemberCtx) (op : O) (left right : Store L), f ctx op left = f ctx op right := by
    first
      | (intro reads; cases reads)
      | (intro _ _ stated; cases stated)
  /-- **The semantic footprint**, for a cell whose fields are not its addresses: a world
  instance's fields live inside its payload entry, and a capability's scope names those. `none`
  (the default): the footprint is read off the changed addresses by `spec.field` and
  `spec.amount`. It is given the operation: a compute funding's footprint is the debit its
  operation names on the shared Book, which no address of its own cell shows. -/
  footprint : Option (O → Store L → Store L → Footprint) := none
  /-- **What a run may claim of this operation** (K-RAN): the field writes a re-executed program's
  product must name, from the loaded store, the program, the target's index in the command, the
  target's cell id and whether the target is the account the transaction's compute funding was
  validated at. `none` (the default): one write at coordinate 0 holding the operation's
  canonical bytes. -/
  runWrites : Option (Store L → Digest → Nat → Nat → Bool → O → Option (List Eval.FieldWrite)) := none
  /-- **The target is never written**: every admitted operation leaves the cell as loaded (what
  the operation does is outside its target, on the shared Book). The transaction then enters the
  target as a read guard on its root, not as a write (`Target.isRead`). `unchanging_silent`
  holds the flag to the semantics. -/
  unchanging : Bool := false
  unchanging_silent : unchanging = true → ∀ (ctx : EffectCtx) (op : O) (s : Store L)
      (ps : Patch L), spec.emitted ctx op s = .ok ps → ps = [] := by
    intro stated; cases stated
  /-- **The operation is the kernel's accounting, not an application effect**: a plan of the
  command's application effects does not report it (a compute funding leg is validated and
  charged by the kernel). -/
  accounting : Bool := false
  /-- Whether the operation authors anything: a world write without actions is admitted and
  changes nothing, and is no one's publication. -/
  authors : O → Bool := fun _ => true
  unpack_pack : ∀ kind cell, unpack kind (pack kind cell) = some cell
  pack_unpack : ∀ kind packed cell, unpack kind packed = some cell → pack kind cell = packed
  /-- An effect authorized as an observation emits nothing: no write, no rotate. -/
  observes_silent : ∀ (ctx : EffectCtx) (op : O) (s : Store L) (ps : Patch L),
    observes (spec.verb ctx.kind op) = true → spec.emitted ctx op s = .ok ps → ps = []
  /-- The declaration's own obligation (`EffectSpec.Complete`): every admitted operation stays
  in its declared frame and its descriptor replays, so neither of the dispatcher's own refusals
  is reachable and every refusal of this effect is one of its names. -/
  complete : spec.Complete
  /-- No slot of the law's view is a joint key: a participant's own projection cannot spell
  another participant's name. -/
  view_unjoint : ∀ site op before after, JointSlots.Unjoint (spec.view site op before after)

instance (e : Effect) : DecidableEq e.O := e.decO

/-- **A member patch agrees with a semantics**: wherever both answer, they answer the same
patch. The law `Effect.member_exact` holds a declaration's stated member patch to it; a function
that fails it cannot be stated (`Effect.member_stated_exact`). -/
def MemberExact {L : Layout.{0, 0, 0}} {O R : Type}
    (spec : Revival.EffectSpec EffectCtx (Revival.storeSubstrate L) O R)
    (f : MemberCtx → O → Store L → Option (Patch L)) : Prop :=
  ∀ (ctx : EffectCtx) (op : O) (s : Store L) (ps patch : Patch L),
    f ctx.signed op s = some patch → spec.sem ctx op s = .ok ps → ps = patch

theorem Effect.member_stated_exact (e : Effect) {f : MemberCtx → e.O → Store e.L → Option (Patch e.L)}
    (stated : e.member = some f) : MemberExact e.spec f :=
  e.member_exact f stated

/-- The dispatch's context: the effect's, plus the deployment and the header's version and
expected root. -/
structure DispatchCtx extends EffectCtx where
  deployment : Deployment
  version : Nat
  root : Digest

/-- An admitted execution: the semantics emitted a descriptor inside the declared frame, and the
post is its replay (with the rotate). Stated over any substrate. -/
theorem _root_.Minidregg.Effects.Revival.EffectSpec.exec_ok {Ctx : Type} {S : Revival.Substrate}
    {O R : Type} {E : Revival.EffectSpec Ctx S O R} {code : Nat} {ctx : Ctx} {op : O}
    {s s' : S.State} (ok : E.exec code ctx op s = .ok s') :
    ∃ ps, E.sem ctx op s = .ok ps ∧ E.InFrame op (ps ++ E.rotate ctx s) ∧
      S.run s (ps ++ E.rotate ctx s) = some s' := by
  simp only [Revival.EffectSpec.exec] at ok
  split at ok
  · cases ok
  · rename_i ps sem
    split at ok
    · rename_i inFrame
      split at ok
      · cases ok
      · rename_i ran
        cases ok
        exact ⟨ps, sem, inFrame, ran⟩
    · cases ok

namespace Effect

variable (e : Effect)

abbrev materializer : Materializer e.L Digest := StoreCodec.materializer e.wire

abbrev Cell : Type := Materialized e.materializer

/-- Selection: the deployment's cell law, then the role. -/
def select (deployment : Deployment) (id : Nat) (kind : ResourceKind) (packed : PackedCell Registry) :
    Option e.Cell :=
  if CanonicalCellRegistry.CellLaw deployment id packed then e.unpack kind packed else none

/-- Observe-only: under every role the operation's verb is the observe verb, so its one
authorization is an observation. -/
def observeOnly (op : e.O) : Bool :=
  [ResourceKind.object, .account, .program].all fun kind => observes (e.spec.verb kind op)

theorem observeOnly_at {op : e.O} (read : e.observeOnly op = true) (kind : ResourceKind) :
    observes (e.spec.verb kind op) = true := by
  unfold observeOnly at read
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at read
  cases kind
  · exact read.1
  · exact read.2.1
  · exact read.2.2

/-- What the controller runs: the declaration's semantics, then the guarded replay of its
descriptor and the rotate. It is the engine's checked executor (`run_eq_exec`) without the
frame check, which `complete` proves cannot refuse: a write pays no footprint computation. -/
def run (code : Nat) (ctx : EffectCtx) (op : e.O) (s : Store e.L) :
    Except Revival.DispatchRefusal (Store e.L) :=
  match e.spec.sem ctx op s with
  | .error r => .error (.refused code (e.spec.refusalName r) (e.spec.refusalDetail r))
  | .ok ps =>
    match (Revival.storeSubstrate e.L).run s (ps ++ e.spec.rotate ctx s) with
    | none => .error (.guardFailed code)
    | some s' => .ok s'

theorem run_eq_exec (code : Nat) (ctx : EffectCtx) (op : e.O) (s : Store e.L) :
    e.run code ctx op s = e.spec.exec code ctx op s := by
  unfold run Revival.EffectSpec.exec
  cases sem : e.spec.sem ctx op s with
  | error r => rfl
  | ok ps =>
    dsimp only
    rw [if_pos (e.complete ctx op s ps sem).1]
    cases (Revival.storeSubstrate e.L).run s (ps ++ e.spec.rotate ctx s) <;> rfl

/-- **The header's scope gate.** For an operation whose guards are reads (`guardFields`): the
authorizing capability must be held in the authority cell and its scope must name every field a
guard reads. It reads the authority cell, the role, the capability and the operation; never the
target cell, so its answer is the same at every loaded store. -/
def scopeRefusal (code : Nat) (ctx : EffectCtx) (op : e.O) : Option Revival.DispatchRefusal :=
  match e.guardFields op with
  | none => none
  | some fields =>
    match CredentialAuthorityState.readCapability ctx.snapshot.cell ctx.kind ctx.capability with
    | none => some (.capabilityRejected code)
    | some stored =>
      if fields.all fun field => decide (CellField.NamedBy stored.head.scope.fields field)
      then none else some (.fieldNotNamed code)

/-- The scope gate's two refusals, under the code it was asked at. -/
theorem scopeRefusal_named {code : Nat} {ctx : EffectCtx} {op : e.O}
    {refusal : Revival.DispatchRefusal} (refused : e.scopeRefusal code ctx op = some refusal) :
    refusal = .capabilityRejected code ∨ refusal = .fieldNotNamed code := by
  unfold scopeRefusal at refused
  split at refused
  · cases refused
  · split at refused
    · exact .inl (Option.some.inj refused).symm
    · split at refused
      · cases refused
      · exact .inr (Option.some.inj refused).symm

theorem scopeRefusal_unscoped {op : e.O} (unscoped : e.guardFields op = none) (code : Nat)
    (ctx : EffectCtx) : e.scopeRefusal code ctx op = none := by
  unfold scopeRefusal; rw [unscoped]

/-- **The derived computation.** The header (role, the scope of the operation's guards, schema
version, and the expected root unless the operation commutes), then the engine's checked
executor: the declaration's semantics, the frame check and the guarded replay. -/
def compute (code : Nat) (ctx : EffectCtx) (version : Nat) (root : Digest) (op : e.O)
    (pre : e.Cell) : Except Revival.DispatchRefusal (Store e.L) :=
  if e.spec.accepts ctx.kind = false then .error (.wrongRole code)
  else match e.scopeRefusal code ctx op with
    | some refusal => .error refusal
    | none =>
      if version ≠ e.spec.version then .error (.unsupportedVersion code)
      else if e.spec.commutes op = false ∧ root ≠ pre.root then .error (.staleTarget code)
      else e.run code ctx op pre.logical

/-- The computation of an operation the scope gate passes: the role, the schema version, the
root, the executor. -/
theorem compute_scoped {code : Nat} {ctx : EffectCtx} {op : e.O}
    (passed : e.scopeRefusal code ctx op = none) (version : Nat) (root : Digest) (pre : e.Cell) :
    e.compute code ctx version root op pre =
      if e.spec.accepts ctx.kind = false then .error (.wrongRole code)
      else if version ≠ e.spec.version then .error (.unsupportedVersion code)
      else if e.spec.commutes op = false ∧ root ≠ pre.root then .error (.staleTarget code)
      else e.run code ctx op pre.logical := by
  unfold compute; rw [passed]

/-- A scope the gate refuses is refused under an accepted role at every schema version, root and
loaded cell. -/
theorem compute_scope_refused {code : Nat} {ctx : EffectCtx} {op : e.O}
    {refusal : Revival.DispatchRefusal} (accepted : e.spec.accepts ctx.kind = true)
    (refused : e.scopeRefusal code ctx op = some refusal) (version : Nat) (root : Digest)
    (pre : e.Cell) : e.compute code ctx version root op pre = .error refusal := by
  unfold compute
  rw [if_neg (by rw [accepted]; decide), refused]

/-- An admitted computation passed the scope gate. -/
theorem compute_ok_scoped {code : Nat} {ctx : EffectCtx} {version : Nat} {root : Digest}
    {op : e.O} {pre : e.Cell} {post : Store e.L}
    (ok : e.compute code ctx version root op pre = .ok post) :
    e.scopeRefusal code ctx op = none := by
  unfold compute at ok
  by_cases accepted : e.spec.accepts ctx.kind = false
  · rw [if_pos accepted] at ok; cases ok
  rw [if_neg accepted] at ok
  cases scope : e.scopeRefusal code ctx op with
  | none => rfl
  | some refusal => rw [scope] at ok; cases ok

/-- **The derived patch**: the emitted descriptor (the operation's patch, then the rotate). -/
def patch (ctx : EffectCtx) (op : e.O) (pre : Store e.L) : Patch e.L :=
  match e.spec.emitted ctx op pre with
  | .ok ps => ps
  | .error _ => []

theorem patch_observeOnly (ctx : EffectCtx) (op : e.O) (pre : Store e.L)
    (read : e.observeOnly op = true) : e.patch ctx op pre = [] := by
  unfold patch
  split
  · rename_i ps emitted
    exact e.observes_silent ctx op pre ps (e.observeOnly_at read ctx.kind) emitted
  · rfl

/-- An admitted computation passed the header, its semantics emitted a descriptor, and the
post is that descriptor (with the rotate) replayed from the loaded store. -/
theorem compute_ok {code : Nat} {ctx : EffectCtx} {version : Nat} {root : Digest} {op : e.O}
    {pre : e.Cell} {post : Store e.L}
    (ok : e.compute code ctx version root op pre = .ok post) :
    e.spec.accepts ctx.kind = true ∧ version = e.spec.version ∧
      ∃ ps, e.spec.sem ctx op pre.logical = .ok ps ∧
        (Revival.storeSubstrate e.L).run pre.logical (ps ++ e.spec.rotate ctx pre.logical) = some post := by
  rw [e.compute_scoped (e.compute_ok_scoped ok)] at ok
  by_cases accepted : e.spec.accepts ctx.kind = false
  · rw [if_pos accepted] at ok; cases ok
  rw [if_neg accepted] at ok
  by_cases versioned : version ≠ e.spec.version
  · rw [if_pos versioned] at ok; cases ok
  rw [if_neg versioned] at ok
  by_cases moved : e.spec.commutes op = false ∧ root ≠ pre.root
  · rw [if_pos moved] at ok; cases ok
  rw [if_neg moved, e.run_eq_exec] at ok
  obtain ⟨ps, sem, _, ran⟩ := Revival.EffectSpec.exec_ok (E := e.spec) ok
  exact ⟨by simpa using accepted, Decidable.not_not.mp versioned, ps, sem, ran⟩

/-- An admitted computation of an operation that does not commute ran at the root its plan
names: the loaded cell's root is the signed one. -/
theorem compute_pinned {code : Nat} {ctx : EffectCtx} {version : Nat} {root : Digest} {op : e.O}
    {pre : e.Cell} {post : Store e.L}
    (ok : e.compute code ctx version root op pre = .ok post)
    (pinned : e.spec.commutes op = false) : root = pre.root := by
  rw [e.compute_scoped (e.compute_ok_scoped ok)] at ok
  by_cases accepted : e.spec.accepts ctx.kind = false
  · rw [if_pos accepted] at ok; cases ok
  rw [if_neg accepted] at ok
  by_cases versioned : version ≠ e.spec.version
  · rw [if_pos versioned] at ok; cases ok
  rw [if_neg versioned] at ok
  by_cases moved : e.spec.commutes op = false ∧ root ≠ pre.root
  · rw [if_pos moved] at ok; cases ok
  · exact Decidable.not_not.mp fun ne => moved ⟨pinned, ne⟩

/-- The kernel's rotate, as a patch of the effect's layout. -/
abbrev rotate (ctx : EffectCtx) (s : Store e.L) : Patch e.L := e.spec.rotate ctx s

/-- Why no member patch is shown for an operation. -/
inductive MemberRefusal where
  /-- The declaration states no member patch: its patch has an input that is neither signed nor
  served. -/
  | unstated
  /-- The operation commutes: its header compares no root, so the member signs no pre-state a
  post could be displayed at. -/
  | commutes
  /-- The member patch does not apply to the served store. -/
  | inapplicable
  deriving DecidableEq, Repr

/-- **The one rule of what a member is shown.** An operation is displayed from its served store
exactly when its declaration states a member patch and the operation pins its root. -/
def memberPatch (ctx : MemberCtx) (op : e.O) (pre : Store e.L) :
    Except MemberRefusal (Patch e.L) :=
  match e.member with
  | none => .error .unstated
  | some f =>
    if e.spec.commutes op = true then .error .commutes
    else
      match f ctx op pre with
      | some patch => .ok patch
      | none => .error .inapplicable

/-- What an accepted member patch is: the declaration states one, the operation pins its root,
and the stated function answered it. -/
theorem memberPatch_ok {ctx : MemberCtx} {op : e.O} {pre : Store e.L} {patch : Patch e.L}
    (shown : e.memberPatch ctx op pre = .ok patch) :
    e.spec.commutes op = false ∧ ∃ f, e.member = some f ∧ f ctx op pre = some patch := by
  unfold memberPatch at shown
  cases stated : e.member with
  | none => rw [stated] at shown; cases shown
  | some f =>
    rw [stated] at shown
    dsimp only at shown
    by_cases free : e.spec.commutes op = true
    · rw [if_pos free] at shown; cases shown
    · rw [if_neg free] at shown
      cases answered : f ctx op pre with
      | none => rw [answered] at shown; cases shown
      | some found =>
        rw [answered] at shown
        cases shown
        exact ⟨by simpa using free, f, rfl, answered⟩

/-- A stated member patch that answers at a root-pinning operation is what is shown. -/
theorem memberPatch_of {f : MemberCtx → e.O → Store e.L → Option (Patch e.L)}
    (stated : e.member = some f) {op : e.O} (pinned : e.spec.commutes op = false)
    {ctx : MemberCtx} {pre : Store e.L} {patch : Patch e.L} (answered : f ctx op pre = some patch) :
    e.memberPatch ctx op pre = .ok patch := by
  unfold memberPatch
  rw [stated]
  dsimp only
  rw [if_neg (by simp [pinned]), answered]

/-- A declaration without a member patch shows none, at every operation and store. -/
theorem memberPatch_unstated (unstated : e.member = none) (ctx : MemberCtx) (op : e.O)
    (pre : Store e.L) : e.memberPatch ctx op pre = .error .unstated := by
  unfold memberPatch; rw [unstated]

/-- A commuting operation is shown no member patch, whatever its declaration states. -/
theorem memberPatch_commuting {op : e.O} (free : e.spec.commutes op = true) (ctx : MemberCtx)
    (pre : Store e.L) : ∃ refusal, e.memberPatch ctx op pre = .error refusal ∧
      (refusal = .unstated ∨ refusal = .commutes) := by
  unfold memberPatch
  cases e.member with
  | none => exact ⟨_, rfl, .inl rfl⟩
  | some f => exact ⟨.commutes, by simp [free], .inr rfl⟩

/-- A member patch that does not read the store is shown the same over any two stores. -/
theorem memberPatch_blind (blind : (e.member.isSome && e.memberReadsStore) = false)
    (ctx : MemberCtx) (op : e.O) (left right : Store e.L) :
    e.memberPatch ctx op left = e.memberPatch ctx op right := by
  unfold memberPatch
  cases stated : e.member with
  | none => rfl
  | some f =>
    have unread : e.memberReadsStore = false := by simpa [stated] using blind
    dsimp only
    rw [e.member_blind unread f stated ctx op left right]

/-- **The member patch against the derived computation.** Wherever the declaration's computation
admits the operation at a loaded cell and the member was shown a patch from that cell's store
under the signed part of the same context: the derived patch is the shown one followed by the
kernel's rotate, the loaded root is the signed one, and the rotate writes only rotated
addresses. -/
theorem member_split {code : Nat} {ctx : EffectCtx} {version : Nat} {root : Digest} {op : e.O}
    {pre : e.Cell} {post : Store e.L} {shown : Patch e.L}
    (computed : e.compute code ctx version root op pre = .ok post)
    (member : e.memberPatch ctx.signed op pre.logical = .ok shown) :
    e.patch ctx op pre.logical = shown ++ e.rotate ctx pre.logical ∧
      root = pre.root ∧
      ∀ (store : Store e.L) (address : Address e.L), e.spec.rotated address = false →
        Patch.run store (e.rotate ctx pre.logical) address = store address := by
  obtain ⟨pinned, f, stated, answered⟩ := e.memberPatch_ok member
  obtain ⟨_, _, ps, sem, _⟩ := e.compute_ok computed
  have exact := e.member_exact f stated ctx op pre.logical ps shown answered sem
  subst exact
  refine ⟨?_, e.compute_pinned computed pinned, fun store address unrotated =>
    e.member_tail f stated ctx pre.logical store address unrotated⟩
  unfold patch Revival.EffectSpec.emitted
  rw [sem]
  rfl

/-- **The engine handler of a declaration**, over the controller's cell universe: what
`Effects.Revival.Dispatches` is stated over. Its header is the live order: selection (role and
cell law), the accepted role, the scope of the operation's guards, the schema version; its
freshness is the expected root. -/
def handler (code : Nat) : Revival.Handler DispatchCtx (PackedCell Registry) where
  S := Revival.storeSubstrate e.L
  O := e.O
  R := e.R
  spec := e.spec.comap DispatchCtx.toEffectCtx
  header ctx op packed :=
    match e.select ctx.deployment ctx.target ctx.kind packed with
    | none => .error (.wrongRole code)
    | some _ =>
      if e.spec.accepts ctx.kind = false then .error (.wrongRole code)
      else match e.scopeRefusal code ctx.toEffectCtx op with
        | some refusal => .error refusal
        | none =>
          if ctx.version ≠ e.spec.version then .error (.unsupportedVersion code)
          else .ok ()
  fresh ctx packed :=
    match e.select ctx.deployment ctx.target ctx.kind packed with
    | none => true
    | some pre => decide (ctx.root = pre.root)
  select ctx packed := (e.unpack ctx.kind packed).map (·.logical)
  pack ctx s := e.pack ctx.kind (CellState.materialize e.materializer s)

end Effect

/-! ## The JSON vocabulary of a declaration's face

The strict reading the Host's request decoder uses: an object's fields are exactly the named
ones, numbers are canonical decimal strings. -/

namespace EffectJson

def exactObject (path : String) (fields : List String) (json : Lean.Json) :
    Except String (Std.TreeMap.Raw String Lean.Json compare) := do
  let value ← (json.getObj?).mapError (fun e => s!"{path}: {e}")
  let actual := value.foldl (init := []) (fun names key _ => key :: names)
  for key in fields do
    unless actual.contains key do throw s!"{path}: missing field {key}"
  for key in actual do
    unless fields.contains key do throw s!"{path}: unknown field {key}"
  pure value

def field (path name : String) (obj : Std.TreeMap.Raw String Lean.Json compare) :
    Except String Lean.Json :=
  match obj.get? name with
  | some value => pure value
  | none => .error s!"{path}: missing field {name}"

def string (path : String) (json : Lean.Json) : Except String String :=
  json.getStr?.mapError (fun _ => s!"{path}: string expected")

def nat (path : String) (json : Lean.Json) : Except String Nat := do
  let source ← string path json
  match source.toNat? with
  | some value =>
      if toString value = source then pure value
      else .error s!"{path}: canonical unsigned decimal string expected"
  | none => .error s!"{path}: unsigned decimal string expected"

def int (path : String) (json : Lean.Json) : Except String Int := do
  let source ← string path json
  match source.toInt? with
  | some value =>
      if toString value = source then pure value
      else .error s!"{path}: canonical signed decimal string expected"
  | none => .error s!"{path}: signed decimal string expected"

def list {α : Type} (path : String) (decode : String → Lean.Json → Except String α)
    (json : Lean.Json) : Except String (List α) := do
  let values ← json.getArr?.mapError (fun _ => s!"{path}: array expected")
  let mut out := #[]
  for i in [:values.size] do
    out := out.push (← decode s!"{path}[{i}]" values[i]!)
  pure out.toList

def optional {α : Type} (path : String) (decode : String → Lean.Json → Except String α)
    (json : Lean.Json) : Except String (Option α) :=
  if json.isNull then pure none else some <$> decode path json

def decimal (value : Nat) : Lean.Json := .str (toString value)

def signedDecimal (value : Int) : Lean.Json := .str (toString value)

end EffectJson

/-! ## The unregistered effect

A code the registry does not bind has no operation: its operation type is empty, so no payload
can carry it and no arm can run for it. -/

/-- The role selection of a declared cell without the deployment's law
(`CanonicalCellRegistry.selectDeclared` is the law, then this: `selectDeclared_eq`). -/
def unpackDeclared (kind : ResourceKind) (packed : PackedCell Registry) :
    Option (Materialized DeclaredEffectCell.materializer) :=
  match kind, packed with
  | .object, ⟨.declaredObject, payload⟩ => some payload
  | .account, ⟨.accountMetadata, payload⟩ => some payload
  | .program, ⟨.declaredProgram, payload⟩ => some payload
  | _, _ => none

theorem selectDeclared_eq (deployment : Deployment) (id : Nat) (kind : ResourceKind)
    (packed : PackedCell Registry) :
    CanonicalCellRegistry.selectDeclared deployment id kind packed =
      if CanonicalCellRegistry.CellLaw deployment id packed then unpackDeclared kind packed
      else none := rfl

theorem unpackDeclared_pack (kind : ResourceKind) (cell : Materialized DeclaredEffectCell.materializer) :
    unpackDeclared kind (DeclaredResourceScalar.packDeclared kind cell) = some cell := by
  cases kind <;> rfl

theorem packDeclared_unpack (kind : ResourceKind) (packed : PackedCell Registry)
    (cell : Materialized DeclaredEffectCell.materializer)
    (selected : unpackDeclared kind packed = some cell) :
    DeclaredResourceScalar.packDeclared kind cell = packed := by
  unfold unpackDeclared at selected
  split at selected <;> first
    | (cases selected; rfl)
    | cases selected

/-- The effect at an unbound code. -/
def Effect.unregistered : Effect where
  name := "unregistered"
  L := EffectDeclaration.effectLayout
  wire := DeclaredEffectCell.wire
  O := Empty
  R := Empty
  decO := fun op => nomatch op
  spec :=
    { opStream :=
        { encode := fun op => nomatch op
          decodePrefix := fun _ => none
          decodePrefix_encode := fun op => nomatch op
          encode_decodePrefix := by intro bytes value; exact nomatch value }
      refusalName := fun r => nomatch r
      accepts := fun _ => false
      version := 0
      sem := fun _ op => nomatch op
      rotate := fun _ _ => []
      rotated := fun _ => false
      field := fun _ => .body
      amount := fun _ _ => 0
      frame := fun _ => ∅
      verb := fun _ op => nomatch op
      view := fun _ op => nomatch op }
  pack := DeclaredResourceScalar.packDeclared
  unpack := unpackDeclared
  toJson := fun op => nomatch op
  ofJson := fun path _ => .error s!"{path}: unregistered effect"
  display := fun op => nomatch op
  unpack_pack := unpackDeclared_pack
  pack_unpack := packDeclared_unpack
  observes_silent := fun _ op => nomatch op
  complete := fun _ op => nomatch op
  view_unjoint := fun _ op => nomatch op

end Minidregg.Kernel.DeclaredResourceController
