/-
# Kernel.SparseAuthenticatedState -- typed sparse ROM/RAM semantics

The old universal map demonstrates that many side tables fit in one address
space, but it fixes keys and payloads to a handful of constructors and `Int`.
This module supplies the semantic memory substrate needed by dynamic heaps,
grains, object stores, control-plane state, and proof-system tables:

* namespaces choose their own key and value types;
* each namespace is ROM, mutable RAM, or fresh-allocation-only append storage;
* absence is the allocation bit, so allocation freshness is a semantic fact;
* access, write, allocation, and free footprints are derived from typed ops;
* an accepted trace has one derived post-state and exact frame/no-ghost laws;
* canonical bytes and roots are projections of a declared lawful codec;
* timestamped lookup-bus rows are derived from the same execution trace.

The bus boundary is intentionally only a semantic equality.  It does not claim
a LogUp/Twist argument, polynomial commitment opening, collision resistance,
or a Rust implementation theorem.  Those require separate compiler and
cryptographic evidence over an encoding of these exact rows.
-/
import Theory.IndexedProgram
import Theory.TypedAuthorization

namespace Minidregg.Kernel.SparseAuthenticatedState

open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe u v w r

/-! ## Typed namespaces and sparse stores -/

/-- The mutation discipline enforced for one namespace.  ROM is initialized
outside an execution and can only be read.  Append-only storage permits fresh
allocation but never overwrite or free.  RAM permits all four operations. -/
inductive Discipline
  | rom
  | ram
  | appendOnly
  deriving DecidableEq, Repr

/-- A heterogeneous address layout.  Both keys and payloads remain indexed by
their namespace; no universal integer payload or unchecked cast is present. -/
structure Layout where
  Namespace : Type u
  Key : Namespace -> Type v
  Value : Namespace -> Type w
  discipline : Namespace -> Discipline

/-- One typed address, existential only in its namespace/key pair. -/
abbrev Address (L : Layout.{u, v, w}) := Sigma L.Key

/-- A sparse store.  `none` is unallocated and `some value` is allocated. -/
abbrev Store (L : Layout.{u, v, w}) :=
  (space : L.Namespace) -> L.Key space -> Option (L.Value space)

/-- Typed lookup through a packed address. -/
def Store.lookup {L : Layout.{u, v, w}} (store : Store L) :
    (address : Address L) -> Option (L.Value address.1)
  | ⟨space, key⟩ => store space key

/-- Update one exact typed address.  `none` deallocates it. -/
def Store.set {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    (store : Store L) (space : L.Namespace) (key : L.Key space)
    (value : Option (L.Value space)) : Store L :=
  Function.update store space (Function.update (store space) key value)

@[simp] theorem Store.set_eq {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    (store : Store L) (space : L.Namespace) (key : L.Key space)
    (value : Option (L.Value space)) :
    (store.set space key value) space key = value := by
  simp [Store.set]

/-- Updating one packed address frames every distinct packed address. -/
theorem Store.set_ne {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    (store : Store L) (space : L.Namespace) (key : L.Key space)
    (value : Option (L.Value space))
    (otherNamespace : L.Namespace) (otherKey : L.Key otherNamespace)
    (different : (⟨otherNamespace, otherKey⟩ : Address L) ≠ ⟨space, key⟩) :
    (store.set space key value) otherNamespace otherKey =
      store otherNamespace otherKey := by
  by_cases namespaceEq : otherNamespace = space
  · subst otherNamespace
    have keyNe : otherKey ≠ key := by
      intro keyEq
      subst otherKey
      exact different rfl
    simp [Store.set, keyNe]
  · simp [Store.set, namespaceEq]

/-- Allocation is exactly absence at an address. -/
def Fresh {L : Layout.{u, v, w}} (store : Store L)
    (space : L.Namespace) (key : L.Key space) : Prop :=
  store space key = none

/-! ## First-order typed memory operations -/

/-- Typed sparse-memory syntax.  Reads retain the value observed.  Writes and
frees retain the exact prior value, preventing an accepted trace from hiding a
stale read.  Allocation carries no caller-authored freshness flag. -/
inductive Op (L : Layout.{u, v, w})
  | read (space : L.Namespace) (key : L.Key space)
      (observed : Option (L.Value space))
  | write (space : L.Namespace) (key : L.Key space)
      (before after : L.Value space)
  | allocate (space : L.Namespace) (key : L.Key space)
      (value : L.Value space)
  | free (space : L.Namespace) (key : L.Key space)
      (before : L.Value space)

namespace Op

/-- The sole address accessed by an operation. -/
def address {L : Layout.{u, v, w}} : Op L -> Address L
  | .read space key _ => ⟨space, key⟩
  | .write space key _ _ => ⟨space, key⟩
  | .allocate space key _ => ⟨space, key⟩
  | .free space key _ => ⟨space, key⟩

/-- The address modified by an operation, if any. -/
def writeAddress? {L : Layout.{u, v, w}} : Op L -> Option (Address L)
  | .read _ _ _ => none
  | op@(.write _ _ _ _) => some op.address
  | op@(.allocate _ _ _) => some op.address
  | op@(.free _ _ _) => some op.address

/-- The address freshly allocated by an operation, if any. -/
def allocationAddress? {L : Layout.{u, v, w}} : Op L -> Option (Address L)
  | op@(.allocate _ _ _) => some op.address
  | _ => none

/-- The address deallocated by an operation, if any. -/
def freeAddress? {L : Layout.{u, v, w}} : Op L -> Option (Address L)
  | op@(.free _ _ _) => some op.address
  | _ => none

/-- Semantic precondition for one operation.  Mutation discipline and stale
value checks are part of this relation, not proof-system side conditions. -/
def Enabled {L : Layout.{u, v, w}} (store : Store L) : Op L -> Prop
  | .read space key observed => store space key = observed
  | .write space key before _ =>
      L.discipline space = .ram /\ store space key = some before
  | .allocate space key _ =>
      L.discipline space ≠ .rom /\ Fresh store space key
  | .free space key before =>
      L.discipline space = .ram /\ store space key = some before

/-- Operation application is total syntax interpretation.  Acceptance must
also carry `Enabled`; application alone grants no authority or validity. -/
def apply {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    (store : Store L) : Op L -> Store L
  | .read _ _ _ => store
  | .write space key _ after => store.set space key (some after)
  | .allocate space key value => store.set space key (some value)
  | .free space key _ => store.set space key none

/-- A fresh allocation is accepted only at an absent address. -/
theorem allocate_enabled_fresh {L : Layout.{u, v, w}} (store : Store L)
    (space : L.Namespace) (key : L.Key space) (value : L.Value space)
    (enabled : Enabled store (.allocate space key value)) :
    Fresh store space key :=
  enabled.2

/-- ROM cannot contain an enabled modifying operation. -/
theorem no_enabled_rom_write {L : Layout.{u, v, w}} (store : Store L)
    (op : Op L) (enabled : Enabled store op)
    (rom : L.discipline op.address.1 = .rom) :
    op.writeAddress? = none := by
  cases op with
  | read => rfl
  | write space key before after =>
      simp only [Enabled] at enabled
      exact False.elim (Discipline.noConfusion (enabled.1.symm.trans rom))
  | allocate space key value =>
      simp only [Enabled] at enabled
      exact False.elim (enabled.1 rom)
  | free space key before =>
      simp only [Enabled] at enabled
      exact False.elim (Discipline.noConfusion (enabled.1.symm.trans rom))

/-- Append-only namespaces accept mutation only through fresh allocation. -/
theorem enabled_appendOnly_modification_is_allocate
    {L : Layout.{u, v, w}} (store : Store L) (op : Op L)
    (enabled : Enabled store op)
    (appendOnly : L.discipline op.address.1 = .appendOnly)
    (modifies : op.writeAddress? ≠ none) :
    op.allocationAddress? = some op.address := by
  cases op with
  | read => exact False.elim (modifies rfl)
  | write space key before after =>
      simp only [Enabled] at enabled
      exact False.elim (Discipline.noConfusion (enabled.1.symm.trans appendOnly))
  | allocate => rfl
  | free space key before =>
      simp only [Enabled] at enabled
      exact False.elim (Discipline.noConfusion (enabled.1.symm.trans appendOnly))

/-- One operation changes no address except its derived write address. -/
theorem apply_frame {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    (store : Store L) (op : Op L)
    (space : L.Namespace) (key : L.Key space)
    (outside : op.writeAddress? ≠ some (⟨space, key⟩ : Address L)) :
    (op.apply store) space key = store space key := by
  cases op with
  | read => rfl
  | write writeNamespace writeKey before after =>
      apply Store.set_ne
      simpa [writeAddress?, address] using outside.symm
  | allocate writeNamespace writeKey value =>
      apply Store.set_ne
      simpa [writeAddress?, address] using outside.symm
  | free writeNamespace writeKey before =>
      apply Store.set_ne
      simpa [writeAddress?, address] using outside.symm

end Op

/-! ## Exact trace execution and append-native footprints -/

namespace Trace

/-- Every accessed address, derived from syntax. -/
def accessFootprint {L : Layout.{u, v, w}} [DecidableEq (Address L)]
    (operations : List (Op L)) : Finset (Address L) :=
  (operations.map Op.address).toFinset

/-- Every modified address, derived from syntax.  Reads cannot enter it. -/
def writeFootprint {L : Layout.{u, v, w}} [DecidableEq (Address L)]
    (operations : List (Op L)) : Finset (Address L) :=
  (operations.filterMap Op.writeAddress?).toFinset

/-- Every freshly allocated address, derived from allocation syntax. -/
def allocationFootprint {L : Layout.{u, v, w}} [DecidableEq (Address L)]
    (operations : List (Op L)) : Finset (Address L) :=
  (operations.filterMap Op.allocationAddress?).toFinset

/-- Every freed address, derived from free syntax. -/
def freeFootprint {L : Layout.{u, v, w}} [DecidableEq (Address L)]
    (operations : List (Op L)) : Finset (Address L) :=
  (operations.filterMap Op.freeAddress?).toFinset

/-- Unconditional interpretation of a list.  Validity below checks each op at
the exact state produced by its prefix. -/
def run {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)] :
    Store L -> List (Op L) -> Store L
  | store, [] => store
  | store, operation :: rest => run (operation.apply store) rest

/-- Prefix-sensitive validity.  In particular, allocation freshness is tested
after every preceding operation, not merely against the initial state. -/
def ValidFrom {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)] :
    Store L -> List (Op L) -> Prop
  | _, [] => True
  | store, operation :: rest =>
      operation.Enabled store /\ ValidFrom (operation.apply store) rest

/-- The exact read/write trace relation.  There is no caller-selected post. -/
def Executes {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    (pre : Store L) (operations : List (Op L)) (post : Store L) : Prop :=
  ValidFrom pre operations /\ run pre operations = post

@[simp] theorem run_append {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    (pre : Store L) (left right : List (Op L)) :
    run pre (left ++ right) = run (run pre left) right := by
  induction left generalizing pre with
  | nil => rfl
  | cons operation rest induction =>
      simp only [List.cons_append, run]
      exact induction (operation.apply pre)

theorem validFrom_append {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    (pre : Store L) (left right : List (Op L)) :
    ValidFrom pre (left ++ right) <->
      ValidFrom pre left /\ ValidFrom (run pre left) right := by
  induction left generalizing pre with
  | nil => simp [ValidFrom, run]
  | cons operation rest induction =>
      simp only [List.cons_append, ValidFrom, run]
      rw [induction (operation.apply pre)]
      tauto

/-- Accepted traces compose by ordinary list append. -/
theorem Executes.append {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    {pre middle post : Store L} {left right : List (Op L)}
    (leftExecutes : Executes pre left middle)
    (rightExecutes : Executes middle right post) :
    Executes pre (left ++ right) post := by
  rcases leftExecutes with ⟨leftValid, leftPost⟩
  rcases rightExecutes with ⟨rightValid, rightPost⟩
  subst middle
  exact ⟨(validFrom_append pre left right).2 ⟨leftValid, rightValid⟩,
    (run_append pre left right).trans rightPost⟩

@[simp] theorem accessFootprint_append {L : Layout.{u, v, w}}
    [DecidableEq (Address L)] (left right : List (Op L)) :
    accessFootprint (left ++ right) =
      accessFootprint left ∪ accessFootprint right := by
  simp [accessFootprint]

@[simp] theorem writeFootprint_append {L : Layout.{u, v, w}}
    [DecidableEq (Address L)] (left right : List (Op L)) :
    writeFootprint (left ++ right) =
      writeFootprint left ∪ writeFootprint right := by
  simp [writeFootprint]

/-- Exactness/no-ghost: membership in the write footprint is equivalent to a
literal modifying operation in the trace. -/
theorem mem_writeFootprint_iff {L : Layout.{u, v, w}}
    [DecidableEq (Address L)] (operations : List (Op L)) (address : Address L) :
    address ∈ writeFootprint operations <->
      exists operation, operation ∈ operations /\
        operation.writeAddress? = some address := by
  simp [writeFootprint]

/-- Exactness/no-ghost for the allocation subset. -/
theorem mem_allocationFootprint_iff {L : Layout.{u, v, w}}
    [DecidableEq (Address L)] (operations : List (Op L)) (address : Address L) :
    address ∈ allocationFootprint operations <->
      exists operation, operation ∈ operations /\
        operation.allocationAddress? = some address := by
  simp [allocationFootprint]

/-- The whole-trace frame law. -/
theorem run_frame {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    (pre : Store L) (operations : List (Op L))
    (space : L.Namespace) (key : L.Key space)
    (outside : (⟨space, key⟩ : Address L) ∉ writeFootprint operations) :
    (run pre operations) space key = pre space key := by
  induction operations generalizing pre with
  | nil => rfl
  | cons operation rest induction =>
      have headOutside :
          operation.writeAddress? ≠ some (⟨space, key⟩ : Address L) := by
        intro equality
        exact outside ((mem_writeFootprint_iff (operation :: rest)
          (⟨space, key⟩ : Address L)).2
            ⟨operation, List.mem_cons_self, equality⟩)
      have tailOutside :
          (⟨space, key⟩ : Address L) ∉ writeFootprint rest := by
        intro member
        rcases (mem_writeFootprint_iff rest
          (⟨space, key⟩ : Address L)).1 member with
          ⟨tailOperation, tailMember, equality⟩
        exact outside ((mem_writeFootprint_iff (operation :: rest)
          (⟨space, key⟩ : Address L)).2
            ⟨tailOperation, List.mem_cons_of_mem _ tailMember, equality⟩)
      rw [run, induction (operation.apply pre) tailOutside]
      exact operation.apply_frame pre space key headOutside

/-- Contrapositive frame: every actual post-state change is named by the exact
derived write footprint. -/
theorem changed_only_in_writeFootprint {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    (pre : Store L) (operations : List (Op L))
    (space : L.Namespace) (key : L.Key space)
    (changed : (run pre operations) space key ≠ pre space key) :
    (⟨space, key⟩ : Address L) ∈ writeFootprint operations := by
  by_contra outside
  exact changed (run_frame pre operations space key outside)

end Trace

/-! ## Canonical materialization and accepted executions -/

/-- A deployment's declared canonical state encoding and root function.  The
root is derived from the exact encoded store.  No collision-resistance or
binding theorem is smuggled into this interface. -/
structure Materializer (L : Layout.{u, v, w}) (Root : Type r) where
  codec : LawfulCodec (Store L)
  rootBytes : List UInt8 -> Root

/-- The private constructor carries only logical state; bytes and root are
projections through the sole materializer. -/
structure Materialized {L : Layout.{u, v, w}} {Root : Type r}
    (materializer : Materializer L Root) where
  private mk ::
  logical : Store L

def materialize {L : Layout.{u, v, w}} {Root : Type r}
    (materializer : Materializer L Root) (logical : Store L) :
    Materialized materializer :=
  ⟨logical⟩

def Materialized.bytes {L : Layout.{u, v, w}} {Root : Type r}
    {materializer : Materializer L Root} (state : Materialized materializer) :
    List UInt8 :=
  materializer.codec.encode state.logical

def Materialized.root {L : Layout.{u, v, w}} {Root : Type r}
    {materializer : Materializer L Root} (state : Materialized materializer) : Root :=
  materializer.rootBytes state.bytes

@[simp] theorem materialize_root {L : Layout.{u, v, w}} {Root : Type r}
    (materializer : Materializer L Root) (logical : Store L) :
    (materialize materializer logical).root =
      materializer.rootBytes (materializer.codec.encode logical) :=
  rfl

/-- An accepted execution retains only prefix validity.  Its post-state, bytes,
root, and footprints are all derived projections. -/
structure AcceptedExecution {L : Layout.{u, v, w}} {Root : Type r}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    (materializer : Materializer L Root) (pre : Materialized materializer)
    (operations : List (Op L)) : Prop where
  valid : Trace.ValidFrom pre.logical operations

namespace AcceptedExecution

variable {L : Layout.{u, v, w}} {Root : Type r}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    {materializer : Materializer L Root} {pre : Materialized materializer}
    {operations : List (Op L)}

/-- The only post-state: run the exact accepted operations and rematerialize. -/
def post (_accepted : AcceptedExecution materializer pre operations) :
    Materialized materializer :=
  materialize materializer (Trace.run pre.logical operations)

@[simp] theorem post_logical
    (accepted : AcceptedExecution materializer pre operations) :
    accepted.post.logical = Trace.run pre.logical operations :=
  rfl

@[simp] theorem post_root
    (accepted : AcceptedExecution materializer pre operations) :
    accepted.post.root = materializer.rootBytes
      (materializer.codec.encode (Trace.run pre.logical operations)) :=
  rfl

theorem executes (accepted : AcceptedExecution materializer pre operations) :
    Trace.Executes pre.logical operations accepted.post.logical :=
  ⟨accepted.valid, rfl⟩

theorem frame (accepted : AcceptedExecution materializer pre operations)
    (space : L.Namespace) (key : L.Key space)
    (outside : (⟨space, key⟩ : Address L) ∉
      Trace.writeFootprint operations) :
    accepted.post.logical space key = pre.logical space key :=
  Trace.run_frame pre.logical operations space key outside

theorem changed_only_declared
    (accepted : AcceptedExecution materializer pre operations)
    (space : L.Namespace) (key : L.Key space)
    (changed : accepted.post.logical space key ≠ pre.logical space key) :
    (⟨space, key⟩ : Address L) ∈ Trace.writeFootprint operations :=
  Trace.changed_only_in_writeFootprint pre.logical operations space key changed

end AcceptedExecution

/-! ## Exact timestamped lookup-bus projection -/

inductive AccessKind
  | read
  | write
  | allocate
  | free
  deriving DecidableEq, Repr

/-- A heterogeneous bus row.  Before/after values retain their namespace type.
`clock` is the operation's exact zero-based position in the trace. -/
structure BusRow (L : Layout.{u, v, w}) where
  clock : Nat
  kind : AccessKind
  space : L.Namespace
  key : L.Key space
  before : Option (L.Value space)
  after : Option (L.Value space)

/-- The bus row selected by one operation at one exact prefix state. -/
def Op.busRow {L : Layout.{u, v, w}} (clock : Nat) (store : Store L) :
    Op L -> BusRow L
  | .read space key observed =>
      ⟨clock, .read, space, key, observed, observed⟩
  | .write space key before after =>
      ⟨clock, .write, space, key, some before, some after⟩
  | .allocate space key value =>
      ⟨clock, .allocate, space, key, none, some value⟩
  | .free space key before =>
      ⟨clock, .free, space, key, some before, none⟩

namespace Trace

/-- Derive one timestamped row per operation while threading exact prefix
states.  This is the semantic source for a future LogUp*/Twist encoding. -/
def busRowsFrom {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)] :
    Nat -> Store L -> List (Op L) -> List (BusRow L)
  | _, _, [] => []
  | clock, store, operation :: rest =>
      operation.busRow clock store ::
        busRowsFrom (clock + 1) (operation.apply store) rest

def busRows {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    (pre : Store L) (operations : List (Op L)) : List (BusRow L) :=
  busRowsFrom 0 pre operations

/-- The sequential memory-bus relation.  Every row is the literal projection
of one enabled operation at its exact prefix state, and the next row consumes
the state produced by that operation. -/
inductive BusRelation {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)] :
    Nat -> Store L -> List (Op L) -> List (BusRow L) -> Store L -> Prop
  | nil (clock : Nat) (store : Store L) :
      BusRelation clock store [] [] store
  | cons {clock : Nat} {store post : Store L} {operation : Op L}
      {operations : List (Op L)} {rows : List (BusRow L)}
      (enabled : operation.Enabled store)
      (tail : BusRelation (clock + 1) (operation.apply store)
        operations rows post) :
      BusRelation clock store (operation :: operations)
        (operation.busRow clock store :: rows) post

/-- Prefix-valid execution generates an exact sequential bus relation. -/
theorem busRelation_of_valid {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    (clock : Nat) (pre : Store L) (operations : List (Op L))
    (valid : ValidFrom pre operations) :
    BusRelation clock pre operations (busRowsFrom clock pre operations)
      (run pre operations) := by
  induction operations generalizing clock pre with
  | nil => exact .nil clock pre
  | cons operation rest induction =>
      exact .cons valid.1
        (induction (clock + 1) (operation.apply pre) valid.2)

/-- The bus relation determines the derived row list exactly. -/
theorem BusRelation.rows_exact {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    {clock : Nat} {pre post : Store L} {operations : List (Op L)}
    {rows : List (BusRow L)}
    (relation : BusRelation clock pre operations rows post) :
    rows = busRowsFrom clock pre operations := by
  induction relation with
  | nil => rfl
  | cons enabled tail induction =>
      simp only [busRowsFrom]
      exact congrArg _ induction

/-- The bus relation also determines the final store exactly. -/
theorem BusRelation.post_exact {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    {clock : Nat} {pre post : Store L} {operations : List (Op L)}
    {rows : List (BusRow L)}
    (relation : BusRelation clock pre operations rows post) :
    post = run pre operations := by
  induction relation with
  | nil => rfl
  | cons enabled tail induction =>
      simpa only [run] using induction

@[simp] theorem busRowsFrom_length {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    (clock : Nat) (pre : Store L) (operations : List (Op L)) :
    (busRowsFrom clock pre operations).length = operations.length := by
  induction operations generalizing clock pre with
  | nil => rfl
  | cons operation rest induction =>
      simp [busRowsFrom, induction]

@[simp] theorem busRows_length {L : Layout.{u, v, w}}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    (pre : Store L) (operations : List (Op L)) :
    (busRows pre operations).length = operations.length := by
  exact busRowsFrom_length 0 pre operations

end Trace

/-- The honest semantic seam to a lookup/permutation proof dialect.  Roots are
the canonical state roots above and rows are literal trace projections.  A
proof compiler may encode this claim, but cannot replace either equality with
a free digest or prover-selected row list. -/
structure ExactBusClaim {L : Layout.{u, v, w}} {Root : Type r}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    {materializer : Materializer L Root} {pre : Materialized materializer}
    {operations : List (Op L)}
    (accepted : AcceptedExecution materializer pre operations) where
  preRoot : Root
  postRoot : Root
  rows : List (BusRow L)
  preRoot_exact : preRoot = pre.root
  postRoot_exact : postRoot = accepted.post.root
  rows_exact : rows = Trace.busRows pre.logical operations
  rows_semantic : Trace.BusRelation 0 pre.logical operations rows
    accepted.post.logical

def AcceptedExecution.exactBusClaim {L : Layout.{u, v, w}} {Root : Type r}
    [DecidableEq L.Namespace] [(space : L.Namespace) -> DecidableEq (L.Key space)]
    {materializer : Materializer L Root} {pre : Materialized materializer}
    {operations : List (Op L)}
    (accepted : AcceptedExecution materializer pre operations) :
    ExactBusClaim accepted where
  preRoot := pre.root
  postRoot := accepted.post.root
  rows := Trace.busRows pre.logical operations
  preRoot_exact := rfl
  postRoot_exact := rfl
  rows_exact := rfl
  rows_semantic := Trace.busRelation_of_valid 0 pre.logical operations accepted.valid

/-! ## A concrete allocation tooth -/

namespace Example

inductive Namespace
  | code
  | heap
  | log
  deriving DecidableEq, Repr

def layout : Layout where
  Namespace := Namespace
  Key := fun _ => Nat
  Value := fun _ => Nat
  discipline
    | .code => .rom
    | .heap => .ram
    | .log => .appendOnly

instance : DecidableEq layout.Namespace := by
  change DecidableEq Namespace
  infer_instance

instance (space : layout.Namespace) : DecidableEq (layout.Key space) := by
  change DecidableEq Nat
  infer_instance

instance (space : layout.Namespace) : DecidableEq (layout.Value space) := by
  change DecidableEq Nat
  infer_instance

def empty : Store layout := fun _ _ => none

def allocateSeven : Op layout :=
  @Op.allocate layout .heap (7 : Nat) (42 : Nat)

example : allocateSeven.Enabled empty := by
  simp [allocateSeven, Op.Enabled, layout, empty, Fresh]

example : (allocateSeven.apply empty) .heap (7 : Nat) = some (42 : Nat) := by
  decide

/-- Freshness has teeth: the same allocation cannot execute twice. -/
theorem duplicate_allocation_rejected :
    ¬ (@Op.allocate layout .heap (7 : Nat) (42 : Nat)).Enabled
      ((@Op.allocate layout .heap (7 : Nat) (42 : Nat)).apply empty) := by
  simp [Op.Enabled, Op.apply, layout, empty, Fresh, Store.set]

/-- ROM overwrite is not an enabled semantic operation. -/
theorem rom_write_rejected :
    ¬ (@Op.write layout .code (0 : Nat) (1 : Nat) (2 : Nat)).Enabled
      (show Store layout from fun (space : Namespace) (_ : Nat) =>
        if space = Namespace.code then some (1 : Nat) else none) := by
  simp [Op.Enabled, layout]

end Example

/-- info: 'Minidregg.Kernel.SparseAuthenticatedState.Store.set_ne' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Store.set_ne
/-- info: 'Minidregg.Kernel.SparseAuthenticatedState.Trace.run_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Trace.run_frame
/-- info: 'Minidregg.Kernel.SparseAuthenticatedState.Trace.mem_writeFootprint_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Trace.mem_writeFootprint_iff
/-- info: 'Minidregg.Kernel.SparseAuthenticatedState.Trace.BusRelation.rows_exact' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Trace.BusRelation.rows_exact
/-- info: 'Minidregg.Kernel.SparseAuthenticatedState.AcceptedExecution.changed_only_declared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AcceptedExecution.changed_only_declared
/-- info: 'Minidregg.Kernel.SparseAuthenticatedState.Example.duplicate_allocation_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Example.duplicate_allocation_rejected

end Minidregg.Kernel.SparseAuthenticatedState
