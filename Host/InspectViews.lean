/-
# Host.InspectViews — the moldable inspector's first views (K-INSPECT-VIEWS)

Each view is a pure Lean function over bytes the client already holds: signed
capability views, its own signed plans and outcome frames, a signed policy view,
its own resource view. A view opens no Store and asks the Host nothing; it is
the same function the operator and a friend run (`inspect KIND IN OUT`).

* `capTree`   — the delegation tree over the capability records the reader holds.
* `lawTokens` — the token sequence the shell's law grammar prints a compiled law
  as (`LawLeaf.renderClause` is its concatenation), and its parser.
* `suggest`   — for a failing clause, the value of the one request slot that would
  satisfy that clause, computed from the clause and the refusal's own values.
* `turnSlots` — a signing plan's slots with their decoded footprints.
-/
import Compiler.NativeHostCodec
import Compiler.PlanFootprintCodec
import Compiler.CredentialAuthorityCell
import Kernel.CapabilityDelegationController
import Kernel.CredentialSignedEnvelopeController
import Theory.AssertAxioms
import Mathlib.Data.List.Dedup

namespace Minidregg.Host.InspectViews

open Minidregg.Compiler
open Minidregg.Pred
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory
open Minidregg.Kernel

set_option autoImplicit false

/-! ## §1. The capability tree -/

/-- With no recorded parents a cell descends only from itself. -/
theorem descends_empty {c r : Nat} (d : Parentage.empty.Descends c r) : c = r := by
  cases d with
  | refl => rfl
  | step link _ => exact absurd link (by simp [Parentage.empty, CoeFun.coe])

/-- Narrowing with no recorded parents is narrowing under EVERY parent
projection: the room map only adds descents. The cap tree holds no room map
(it renders bytes the reader holds), so it decides narrowing at `empty`, and
what it draws narrows whatever the Store's parentage is. -/
theorem narrows_of_empty {kind : ResourceKind} {child parent : Scope kind}
    (h : child.Narrows parent Parentage.empty) (parentage : Parentage) :
    child.Narrows parent parentage := by
  refine ⟨?_, h.verbs, h.maxCost, h.fields, h.maxDelta⟩
  have t := h.targets
  revert t
  cases ct : child.targets <;> cases pt : parent.targets <;>
    simp only [TargetSet.Narrows] <;> intro t
  · exact t
  · intro x mem
    rw [descends_empty (t x mem)]
    exact .refl _
  · exact t.elim
  · rw [descends_empty t]
    exact .refl _

/-- Where a capability the reader can see came from. -/
inductive Source where
  /-- The head of a stored record returned by a signed `capability` view. -/
  | record
  /-- A parent link inside such a record's stored lineage. -/
  | lineage
  /-- The child of a delegation this reader signed (its own plan), with the
  Host's verdict on that plan when the reader holds one. -/
  | delegated (proposal : String) (confirmed : Option Bool)
  deriving DecidableEq, Repr

/-- One piece of held evidence. -/
inductive Item (kind : ResourceKind) where
  | record (stored : StoredCapability kind)
  | delegated (proposal : String) (child : Capability kind) (confirmed : Option Bool)
  /-- A signed `capability` view of `id` that the Host refused, with its reason. -/
  | refused (id : Nat) (reason : RefusalReason)

/-- The capabilities an item shows, with where each came from. -/
def Item.known {kind : ResourceKind} : Item kind → List (Capability kind × Source)
  | .record stored => (stored.head, .record) :: stored.ancestry.map (fun link => (link.parent, .lineage))
  | .delegated proposal child confirmed => [(child, .delegated proposal confirmed)]
  | .refused _ _ => []

/-- The capability ids an item names. -/
def Item.ids {kind : ResourceKind} : Item kind → List Nat
  | .refused id _ => [id]
  | item => item.known.map (fun known => known.1.id.value)

def Item.refusals {kind : ResourceKind} (id : Nat) : Item kind → List RefusalReason
  | .refused named reason => if named = id then [reason] else []
  | _ => []

structure Node (kind : ResourceKind) where
  id : Nat
  /-- The capability, when some held evidence carries it; `none` is `[not readable]`. -/
  cap : Option (Capability kind)
  sources : List Source
  refusals : List RefusalReason
  /-- Two pieces of evidence carry different capabilities under this id. -/
  conflict : Bool

def Node.revoked {kind : ResourceKind} (node : Node kind) : Bool :=
  node.refusals.contains .revoked

def allKnown {kind : ResourceKind} (items : List (Item kind)) : List (Capability kind × Source) :=
  items.flatMap Item.known

/-- Every id the input names: the items' own, then every parent a known capability names. -/
def inputIds {kind : ResourceKind} (items : List (Item kind)) : List Nat :=
  items.flatMap Item.ids

def parentIds {kind : ResourceKind} (items : List (Item kind)) : List Nat :=
  (allKnown items).filterMap (fun known => known.1.parent.map (·.value))

def nodeOf {kind : ResourceKind} (items : List (Item kind)) (id : Nat) : Node kind :=
  let found := (allKnown items).filter (fun known => known.1.id.value = id)
  { id
    cap := found.head?.map (·.1)
    sources := found.map (·.2)
    refusals := items.flatMap (Item.refusals id)
    conflict := found.any (fun known => some known.1 != found.head?.map (·.1)) }

structure Edge (kind : ResourceKind) where
  child : Capability kind
  parent : Capability kind

structure CapTree (kind : ResourceKind) where
  nodes : List (Node kind)
  /-- Parent links whose parent is readable and which narrow it. -/
  edges : List (Edge kind)
  /-- Parent links whose parent is readable but which do NOT narrow it. -/
  widenings : List (Edge kind)

/-- The readable parent a capability names, if the tree holds one. -/
def parentIn {kind : ResourceKind} (nodes : List (Node kind)) (child : Capability kind) :
    Option (Capability kind) := do
  let parentId ← child.parent
  let node ← nodes.find? (fun node => node.id = parentId.value)
  let parent ← node.cap
  if parent.id = parentId then some parent else none

def links {kind : ResourceKind} (nodes : List (Node kind)) : List (Edge kind) :=
  nodes.filterMap fun node => do
    let child ← node.cap
    let parent ← parentIn nodes child
    pure ⟨child, parent⟩

def capTree {kind : ResourceKind} (items : List (Item kind)) : CapTree kind :=
  let nodes := (inputIds items ++ parentIds items).dedup.map (nodeOf items)
  { nodes
    edges := (links nodes).filter (fun edge => decide (edge.child.scope.Narrows edge.parent.scope Parentage.empty))
    widenings := (links nodes).filter (fun edge => !decide (edge.child.scope.Narrows edge.parent.scope Parentage.empty)) }

theorem parentIn_names {kind : ResourceKind} (nodes : List (Node kind))
    (child parent : Capability kind) (found : parentIn nodes child = some parent) :
    child.parent = some parent.id := by
  unfold parentIn at found
  cases hp : child.parent with
  | none => simp [hp] at found
  | some parentId =>
    cases hn : nodes.find? (fun node => node.id = parentId.value) with
    | none => simp [hp, hn] at found
    | some node =>
      cases hc : node.cap with
      | none => simp [hp, hn, hc] at found
      | some cap =>
        simp only [hp, hn, hc, Option.bind_eq_bind, Option.bind_some] at found
        split at found
        · rename_i same
          simp only [Option.some.injEq] at found
          subst found
          simp [same]
        · simp at found

theorem mem_links {kind : ResourceKind} (nodes : List (Node kind)) (edge : Edge kind)
    (linked : edge ∈ links nodes) : parentIn nodes edge.child = some edge.parent := by
  simp only [links, List.mem_filterMap] at linked
  obtain ⟨node, _, made⟩ := linked
  cases hcap : node.cap with
  | none => simp [hcap] at made
  | some child =>
    cases hparent : parentIn nodes child with
    | none => simp [hcap, hparent] at made
    | some parent =>
      simp only [hcap, hparent, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at made
      subst made
      exact hparent

/-- The view cannot draw a widening edge: every drawn edge joins a capability to
the parent it names, and the child's scope narrows the parent's under every
parent projection (the Store's, whatever it records). -/
theorem capTree_edges_narrow {kind : ResourceKind} (items : List (Item kind))
    (edge : Edge kind) (drawn : edge ∈ (capTree items).edges) :
    edge.child.parent = some edge.parent.id ∧
      ∀ parentage, edge.child.scope.Narrows edge.parent.scope parentage := by
  have drawn' := drawn
  simp only [capTree, List.mem_filter, decide_eq_true_eq] at drawn'
  exact ⟨parentIn_names _ _ _ (mem_links _ _ drawn'.1), narrows_of_empty drawn'.2⟩

/-- Every capability id the input names appears as exactly one node. -/
theorem capTree_complete_over_input {kind : ResourceKind} (items : List (Item kind))
    (id : Nat) (named : id ∈ inputIds items) :
    ((capTree items).nodes.map Node.id).count id = 1 := by
  have ids : (capTree items).nodes.map Node.id = (inputIds items ++ parentIds items).dedup := by
    simp only [capTree, List.map_map]
    conv => rhs; rw [← List.map_id (inputIds items ++ parentIds items).dedup]
    rfl
  rw [ids]
  exact List.count_eq_one_of_mem (List.nodup_dedup _)
    (List.mem_dedup.mpr (List.mem_append_left _ named))

/-- A parent link to a readable parent is drawn either as an edge or as a widening. -/
theorem capTree_links_accounted {kind : ResourceKind} (items : List (Item kind))
    (edge : Edge kind) (linked : edge ∈ links (capTree items).nodes) :
    edge ∈ (capTree items).edges ∨ edge ∈ (capTree items).widenings := by
  simp only [capTree] at linked ⊢
  by_cases narrows : edge.child.scope.Narrows edge.parent.scope Parentage.empty
  · left; simp [List.mem_filter, linked, narrows]
  · right; simp [List.mem_filter, linked, narrows]

/-! ## §2. The law, in the shell's one-line grammar -/

/-- A token of the law grammar. Each carries its own text (`Tok.text`), spacing
included, so a law's printed form is the concatenation of its tokens' texts. -/
inductive Tok where
  | slot (s : Slot)
  | slots (ss : List Slot)
  | num (s : Slot) (v : Int)
  | set (s : Slot) (xs : List Int)
  | vk (id : String)
  | eqeq | le | inn | writeOnce | monotone | plus
  | notOpen | close | allOpen | anyOpen | listClose | comma
  | openLaw | sealedLaw | witnessed
  | hashOpen | hashClose | ranKw | sumKw
  | nat (n : Nat)
  deriving DecidableEq, Repr

def Tok.text : Tok → String
  | .slot s => LawLeaf.renderSlot s
  | .slots ss => ", ".intercalate (ss.map LawLeaf.renderSlot)
  | .num s v => LawLeaf.renderValue s v
  | .set s xs => LawLeaf.renderSet s xs
  | .vk id => id.quote
  | .eqeq => " == " | .le => " <= " | .inn => " in "
  | .writeOnce => " writeOnce" | .monotone => " monotone" | .plus => " + "
  | .notOpen => "not (" | .close => ")" | .allOpen => "all [ " | .anyOpen => "any [ "
  | .listClose => " ]" | .comma => ", "
  | .openLaw => "open" | .sealedLaw => "sealed" | .witnessed => "witnessed "
  | .hashOpen => " opens (" | .hashClose => ") with " | .ranKw => "ran " | .sumKw => "sum ("
  | .nat n => toString n

mutual
def lawTokens : Pred → List Tok
  | .eq s v => [.slot s, .eqeq, .num s v]
  | .le s v => [.slot s, .le, .num s v]
  | .memberOf s xs => [.slot s, .inn, .set s xs]
  | .writeOnce s => [.slot s, .writeOnce]
  | .monotone s => [.slot s, .monotone]
  | .witnessed vk => [.witnessed, .vk vk.id]
  | .eqSlots a b => [.slot a, .eqeq, .slot b]
  | .leSlots a b => [.slot a, .le, .slot b]
  | .leSlotsOff a b k => [.slot a, .le, .slot b, .plus, .num "" k]
  | .sumEq l r => [.sumKw, .slots l, .close, .eqeq, .sumKw, .slots r, .close]
  | .hashEq vs b c => [.slot c, .hashOpen, .slots vs, .hashClose, .slot b]
  | .ran program => [.ranKw, .nat program]
  | .not q => .notOpen :: lawTokens q ++ [.close]
  | .allL .nil => [.openLaw]
  | .anyL .nil => [.sealedLaw]
  | .allL (.cons q rest) => .allOpen :: lawTokens q ++ lawTokensTail rest ++ [.listClose]
  | .anyL (.cons q rest) => .anyOpen :: lawTokens q ++ lawTokensTail rest ++ [.listClose]
def lawTokensTail : PredList → List Tok
  | .nil => []
  | .cons q rest => .comma :: lawTokens q ++ lawTokensTail rest
end

/-- Concatenation of strings, right-nested. -/
def cat : List String → String
  | [] => ""
  | s :: rest => s ++ cat rest

theorem cat_append (a b : List String) : cat (a ++ b) = cat a ++ cat b := by
  induction a with
  | nil => simp [cat]
  | cons s rest ih => simp [cat, ih, String.append_assoc]

@[simp] theorem string_toString (s : String) : toString s = s := rfl

@[simp] theorem renderValue_empty (k : Int) : LawLeaf.renderValue "" k = toString k := by
  simp [LawLeaf.renderValue]

def textOf (tokens : List Tok) : String := cat (tokens.map Tok.text)

theorem textOf_append (a b : List Tok) : textOf (a ++ b) = textOf a ++ textOf b := by
  simp [textOf, List.map_append, cat_append]

theorem textOf_cons (t : Tok) (rest : List Tok) : textOf (t :: rest) = t.text ++ textOf rest := rfl

mutual
/-- The printed law is exactly the concatenation of its tokens' texts: the
tokens are the printer `LawLeaf.renderClause` (the one OUTCOME `explain` uses). -/
theorem textOf_lawTokens : (p : Pred) → textOf (lawTokens p) = LawLeaf.renderClause p
  | .eq s v => by simp [lawTokens, textOf, cat, Tok.text, LawLeaf.renderClause, String.append_assoc]
  | .le s v => by simp [lawTokens, textOf, cat, Tok.text, LawLeaf.renderClause, String.append_assoc]
  | .memberOf s xs => by simp [lawTokens, textOf, cat, Tok.text, LawLeaf.renderClause, String.append_assoc]
  | .writeOnce s => by simp [lawTokens, textOf, cat, Tok.text, LawLeaf.renderClause, String.append_assoc]
  | .monotone s => by simp [lawTokens, textOf, cat, Tok.text, LawLeaf.renderClause, String.append_assoc]
  | .witnessed vk => by simp [lawTokens, textOf, cat, Tok.text, LawLeaf.renderClause, String.append_assoc]
  | .eqSlots a b => by simp [lawTokens, textOf, cat, Tok.text, LawLeaf.renderClause, String.append_assoc]
  | .leSlots a b => by simp [lawTokens, textOf, cat, Tok.text, LawLeaf.renderClause, String.append_assoc]
  | .leSlotsOff a b k => by simp [lawTokens, textOf, cat, Tok.text, LawLeaf.renderClause, String.append_assoc]
  | .sumEq l r => by
      simp only [lawTokens, textOf, cat, List.map, Tok.text, LawLeaf.renderClause,
        String.append_assoc, String.append_empty]
  | .hashEq v b c => by simp [lawTokens, textOf, cat, Tok.text, LawLeaf.renderClause, String.append_assoc]
  | .ran program => by simp [lawTokens, textOf, cat, Tok.text, LawLeaf.renderClause, String.append_assoc]
  | .not q => by
      simp only [lawTokens, List.cons_append, textOf_cons, textOf_append, textOf_lawTokens q]
      simp [textOf, cat, Tok.text, LawLeaf.renderClause, String.append_assoc]
  | .allL .nil => by simp [lawTokens, textOf, cat, Tok.text, LawLeaf.renderClause]
  | .anyL .nil => by simp [lawTokens, textOf, cat, Tok.text, LawLeaf.renderClause]
  | .allL (.cons q rest) => by
      have tail := textOf_lawTokensTail q rest
      simp only [lawTokens, List.cons_append, List.append_assoc, textOf_cons, textOf_append,
        textOf_lawTokens q, LawLeaf.renderClause]
      rw [← tail]
      simp [textOf, cat, Tok.text, String.append_assoc]
  | .anyL (.cons q rest) => by
      have tail := textOf_lawTokensTail q rest
      simp only [lawTokens, List.cons_append, List.append_assoc, textOf_cons, textOf_append,
        textOf_lawTokens q, LawLeaf.renderClause]
      rw [← tail]
      simp [textOf, cat, Tok.text, String.append_assoc]
/-- `renderClauses (q :: rest)` is `q`'s text followed by the tail's tokens. -/
theorem textOf_lawTokensTail : (q : Pred) → (rest : PredList) →
    LawLeaf.renderClause q ++ textOf (lawTokensTail rest) =
      LawLeaf.renderClauses (.cons q rest)
  | q, .nil => by simp [lawTokensTail, textOf, cat, LawLeaf.renderClauses]
  | q, .cons r rest => by
      simp only [lawTokensTail, List.cons_append, textOf_cons, textOf_append, textOf_lawTokens r]
      rw [← String.append_assoc, textOf_lawTokensTail r rest]
      simp [Tok.text, LawLeaf.renderClauses, String.append_assoc]
end

/-- What may follow a clause: nothing, a comma, or a closing bracket/paren. -/
def follows : List Tok → Bool
  | [] | .comma :: _ | .listClose :: _ | .close :: _ => true
  | _ => false

mutual
def parseClause : Nat → List Tok → Option (Pred × List Tok)
  | 0, _ => none
  | _ + 1, .openLaw :: r => some (.allL .nil, r)
  | _ + 1, .sealedLaw :: r => some (.anyL .nil, r)
  | _ + 1, .witnessed :: .vk id :: r => some (.witnessed ⟨id⟩, r)
  | _ + 1, .slot c :: .hashOpen :: .slots vs :: .hashClose :: .slot b :: r =>
      some (.hashEq vs b c, r)
  | _ + 1, .ranKw :: .nat program :: r => some (.ran program, r)
  | _ + 1, .sumKw :: .slots l :: .close :: .eqeq :: .sumKw :: .slots rs :: .close :: r =>
      some (.sumEq l rs, r)
  | n + 1, .notOpen :: r => match parseClause n r with
      | some (q, .close :: r) => some (.not q, r)
      | _ => none
  | n + 1, .allOpen :: r => match parseClause n r with
      | some (q, r) => match parseTail n r with
        | some (rest, .listClose :: r) => some (.allL (.cons q rest), r)
        | _ => none
      | none => none
  | n + 1, .anyOpen :: r => match parseClause n r with
      | some (q, r) => match parseTail n r with
        | some (rest, .listClose :: r) => some (.anyL (.cons q rest), r)
        | _ => none
      | none => none
  | _ + 1, .slot s :: .eqeq :: .num _ v :: r => some (.eq s v, r)
  | _ + 1, .slot s :: .le :: .num _ v :: r => some (.le s v, r)
  | _ + 1, .slot s :: .inn :: .set _ xs :: r => some (.memberOf s xs, r)
  | _ + 1, .slot s :: .writeOnce :: r => some (.writeOnce s, r)
  | _ + 1, .slot s :: .monotone :: r => some (.monotone s, r)
  | _ + 1, .slot a :: .eqeq :: .slot b :: r => some (.eqSlots a b, r)
  | _ + 1, .slot a :: .le :: .slot b :: .plus :: .num _ k :: r => some (.leSlotsOff a b k, r)
  | _ + 1, .slot a :: .le :: .slot b :: r => some (.leSlots a b, r)
  | _ + 1, _ => none
def parseTail : Nat → List Tok → Option (PredList × List Tok)
  | 0, _ => none
  | n + 1, .comma :: r => match parseClause n r with
      | some (q, r) => match parseTail n r with
        | some (rest, r) => some (.cons q rest, r)
        | none => none
      | none => none
  | _ + 1, r => some (.nil, r)
end

mutual
/-- The fuel a clause's parse needs. -/
def fuel : Pred → Nat
  | .not q => fuel q + 1
  | .allL (.cons q rest) => max (fuel q) (fuelTail rest) + 1
  | .anyL (.cons q rest) => max (fuel q) (fuelTail rest) + 1
  | _ => 0
def fuelTail : PredList → Nat
  | .nil => 0
  | .cons q rest => max (fuel q) (fuelTail rest) + 1
end

mutual
theorem parseClause_lawTokens : (p : Pred) → (n : Nat) → fuel p < n → (r : List Tok) →
    follows r = true → parseClause n (lawTokens p ++ r) = some (p, r)
  | .eq s v, n + 1, _, r, _ => by simp [lawTokens, parseClause]
  | .le s v, n + 1, _, r, _ => by simp [lawTokens, parseClause]
  | .memberOf s xs, n + 1, _, r, _ => by simp [lawTokens, parseClause]
  | .writeOnce s, n + 1, _, r, _ => by simp [lawTokens, parseClause]
  | .monotone s, n + 1, _, r, _ => by simp [lawTokens, parseClause]
  | .witnessed vk, n + 1, _, r, _ => by simp [lawTokens, parseClause]
  | .eqSlots a b, n + 1, _, r, _ => by simp [lawTokens, parseClause]
  | .leSlotsOff a b k, n + 1, _, r, _ => by simp [lawTokens, parseClause]
  | .sumEq l rs, n + 1, _, r, _ => by simp [lawTokens, parseClause]
  | .hashEq v b c, n + 1, _, r, _ => by simp [lawTokens, parseClause]
  | .ran program, n + 1, _, r, _ => by simp [lawTokens, parseClause]
  | .leSlots a b, n + 1, _, r, hr => by
      match r, hr with
      | [], _ => simp [lawTokens, parseClause]
      | .comma :: r, _ => simp [lawTokens, parseClause]
      | .listClose :: r, _ => simp [lawTokens, parseClause]
      | .close :: r, _ => simp [lawTokens, parseClause]
  | .allL .nil, n + 1, _, r, _ => by simp [lawTokens, parseClause]
  | .anyL .nil, n + 1, _, r, _ => by simp [lawTokens, parseClause]
  | .not q, n + 1, h, r, _ => by
      have inner := parseClause_lawTokens q n (by simp [fuel] at h; omega) (.close :: r) rfl
      simp only [lawTokens, List.cons_append, List.append_assoc, List.singleton_append]
      simp [parseClause, inner]
  | .allL (.cons q rest), n + 1, h, r, _ => by
      simp only [fuel] at h
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have tail := parseTail_lawTokensTail rest m (by omega) r
      have first := parseClause_lawTokens q (m + 1) (by omega) (lawTokensTail rest ++ .listClose :: r)
        (by cases rest <;> simp [lawTokensTail, follows])
      simp only [lawTokens, List.cons_append, List.append_assoc, List.singleton_append]
      simp [parseClause, first, tail]
  | .anyL (.cons q rest), n + 1, h, r, _ => by
      simp only [fuel] at h
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have tail := parseTail_lawTokensTail rest m (by omega) r
      have first := parseClause_lawTokens q (m + 1) (by omega) (lawTokensTail rest ++ .listClose :: r)
        (by cases rest <;> simp [lawTokensTail, follows])
      simp only [lawTokens, List.cons_append, List.append_assoc, List.singleton_append]
      simp [parseClause, first, tail]
theorem parseTail_lawTokensTail : (rest : PredList) → (n : Nat) → fuelTail rest ≤ n →
    (r : List Tok) → parseTail (n + 1) (lawTokensTail rest ++ .listClose :: r) =
      some (rest, .listClose :: r)
  | .nil, n, _, r => by simp [lawTokensTail, parseTail]
  | .cons q rest, n, h, r => by
      simp only [fuelTail] at h
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have tail := parseTail_lawTokensTail rest m (by omega) r
      have first := parseClause_lawTokens q (m + 1) (by omega)
        (lawTokensTail rest ++ .listClose :: r)
        (by cases rest <;> simp [lawTokensTail, follows])
      simp only [lawTokensTail, List.cons_append, List.append_assoc]
      simp [parseTail, first, tail]
end

/-- The parse of a whole printed law: enough fuel, and nothing left over. -/
def parseLaw (tokens : List Tok) : Option Pred :=
  match parseClause (tokens.length + 1) tokens with
  | some (p, []) => some p
  | _ => none

mutual
theorem fuel_lt_length : (p : Pred) → fuel p < (lawTokens p).length + 1
  | .eq _ _ | .le _ _ | .memberOf _ _ | .writeOnce _ | .monotone _ | .witnessed _
  | .eqSlots _ _ | .leSlots _ _ | .leSlotsOff _ _ _ | .sumEq _ _ | .hashEq _ _ _ | .ran _
  | .allL .nil | .anyL .nil => by
      simp [fuel, lawTokens]
  | .not q => by
      have := fuel_lt_length q
      simp [fuel, lawTokens]; omega
  | .allL (.cons q rest) => by
      have := fuel_lt_length q
      have := fuelTail_le_length rest
      simp [fuel, lawTokens]; omega
  | .anyL (.cons q rest) => by
      have := fuel_lt_length q
      have := fuelTail_le_length rest
      simp [fuel, lawTokens]; omega
theorem fuelTail_le_length : (rest : PredList) → fuelTail rest ≤ (lawTokensTail rest).length
  | .nil => by simp [fuelTail, lawTokensTail]
  | .cons q rest => by
      have := fuel_lt_length q
      have := fuelTail_le_length rest
      simp [fuelTail, lawTokensTail]; omega
end

/-- **`law_print_parse`**: every compiled law is recovered from the token
sequence it prints as; the printed text is that sequence's concatenation
(`textOf_lawTokens`). The string-to-token step (lexing) is the shell's
`law.rs` parser, which the journey checks against the committed law. -/
theorem law_print_parse (p : Pred) : parseLaw (lawTokens p) = some p := by
  have := parseClause_lawTokens p ((lawTokens p).length + 1) (fuel_lt_length p) [] rfl
  simp only [List.append_nil] at this
  simp [parseLaw, this]

/-- Two compiled laws that print the same token sequence are the same law. -/
theorem lawTokens_injective : Function.Injective lawTokens := by
  intro a b same
  have ha := law_print_parse a
  rw [same, law_print_parse b] at ha
  exact (Option.some.inj ha).symm

/-- The clauses of an installed law, each with its index: a top-level
conjunction of two or more is printed as `;`-separated clauses (the grammar's
`a; b` is `all [ a, b ]`); any other law is one clause. -/
def lawClauses : Pred → List Pred
  | .allL (.cons q (.cons r rest)) => q :: r :: (PredList.toList rest)
  | p => [p]

mutual
/-- The slots a clause reads. -/
def slotsOf : Pred → List Slot
  | .eq s _ | .le s _ | .memberOf s _ | .writeOnce s | .monotone s => [s]
  | .eqSlots a b | .leSlots a b | .leSlotsOff a b _ => [a, b]
  | .sumEq l r => l ++ r
  | .witnessed _ => []
  | .hashEq vs b c => vs ++ [b, c]
  | .ran program => [ranSlot program]
  | .not q => slotsOf q
  | .allL ps | .anyL ps => slotsOfList ps
def slotsOfList : PredList → List Slot
  | .nil => []
  | .cons q rest => slotsOf q ++ slotsOfList rest
end

/-! ## §3. `why`: the smallest change to the request that passes the failing clause -/

/-- The value a request writes under this slot: a field's `after` view, or the cost. -/
def requestSlot (s : Slot) : Bool :=
  match s.splitOn "/" with
  | ["resource", "field", _, "after"] => true
  | ["request", "cost"] => true
  | _ => false

/-- The state with `slot` overwritten (a read finds the first binding). -/
def setSlot (state : State) (slot : Slot) (value : Int) : State :=
  ⟨(slot, value) :: state.slots⟩

@[simp] theorem get_setSlot (state : State) (slot : Slot) (value : Int) :
    (setSlot state slot value).get slot = some value := by
  simp [setSlot, State.get, List.find?]

/-- The member of `xs` closest to `target` (the first such). -/
def nearest (target : Int) : List Int → Option Int
  | [] => none
  | x :: xs => match nearest target xs with
    | none => some x
    | some y => if (x - target).natAbs ≤ (y - target).natAbs then some x else some y

theorem nearest_mem (target : Int) : (xs : List Int) → (v : Int) → nearest target xs = some v → v ∈ xs
  | [], _, h => by simp [nearest] at h
  | x :: xs, v, h => by
      unfold nearest at h
      cases hn : nearest target xs with
      | none => simp [hn] at h; simp [h]
      | some y =>
        simp only [hn] at h
        split at h
        · simp at h; simp [h]
        · simp at h; subst h; exact List.mem_cons_of_mem _ (nearest_mem target xs y hn)

/-- The value nearest `target` outside `xs`: `target ± k` for the least such `k`. -/
def avoid (target : Int) (xs : List Int) : Int :=
  ((List.range (xs.length + 1)).flatMap
      (fun (k : Nat) => [target + ((k : Int) + 1), target - ((k : Int) + 1)])).find?
    (fun v => !xs.contains v) |>.getD (target + xs.length + 1)

theorem avoid_not_mem (target : Int) (xs : List Int) : avoid target xs ∉ xs := by
  unfold avoid
  cases h : ((List.range (xs.length + 1)).flatMap
      (fun (k : Nat) => [target + ((k : Int) + 1), target - ((k : Int) + 1)])).find?
      (fun v => !xs.contains v) with
  | some v =>
      have := List.find?_some h
      simpa using this
  | none =>
      exfalso
      have none := List.find?_eq_none.mp h
      -- the `xs.length + 1` values `target + 1, …, target + xs.length + 1` are distinct,
      -- so one of them is outside `xs`
      have all : ∀ k : Nat, k < xs.length + 1 → target + ((k : Int) + 1) ∈ xs := by
        intro k hk
        have := none (target + ((k : Int) + 1)) (by
          rw [List.mem_flatMap]
          exact ⟨k, List.mem_range.mpr hk, by simp⟩)
        simpa using this
      have sub : ((List.range (xs.length + 1)).map (fun k : Nat => target + ((k : Int) + 1))).toFinset ⊆
          xs.toFinset := by
        intro v hv
        simp only [List.mem_toFinset, List.mem_map, List.mem_range] at hv
        obtain ⟨k, hk, rfl⟩ := hv
        simpa using all k hk
      have card := Finset.card_le_card sub
      rw [List.toFinset_card_of_nodup] at card
      · simp at card
        have := List.toFinset_card_le xs
        omega
      · apply List.Nodup.map
        · intro a b same; simp at same; exact_mod_cast same
        · exact List.nodup_range

/-- For a failing clause, the slot to change and a value that satisfies it.
`before` is the value the slot had in the old view (the refusal's `before`),
`after` the value the request asked. Only request slots are suggested; a
clause over who you are, or over two slots, has no single-value repair. -/
def suggest (clause : Pred) (before after : Option Int) : Option (Slot × Int) :=
  match clause with
  | .eq s v => if requestSlot s then some (s, v) else none
  | .le s v => if requestSlot s then some (s, v) else none
  | .memberOf s xs => match nearest (after.getD 0) xs with
    | some v => if requestSlot s then some (s, v) else none
    | none => none
  | .monotone s => match before with
    | some b => if requestSlot s then some (s, b) else none
    | none => none
  | .writeOnce s => match before with
    | some b => if requestSlot s then some (s, b) else none
    | none => none
  | .not (.eq s v) => if requestSlot s then some (s, v + 1) else none
  | .not (.le s v) => if requestSlot s then some (s, v + 1) else none
  | .not (.memberOf s xs) => if requestSlot s then some (s, avoid (after.getD 0) xs) else none
  | _ => none

/-- **`suggest_passes`**: the suggested value satisfies the failing clause. Writing
`value` under `slot` (all else as requested) makes the clause true, given that
`before` is the slot's value in the old view (as the refusal's `LawLeaf` carries). -/
theorem suggest_passes (clause : Pred) (old new : State) (before after : Option Int)
    (slot : Slot) (value : Int) (hbefore : before = old.get slot)
    (suggested : suggest clause before after = some (slot, value)) :
    Minidregg.Pred.eval clause old (setSlot new slot value) = true := by
  cases clause with
  | eq s v => simp_all [suggest, Minidregg.Pred.eval, evalWith]
  | le s v => simp_all [suggest, Minidregg.Pred.eval, evalWith]
  | memberOf s xs =>
      cases hn : nearest (after.getD 0) xs with
      | none => simp_all [suggest]
      | some v =>
        have := nearest_mem _ _ _ hn
        simp_all [suggest, Minidregg.Pred.eval, evalWith]
  | monotone s =>
      subst hbefore
      cases hb : old.get slot with
      | none => simp [suggest, hb] at suggested
      | some b =>
        simp only [suggest, hb] at suggested
        split at suggested <;> simp at suggested
        obtain ⟨rfl, rfl⟩ := suggested
        simp [Minidregg.Pred.eval, evalWith, hb]
  | writeOnce s =>
      subst hbefore
      cases hb : old.get slot with
      | none => simp [suggest, hb] at suggested
      | some b =>
        simp only [suggest, hb] at suggested
        split at suggested <;> simp at suggested
        obtain ⟨rfl, rfl⟩ := suggested
        simp [Minidregg.Pred.eval, evalWith, hb]
  | not q =>
      cases q with
      | eq s v =>
          simp [suggest] at suggested
          obtain ⟨_, rfl, rfl⟩ := suggested
          simp [Minidregg.Pred.eval, evalWith]
      | le s v =>
          simp [suggest] at suggested
          obtain ⟨_, rfl, rfl⟩ := suggested
          simp [Minidregg.Pred.eval, evalWith]
      | memberOf s xs =>
          have := avoid_not_mem (after.getD 0) xs
          simp_all [suggest, Minidregg.Pred.eval, evalWith]
      | _ => simp [suggest] at suggested
  | _ => simp [suggest] at suggested

/-! ## §4. `turn` / `receipt`: a signing plan's legs -/

abbrev AuthAddress := Minidregg.Theory.Store.Address CredentialAuthorityState.layout

/-- One signing slot, decoded: its header and the reads its footprint names. -/
structure SlotLegs where
  header : CredentialSignedEnvelopeController.SignedHeader
  reads : Minidregg.Theory.PlanBinding.Footprint CredentialAuthorityState.layout

/-- Decode a slot's signed header and its footprint; refuse unless both
re-encode to exactly the signed bytes. -/
def decodeSlot (slot : NativeHostCodec.SigningSlot) : Option SlotLegs := do
  let header ← CredentialSignedEnvelopeController.headerCodec.decode slot.header
  let reads ← PlanFootprintCodec.decode CredentialAuthorityCell.wire header.footprint
  if CredentialSignedEnvelopeController.headerCodec.encode header = slot.header ∧
      PlanFootprintCodec.encode CredentialAuthorityCell.wire reads = header.footprint then
    some ⟨header, reads⟩
  else none

/-- The turn view's slots: every slot of the plan, in order, with its decoding. -/
def turnSlots (plan : NativeHostCodec.SigningPlan) :
    List (NativeHostCodec.SigningSlot × Option SlotLegs) :=
  plan.slots.map fun slot => (slot, decodeSlot slot)

/-- **`turn_view_matches_footprint`**: the view lists every slot of the signed
plan, in order, and the reads it lists for a slot re-encode to exactly the
footprint bytes that slot's signed header carries (and that header to the
exact signed header bytes): nothing is dropped, added or paraphrased. -/
theorem turn_view_matches_footprint (plan : NativeHostCodec.SigningPlan) :
    (turnSlots plan).map Prod.fst = plan.slots ∧
    ∀ entry ∈ turnSlots plan, ∀ legs, entry.2 = some legs →
      CredentialSignedEnvelopeController.headerCodec.encode legs.header = entry.1.header ∧
      PlanFootprintCodec.encode CredentialAuthorityCell.wire legs.reads = legs.header.footprint := by
  refine ⟨by simp [turnSlots, Function.comp_def], ?_⟩
  intro entry member legs decoded
  simp only [turnSlots, List.mem_map] at member
  obtain ⟨slot, _, rfl⟩ := member
  simp only [decodeSlot] at decoded
  cases hh : CredentialSignedEnvelopeController.headerCodec.decode slot.header with
  | none => simp [hh] at decoded
  | some header =>
    cases hr : PlanFootprintCodec.decode CredentialAuthorityCell.wire header.footprint with
    | none => simp [hh, hr] at decoded
    | some reads =>
      simp only [hh, hr, Option.bind_eq_bind, Option.bind_some] at decoded
      split at decoded
      · rename_i exact
        simp only [Option.some.injEq] at decoded
        subst decoded
        exact exact
      · simp at decoded

#assert_axioms capTree_edges_narrow
#assert_axioms capTree_complete_over_input
#assert_axioms capTree_links_accounted
#assert_axioms textOf_lawTokens
#assert_axioms law_print_parse
#assert_axioms lawTokens_injective
#assert_axioms suggest_passes
#assert_axioms turn_view_matches_footprint

end Minidregg.Host.InspectViews
