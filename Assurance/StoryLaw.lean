/-
# Assurance.StoryLaw — a sealed story's table is the law on every player's cell

A story (PLACE §2.8, item 8) is a transition table a friend writes and then seals. After
`story seal`, the client (`native/resource-client/src/story.rs`, `table_law`) installs one law
on every player's cell, generated from the table:

* the cell's fields are `scene` (field 0), `turn` (field 1) and `carries/ITEM` (field `2 + i` for
  the table's `i`-th item, in the table's order);
* clause 0 (`management`) admits only reads and writes, so nobody, the author included, can
  install another law, delegate or revoke on the cell;
* every other clause is guarded by `not (verb == write)` and judges a write: `mover` (only the
  player), `turn` (`turn` goes up by exactly one), `exits` (the scene stays, or moves along one
  of the table's edges), one `needs` clause per conditional edge (its item is already held),
  and per item `here` (taken only standing in its scene), `once` (it goes from 0 to 1 and never
  back), and finally `progress` (every turn moves or takes something).

§2 defines that law for every table (`law`); §3–§5 prove what it admits; §6 proves that no
policy installation can ever replace it; §7 is the table document's own sealed law; §8 is the
example story (`deploy/shell/templates/story/tale/table`) with its law as the client generated
it, embedded by `scripts/gen-storylaw.py` (`--check` proves the embed is the client's output),
and proved equal to `law taleTable` by `rfl`; §8 also has both poles by `decide`.

**Why this file is in `Assurance/`, not `Theory/`.** It imports `Pred` and `Kernel` (it reuses
`Kernel.LawView`'s view of the declared field store and its `CheckedLeg` bridge, and reads
`Kernel.PolicyInstallController`). `scripts/check-import-boundary.sh` admits only Mathlib and
`Theory` imports under `Theory/`, so the file lives where cross-layer theorems may.
-/
import Kernel.LawHistory
import Kernel.PolicyInstallController
import Compiler.RefusalReason

namespace Minidregg.Assurance.StoryLaw

open Minidregg.Pred (Pred State eval)
open Minidregg.Kernel.DeclaredResourceProjection (Values fieldName get)
open Minidregg.Kernel.LawView (ev_eq ev_not ev_all ev_any view admits Turn get_after get_before
  get_delta get_verb get_subject)
open Minidregg.Kernel.LawHistory (stepsOf final Accepted)
set_option autoImplicit false

/-! ## §1. A table, as the law reads it -/

/-- An edge of the table: an exit or an act from scene `src` to scene `dst`; `needs` is the index
of the item that must already be held. The word a player types (`go north`, `act open`) is the
client's: the law sees only the two scenes. -/
structure Edge where
  src : Int
  dst : Int
  needs : Option Nat
deriving DecidableEq, Repr

/-- The part of a table the law depends on: its edges, and for each item (in the table's
order) the scene it lies in. Scene texts, the start and the end scenes are the client's. -/
structure Table where
  edges : List Edge
  items : List Int
deriving DecidableEq, Repr

/-- `carries/ITEM` of the table's `i`-th item. -/
def carry (i : Nat) : Nat := 2 + i

/-- The items, numbered from `k`. -/
def numbered : Nat → List Int → List (Nat × Int)
  | _, [] => []
  | k, s :: rest => (k, s) :: numbered (k + 1) rest

/-! ## §2. The law -/

/-- `not (verb == write)`: the guard every game clause carries (`LawLeaf.writeGuard`). -/
def writeGuard : Pred := .not (.eq "request/verb" 2)

/-- A game clause: one of `xs`, or the request is not a write. -/
def guard (xs : List Pred) : Pred := Pred.any (xs ++ [writeGuard])

def management : Pred := Pred.any [.eq "request/verb" 1, .eq "request/verb" 2]

def mover (S : Int) : Pred := guard [.eq "request/subject" S]

def turn : Pred := guard [.eq (fieldName 1 "delta") 1]

def edgeStep (e : Edge) : Pred :=
  Pred.all [.eq (fieldName 0 "before") e.src, .eq (fieldName 0 "after") e.dst]

def exits (t : Table) : Pred := guard ([.eq (fieldName 0 "delta") 0] ++ t.edges.map edgeStep)

def needsClause (e : Edge) (i : Nat) : Pred :=
  guard [.not (edgeStep e), .eq (fieldName (carry i) "before") 1]

def needsClauses (t : Table) : List Pred := t.edges.filterMap fun e => e.needs.map (needsClause e)

def here (i : Nat) (s : Int) : Pred :=
  guard [.eq (fieldName (carry i) "delta") 0,
    Pred.all [.eq (fieldName 0 "before") s, .eq (fieldName 0 "delta") 0]]

def once (i : Nat) : Pred :=
  guard [.eq (fieldName (carry i) "delta") 0,
    Pred.all [.eq (fieldName (carry i) "before") 0, .eq (fieldName (carry i) "after") 1]]

def progress (t : Table) : Pred :=
  guard ([.not (.eq (fieldName 0 "delta") 0)] ++
    (numbered 0 t.items).map fun p => .not (.eq (fieldName (carry p.1) "delta") 0))

/-- The clauses in the installed order (the order a refusal names the first failing one in). -/
def clauses (t : Table) (S : Int) : List Pred :=
  [management, mover S, turn, exits t] ++ needsClauses t ++
    (numbered 0 t.items).map (fun p => here p.1 p.2) ++
    (numbered 0 t.items).map (fun p => once p.1) ++ [progress t]

/-- **The sealed law of player `S`'s cell in a story with table `t`.** -/
def law (t : Table) (S : Int) : Pred := Pred.all (clauses t S)

/-! ## §3. What the law admits, one step at a time -/

section Law
variable {o n : State}

theorem guarded {xs : List Pred} (w : n.get "request/verb" = some 2)
    (h : eval (guard xs) o n = true) : ∃ q ∈ xs, eval q o n = true := by
  obtain ⟨q, hq, hv⟩ := ev_any.mp h
  rcases List.mem_append.mp hq with hq | hq
  · exact ⟨q, hq, hv⟩
  · simp only [List.mem_singleton] at hq
    subst hq
    rw [writeGuard, ev_not, ev_eq] at hv
    exact absurd w hv

theorem clause_of {t : Table} {S : Int} (h : eval (law t S) o n = true) {q : Pred}
    (hq : q ∈ clauses t S) : eval q o n = true :=
  ev_all.mp h q hq

/-- What one admitted write is: by the player, one turn on, and a stay or a table edge. -/
structure Step (t : Table) (S : Int) (n : State) : Prop where
  subject : n.get "request/subject" = some S
  turn : n.get (fieldName 1 "delta") = some 1
  scene : n.get (fieldName 0 "delta") = some 0 ∨
    ∃ e ∈ t.edges, n.get (fieldName 0 "before") = some e.src ∧ n.get (fieldName 0 "after") = some e.dst

theorem law_step (t : Table) (S : Int) (h : eval (law t S) o n = true)
    (w : n.get "request/verb" = some 2) : Step t S n := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨q, hq, hv⟩ := guarded w (clause_of h (q := mover S) (by simp [clauses]))
    simp only [List.mem_singleton] at hq
    subst hq
    exact ev_eq.mp hv
  · obtain ⟨q, hq, hv⟩ := guarded w (clause_of h (q := turn) (by simp [clauses]))
    simp only [List.mem_singleton] at hq
    subst hq
    exact ev_eq.mp hv
  · obtain ⟨q, hq, hv⟩ := guarded w (clause_of h (q := exits t) (by simp [clauses]))
    rcases List.mem_append.mp hq with hq | hq
    · simp only [List.mem_singleton] at hq
      subst hq
      exact .inl (ev_eq.mp hv)
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
      have hs := ev_all.mp hv
      exact .inr ⟨e, he, ev_eq.mp (hs _ (by simp)), ev_eq.mp (hs _ (by simp))⟩

/-- A conditional edge is taken only by a player already holding its item. -/
theorem law_needs (t : Table) (S : Int) (h : eval (law t S) o n = true)
    (w : n.get "request/verb" = some 2) {e : Edge} (he : e ∈ t.edges) {i : Nat}
    (hi : e.needs = some i) (from_ : n.get (fieldName 0 "before") = some e.src)
    (to_ : n.get (fieldName 0 "after") = some e.dst) :
    n.get (fieldName (carry i) "before") = some 1 := by
  have mem : needsClause e i ∈ clauses t S := by
    simp only [clauses, List.mem_append]
    exact .inl (.inl (.inl (.inr (List.mem_filterMap.mpr ⟨e, he, by simp [hi]⟩))))
  obtain ⟨q, hq, hv⟩ := guarded w (clause_of h mem)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · rw [ev_not] at hv
    exact absurd (ev_all.mpr (by simp [ev_eq, from_, to_])) hv
  · exact ev_eq.mp hv

/-- **Sealed, law form.** The law admits only reads and writes: no installation (4), no
delegation (3), no revocation (5), for any subject. -/
theorem law_read_or_write (t : Table) (S : Int) (h : eval (law t S) o n = true) :
    n.get "request/verb" = some 1 ∨ n.get "request/verb" = some 2 := by
  obtain ⟨q, hq, hv⟩ := ev_any.mp (clause_of h (q := management) (by simp [clauses]))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact .inl (ev_eq.mp hv)
  · exact .inr (ev_eq.mp hv)

theorem law_no_install (t : Table) (S : Int) (h : eval (law t S) o n = true) :
    n.get "request/verb" ≠ some 4 := by
  rcases law_read_or_write t S h with v | v <;> rw [v] <;> decide

end Law

/-! ## §4. The step over the declared field store

`view tt pre post` is the slot list the controller hands the law (`Kernel.LawView` §6): the
law's old state is `view tt pre pre`, its new state `view tt pre tt.post`. -/

section Store

/-- **One admitted write on a player's cell**: it is the player's, the turn goes from `k` to
`k + 1`, and the scene stays or moves along a table edge. -/
theorem scene_step (t : Table) (S : Int) {pre : Values} {tt : Turn}
    (h : admits (law t S) pre tt = true) (w : tt.verb = 2) {a k : Int}
    (ha : get pre 0 = some a) (hk : get pre 1 = some k) :
    tt.subject = S ∧ get tt.post 1 = some (k + 1) ∧
      ∃ b, get tt.post 0 = some b ∧ (b = a ∨ ∃ e ∈ t.edges, e.src = a ∧ e.dst = b) := by
  have st := law_step t S h (by rw [get_verb, w])
  refine ⟨?_, ?_, ?_⟩
  · have := st.subject
    rw [get_subject] at this
    exact Option.some.inj this
  · have := st.turn
    rw [get_delta tt pre tt.post 1 k hk] at this
    cases hp : get tt.post 1 with
    | none => rw [hp] at this; cases this
    | some x =>
        rw [hp] at this
        simp only [Option.map_some, Option.some.injEq] at this
        rw [show x = k + 1 by omega]
  · rcases st.scene with d | ⟨e, he, hb, hd⟩
    · rw [get_delta tt pre tt.post 0 a ha] at d
      cases hp : get tt.post 0 with
      | none => rw [hp] at d; cases d
      | some x =>
          rw [hp] at d
          simp only [Option.map_some, Option.some.injEq] at d
          exact ⟨x, rfl, .inl (by omega)⟩
    · rw [get_before, ha] at hb
      rw [get_after] at hd
      exact ⟨e.dst, hd, .inr ⟨e, he, (Option.some.inj hb).symm, rfl⟩⟩

/-- A move along a conditional edge needs its item already held (in the pre-state). -/
theorem needs_step (t : Table) (S : Int) {pre : Values} {tt : Turn}
    (h : admits (law t S) pre tt = true) (w : tt.verb = 2) {e : Edge} (he : e ∈ t.edges)
    {i : Nat} (hi : e.needs = some i) (from_ : get pre 0 = some e.src)
    (to_ : get tt.post 0 = some e.dst) : get pre (carry i) = some 1 := by
  have := law_needs t S h (by rw [get_verb, w]) he hi (by rw [get_before, from_])
    (by rw [get_after, to_])
  rwa [get_before] at this

end Store

/-! ## §5. Histories: no skip, no rewind -/

section History

theorem stepsOf_append (v : Values) (xs ys : List Turn) :
    stepsOf v (xs ++ ys) = stepsOf v xs ++ stepsOf (final v xs) ys := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih => simp [stepsOf, final, ih]

theorem final_append (v : Values) (xs ys : List Turn) :
    final v (xs ++ ys) = final (final v xs) ys := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih => simp [final, ih]

theorem accepted_prefix {L : Pred} {v : Values} {xs ys : List Turn}
    (h : Accepted L v (xs ++ ys)) : Accepted L v xs :=
  fun s hs => h s (by rw [stepsOf_append]; exact List.mem_append_left _ hs)

/-- **`sealed_story_scene_monotone`.** Along any accepted history of writes on a player's cell
under the sealed law, starting from scene `a` at turn `k`: every write is the player's, every
write moves the scene only along a table edge (or not at all) — no skip — and raises the turn
by exactly one, so after `n` writes the turn is `k + n` — no rewind. -/
theorem sealed_story_scene_monotone (t : Table) (S : Int) :
    ∀ (v : Values) (ts : List Turn) (a k : Int), get v 0 = some a → get v 1 = some k →
      Accepted (law t S) v ts →
      (∀ s ∈ stepsOf v ts, s.2.subject = S ∧ ∃ x y m, get s.1 0 = some x ∧
          get s.2.post 0 = some y ∧ get s.1 1 = some m ∧ get s.2.post 1 = some (m + 1) ∧
          (y = x ∨ ∃ e ∈ t.edges, e.src = x ∧ e.dst = y)) ∧
        get (final v ts) 1 = some (k + ts.length) := by
  intro v ts
  induction ts generalizing v with
  | nil => intro a k _ hk _; exact ⟨fun s hs => by simp [stepsOf] at hs, by simpa [final] using hk⟩
  | cons tt ts ih =>
      intro a k ha hk acc
      obtain ⟨w, adm⟩ := acc.head
      obtain ⟨subj, hk', b, hb, edge⟩ := scene_step t S adm w ha hk
      obtain ⟨rest, fin⟩ := ih tt.post b (k + 1) hb hk' acc.tail
      refine ⟨?_, ?_⟩
      · intro s hs
        simp only [stepsOf, List.mem_cons] at hs
        rcases hs with rfl | hs
        · exact ⟨subj, a, b, k, ha, hb, hk, hk', edge⟩
        · exact rest s hs
      · simp only [final, List.length_cons]
        rw [fin]
        congr 1
        push_cast
        ring

/-- **No rewind.** An accepted continuation never brings a player's cell back to a state it
held: the turn of the later state is strictly greater. -/
theorem no_rewind (t : Table) (S : Int) (v : Values) (xs ys : List Turn) {a k : Int}
    (ha : get v 0 = some a) (hk : get v 1 = some k) (acc : Accepted (law t S) v (xs ++ ys))
    (more : ys ≠ []) : final v (xs ++ ys) ≠ final v xs := by
  intro same
  have whole := (sealed_story_scene_monotone t S v (xs ++ ys) a k ha hk acc).2
  have part := (sealed_story_scene_monotone t S v xs a k ha hk (accepted_prefix acc)).2
  rw [same, part, List.length_append] at whole
  have : (ys.length : Int) = 0 := by
    have := Option.some.inj whole
    push_cast at this
    omega
  exact more (List.length_eq_zero_iff.mp (by exact_mod_cast this))

end History

/-! ## §6. Sealed: no installation can replace the law

`PolicyInstallController.Installed` is every accepted policy installation. Its
`old_policy_evaluated` says the cell's current law admitted the install request, projected with
`request/verb` = installPolicy (tag 4). A law that admits no verb-4 step therefore has no
accepted installation at all: once a cell carries it, nobody — owner, author, room founder —
replaces it. -/

section Sealed
open Minidregg.Compiler Minidregg.Compiler.CanonicalPolicyAdmission
  Minidregg.Compiler.CredentialAuthorityPolicyRegistry Minidregg.Kernel.CanonicalPolicyRegistry
  Minidregg.Theory.Store Minidregg.Kernel.PolicyInstallController
open Minidregg.Theory.CredentialAuthorityState (layout)

variable {F : Type} [Field F]

theorem install_view_verb (profile : RuntimeProfile F) (snapshot : Snapshot)
    (context : RequestContext) (declaration : Declaration) (logical : Store layout)
    (storageKind : Nat := 0) :
    (project (request profile snapshot context declaration) declaration logical storageKind).get "request/verb" =
      some 4 := by
  simp [project, State.get, CanonicalRuntimeProfile.requestSlots, request,
    CredentialAuthorityEntryCodec.verbTag]

/-- **A law that admits no installation is never replaced.** -/
theorem never_relawed [DecidableEq F] (L : Pred)
    (refuses : ∀ o n : State, eval L o n = true → n.get "request/verb" ≠ some 4)
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext}
    {store : PayloadStore} (installed : Installed profile snapshot context store)
    (current : Minidregg.Kernel.LawHistory.ActiveComponent
      (installed.prepared.policyConfig store) (L)) : False := by
  have holds := Minidregg.Kernel.LawHistory.authorized_component_eval
    (installed.prepared.policyConfig store)
    (request profile snapshot context installed.prepared.declaration)
    installed.accepted.authorization L current
  exact refuses _ _ holds (install_view_verb profile snapshot context
    installed.prepared.declaration installed.post.logical installed.prepared.storageKind)

/-- **The author cannot change a sealed story under a player**: no accepted installation exists
on a player's cell whose current law is the sealed story law. -/
theorem sealed_story_never_relawed [DecidableEq F] (t : Table) (S : Int)
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext}
    {store : PayloadStore} (installed : Installed profile snapshot context store)
    (current : Minidregg.Kernel.LawHistory.ActiveComponent
      (installed.prepared.policyConfig store) (law t S)) : False :=
  never_relawed (law t S) (fun _ _ h => law_no_install t S h) installed current

/-! ## §7. The table document's sealed law

`story seal` installs this on the story's `table` document: clause 0 refuses every write and the
Host names it `sealed` (`LawLeaf.explained` drops the write guard and `renderClause (any [])` is
`sealed`); clause 1 admits only reads and writes, so no installation replaces it (§6). -/

def tableSealed : Pred := Pred.all [guard [Pred.any []], .memberOf "request/verb" [1, 2]]

theorem table_refuses_write {o n : State} (h : eval tableSealed o n = true) :
    n.get "request/verb" ≠ some 2 := by
  intro w
  have h0 := ev_all.mp h (guard [Pred.any []]) (by simp)
  obtain ⟨q, hq, hv⟩ := guarded w h0
  simp only [List.mem_singleton] at hq
  subst hq
  obtain ⟨r, hr, -⟩ := ev_any.mp hv
  simp at hr

theorem table_no_install {o n : State} (h : eval tableSealed o n = true) :
    n.get "request/verb" ≠ some 4 := by
  have h1 := ev_all.mp h (.memberOf "request/verb" [1, 2]) (by simp)
  intro w
  obtain ⟨x, hx, mem⟩ := Minidregg.Kernel.LawView.ev_memberOf.mp h1
  rw [w] at hx
  cases hx
  simp at mem

theorem sealed_table_never_relawed [DecidableEq F]
    {profile : RuntimeProfile F} {snapshot : Snapshot} {context : RequestContext}
    {store : PayloadStore} (installed : Installed profile snapshot context store)
    (current : Minidregg.Kernel.LawHistory.ActiveComponent
      (installed.prepared.policyConfig store) (tableSealed)) : False :=
  never_relawed tableSealed (fun _ _ h => table_no_install h) installed current

/-- The Host's explanation of a refused table edit is `any []`, which renders `sealed`. -/
theorem table_refusal_explained : LawLeaf.explained (guard [Pred.any []]) = Pred.any [] := by
  decide

theorem table_refusal_rendered : LawLeaf.renderClause (Pred.any []) = "sealed" := rfl

end Sealed

/-! ## §8. The tale: the example story, its generated law, and both poles

`taleTable` and `taleEmbedded` (between the markers) are written by `scripts/gen-storylaw.py`
from `mini story-law --table deploy/shell/templates/story/tale/table`: the client's own table
parser and law generator, the code `story seal` runs. `--check` fails if either differs from
what the client generates now. -/

-- BEGIN GENERATED (scripts/gen-storylaw.py)
/-- The tale's table, as the client parsed it: edges in (from, to) order, item scenes in item-name order. -/
def taleTable : Table := ⟨[⟨0, 1, none⟩, ⟨1, 2, none⟩, ⟨1, 3, some 0⟩, ⟨3, 4, none⟩], [1]⟩

/-- The client's law for player `S` of the tale, as `story seal` generates it. -/
def taleEmbedded (S : Int) : Pred :=
  Pred.all [
    Pred.any [
      .eq "request/verb" 1,
      .eq "request/verb" 2],
    Pred.any [
      .eq "request/subject" S,
      .not (.eq "request/verb" 2)],
    Pred.any [
      .eq "resource/field/1/delta" 1,
      .not (.eq "request/verb" 2)],
    Pred.any [
      .eq "resource/field/0/delta" 0,
      Pred.all [
        .eq "resource/field/0/before" 0,
        .eq "resource/field/0/after" 1],
      Pred.all [
        .eq "resource/field/0/before" 1,
        .eq "resource/field/0/after" 2],
      Pred.all [
        .eq "resource/field/0/before" 1,
        .eq "resource/field/0/after" 3],
      Pred.all [
        .eq "resource/field/0/before" 3,
        .eq "resource/field/0/after" 4],
      .not (.eq "request/verb" 2)],
    Pred.any [
      .not (Pred.all [
          .eq "resource/field/0/before" 1,
          .eq "resource/field/0/after" 3]),
      .eq "resource/field/2/before" 1,
      .not (.eq "request/verb" 2)],
    Pred.any [
      .eq "resource/field/2/delta" 0,
      Pred.all [
        .eq "resource/field/0/before" 1,
        .eq "resource/field/0/delta" 0],
      .not (.eq "request/verb" 2)],
    Pred.any [
      .eq "resource/field/2/delta" 0,
      Pred.all [
        .eq "resource/field/2/before" 0,
        .eq "resource/field/2/after" 1],
      .not (.eq "request/verb" 2)],
    Pred.any [
      .not (.eq "resource/field/0/delta" 0),
      .not (.eq "resource/field/2/delta" 0),
      .not (.eq "request/verb" 2)]]
-- END GENERATED

/-- **The client's generated law is this file's `law`** of the generated table. -/
theorem tale_embedded_is_law (S : Int) : taleEmbedded S = law taleTable S := rfl

section Poles

/-- Player `S` = 7; a write of the player's own cell. -/
def mv (post : Values) : Turn := ⟨2, 7, none, [], post⟩

/-- `(scene, turn, carries/key)`. -/
def cell (scene turn key : Int) : Values := [(0, scene), (1, turn), (2, key)]

def L : Pred := law taleTable 7

/-- Admitted: hallway → anteroom (`go north`), turn 0 → 1. -/
theorem legal_step_admitted : admits L (cell 0 0 0) (mv (cell 1 1 0)) = true := by decide

/-- Admitted: taking the key in the anteroom. -/
theorem take_key_admitted : admits L (cell 1 1 0) (mv (cell 1 2 1)) = true := by decide

/-- Admitted: anteroom → landing holding the key (the conditional edge). -/
theorem conditional_with_key_admitted : admits L (cell 1 2 1) (mv (cell 3 3 1)) = true := by
  decide

/-- Refused: a skip, hallway → landing. The first failing clause is `exits` (clause 3). -/
theorem skip_refused : admits L (cell 0 0 0) (mv (cell 3 1 0)) = false := by decide

theorem skip_names_exits :
    (Minidregg.Compiler.LawLeaf.of L (view (mv (cell 3 1 0)) (cell 0 0 0) (cell 0 0 0))
      (view (mv (cell 3 1 0)) (cell 0 0 0) (cell 3 1 0))).map (·.path) = some [3] := by decide

/-- Refused: a rewind, anteroom → hallway (not an edge), turn going on. -/
theorem rewind_refused : admits L (cell 1 1 0) (mv (cell 0 2 0)) = false := by decide

/-- Refused: a rewind of the whole state, turn 1 → 0 (clause 2, `turn`). -/
theorem rewind_turn_refused : admits L (cell 1 1 0) (mv (cell 0 0 0)) = false := by decide

theorem rewind_turn_names_turn :
    (Minidregg.Compiler.LawLeaf.of L (view (mv (cell 0 0 0)) (cell 1 1 0) (cell 1 1 0))
      (view (mv (cell 0 0 0)) (cell 1 1 0) (cell 0 0 0))).map (·.path) = some [2] := by decide

/-- Refused: the conditional edge without the key (clause 4, `needs`). -/
theorem conditional_without_key_refused :
    admits L (cell 1 1 0) (mv (cell 3 2 0)) = false := by decide

theorem conditional_names_needs :
    (Minidregg.Compiler.LawLeaf.of L (view (mv (cell 3 2 0)) (cell 1 1 0) (cell 1 1 0))
      (view (mv (cell 3 2 0)) (cell 1 1 0) (cell 3 2 0))).map (·.path) = some [4] := by decide

/-- Refused: taking the key where it does not lie (clause 5, `here`). -/
theorem take_absent_refused : admits L (cell 0 0 0) (mv (cell 0 1 1)) = false := by decide

/-- Refused: taking the key twice (clause 7, `progress`: the turn changed nothing). -/
theorem take_twice_refused : admits L (cell 1 2 1) (mv (cell 1 3 1)) = false := by decide

/-- Refused: dropping the key (clause 6, `once`). -/
theorem drop_refused : admits L (cell 1 2 1) (mv (cell 1 3 0)) = false := by decide

/-- Refused: another subject (9) moving player 7's cell (clause 1, `mover`). -/
theorem other_player_refused :
    admits L (cell 0 0 0) ⟨2, 9, none, [], cell 1 1 0⟩ = false := by decide

/-- Refused: an installation on the cell (clause 0, `management`), by anyone. -/
theorem install_refused :
    admits L (cell 0 0 0) ⟨4, 7, none, [], cell 0 0 0⟩ = false := by decide

/-- Admitted: a read. -/
theorem read_admitted : admits L (cell 1 1 0) ⟨1, 9, none, [], cell 1 1 0⟩ = true := by decide

/-- The sealed table: a read admitted, the author's edit and a re-law refused. -/
theorem table_read_admitted : eval tableSealed ⟨[("request/verb", 1)]⟩ ⟨[("request/verb", 1)]⟩ = true := by
  decide

theorem table_edit_refused : eval tableSealed ⟨[("request/verb", 2)]⟩ ⟨[("request/verb", 2)]⟩ = false := by
  decide

theorem table_relaw_refused : eval tableSealed ⟨[("request/verb", 4)]⟩ ⟨[("request/verb", 4)]⟩ = false := by
  decide

/-- A whole play-through of the tale is accepted: hallway, anteroom, the key, the landing, the
lamp room (`act open`). -/
theorem playthrough_accepted :
    Accepted L (cell 0 0 0)
      [mv (cell 1 1 0), mv (cell 1 2 1), mv (cell 3 3 1), mv (cell 4 4 1)] := by decide

end Poles

/-! ## §9. Kernel form: every admitted leg on a player's cell -/

section Kernel
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Compiler

variable {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient}
  {ground : Ground deployment} {command : Command}

/-- The authenticated effective closure includes the sealed story law of `t` for player `S` as an active component. -/
def StoryInstalled (t : Table) (S : Int)
    {prepared : PreparedInvocation deployment profile ambient ground command}
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) : Prop :=
  Minidregg.Kernel.LawHistory.ActiveComponent
    (policyConfig prepared tuple incidence) (law t S)

/-- Derive the installed-law assurance premise from the receiver's cached,
authenticated effective graph; no caller assertion or second resolver is used. -/
def checkInstalled (t : Table) (S : Int)
    {prepared : PreparedInvocation deployment profile ambient ground command}
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command)
    (resolved : Minidregg.Compiler.ComposedPolicyAdmission.PreparedLaw
      (policyConfig prepared tuple incidence)) :
    Option (PLift (StoryInstalled t S tuple incidence)) :=
  Minidregg.Kernel.LawHistory.checkActiveComponent resolved (law t S)

/-- **Kernel form.** Every write leg the controller admitted on a player's cell under the sealed
story law is the player's, one turn on, and a stay or a table edge. -/
theorem kernel_story_step (t : Table) (S : Int)
    {prepared : PreparedInvocation deployment profile ambient ground command}
    {tuple : PreparedTuple (plan prepared)} {incidence : Incidence command} {envelope : List UInt8}
    (leg : CheckedLeg prepared tuple incidence envelope) (installed : StoryInstalled t S tuple incidence)
    (w : (step prepared tuple incidence).newState.get "request/verb" = some 2) :
    Step t S (step prepared tuple incidence).newState := by
  have holds := Minidregg.Kernel.LawHistory.checked_leg_component_eval leg
    (law t S) installed
  exact law_step t S holds w

end Kernel

/-! ## Axiom pins: every theorem rests on the standard three or fewer. -/

/-- info: 'Minidregg.Assurance.StoryLaw.law_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms law_step
/-- info: 'Minidregg.Assurance.StoryLaw.law_needs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms law_needs
/-- info: 'Minidregg.Assurance.StoryLaw.law_read_or_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms law_read_or_write
/-- info: 'Minidregg.Assurance.StoryLaw.law_no_install' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms law_no_install
/-- info: 'Minidregg.Assurance.StoryLaw.scene_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scene_step
/-- info: 'Minidregg.Assurance.StoryLaw.needs_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms needs_step
/-- info: 'Minidregg.Assurance.StoryLaw.stepsOf_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms stepsOf_append
/-- info: 'Minidregg.Assurance.StoryLaw.final_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms final_append
/-- info: 'Minidregg.Assurance.StoryLaw.accepted_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_prefix
/-- info: 'Minidregg.Assurance.StoryLaw.sealed_story_scene_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sealed_story_scene_monotone
/-- info: 'Minidregg.Assurance.StoryLaw.no_rewind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_rewind
/-- info: 'Minidregg.Assurance.StoryLaw.install_view_verb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms install_view_verb
/-- info: 'Minidregg.Assurance.StoryLaw.never_relawed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms never_relawed
/-- info: 'Minidregg.Assurance.StoryLaw.sealed_story_never_relawed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sealed_story_never_relawed
/-- info: 'Minidregg.Assurance.StoryLaw.table_refuses_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms table_refuses_write
/-- info: 'Minidregg.Assurance.StoryLaw.table_no_install' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms table_no_install
/-- info: 'Minidregg.Assurance.StoryLaw.sealed_table_never_relawed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sealed_table_never_relawed
/-- info: 'Minidregg.Assurance.StoryLaw.table_refusal_explained' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms table_refusal_explained
/-- info: 'Minidregg.Assurance.StoryLaw.table_refusal_rendered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms table_refusal_rendered
/-- info: 'Minidregg.Assurance.StoryLaw.tale_embedded_is_law' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms tale_embedded_is_law
/-- info: 'Minidregg.Assurance.StoryLaw.legal_step_admitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms legal_step_admitted
/-- info: 'Minidregg.Assurance.StoryLaw.take_key_admitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms take_key_admitted
/-- info: 'Minidregg.Assurance.StoryLaw.conditional_with_key_admitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms conditional_with_key_admitted
/-- info: 'Minidregg.Assurance.StoryLaw.skip_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms skip_refused
/-- info: 'Minidregg.Assurance.StoryLaw.skip_names_exits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms skip_names_exits
/-- info: 'Minidregg.Assurance.StoryLaw.rewind_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rewind_refused
/-- info: 'Minidregg.Assurance.StoryLaw.rewind_turn_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rewind_turn_refused
/-- info: 'Minidregg.Assurance.StoryLaw.rewind_turn_names_turn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rewind_turn_names_turn
/-- info: 'Minidregg.Assurance.StoryLaw.conditional_without_key_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms conditional_without_key_refused
/-- info: 'Minidregg.Assurance.StoryLaw.conditional_names_needs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms conditional_names_needs
/-- info: 'Minidregg.Assurance.StoryLaw.take_absent_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms take_absent_refused
/-- info: 'Minidregg.Assurance.StoryLaw.take_twice_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms take_twice_refused
/-- info: 'Minidregg.Assurance.StoryLaw.drop_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms drop_refused
/-- info: 'Minidregg.Assurance.StoryLaw.other_player_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms other_player_refused
/-- info: 'Minidregg.Assurance.StoryLaw.install_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms install_refused
/-- info: 'Minidregg.Assurance.StoryLaw.read_admitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_admitted
/-- info: 'Minidregg.Assurance.StoryLaw.table_read_admitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms table_read_admitted
/-- info: 'Minidregg.Assurance.StoryLaw.table_edit_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms table_edit_refused
/-- info: 'Minidregg.Assurance.StoryLaw.table_relaw_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms table_relaw_refused
/-- info: 'Minidregg.Assurance.StoryLaw.playthrough_accepted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms playthrough_accepted
/-- info: 'Minidregg.Assurance.StoryLaw.kernel_story_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kernel_story_step

end Minidregg.Assurance.StoryLaw
