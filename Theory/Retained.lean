/-
# Theory.Retained -- maintained views answer as recomputation does (statement)

The retained-mode abstraction (`docs/RETAINED-MODE.md`). A system state advances by admitted
deltas; a *view* is a family of queries whose meaning is a function of the state (`spec`, the
recomputation, which never runs on a request path). A *maintained* implementation keeps a
representation beside the state, advances it by each delta, and answers every query as the
specification would at every reachable state. Stated once and proved once
(`Maintained.maintained_eq_recompute`, `Maintained.checkpoint_restore_from`); a concrete
derived structure owes only its local lemmas (`Node.fetch_sound`, `Node.update_holds`).

* `DeltaSystem`: states, deltas, a partial `step` (none = refused), a genesis.
* `View`: queries `Q`, dependent answers `A q`, `spec : State → (q : Q) → A q`.
* `Maintained D V` (closed): `Rep`, a representation relation `Holds` (a relation, so a kept
  trie need not be the bulk build's: ACL2's abstract stobjs, `Theory.CellStateAux`), `fetch`
  (answer and the representation to keep: a read may fill a memo), `advance`, `init`.
* `Node D In Out` (open over an input view): a read declares the input queries it needs given
  its representation (`readProbes`: none on a hit) and sees only their answers (`Reads`); an
  update declares probes from the delta alone (pre or post the delta) and sees only theirs.
  `ReadFootprintBounded`/`ProbeFootprintBounded` bound the declared input footprint
  (`c + k · size`), NOT cost: the representation and the delta are free, so a shadow-state node
  (`Rep := Store`, `update := Patch.run`, `fetch := spec`) meets a zero footprint while recomputing
  on every read. Cost is gated by the flatness bench (law 17); a cost statement over an
  instrumented interpreter (as `PrivateCellTrie.EraseCost` over `AuthTrie.Prog`) is owed per node.
* `Node.stack N M`: a node over a maintained input is maintained; the input's answers are
  fetched once, materialized, and its fills kept (the chain rule; nested `View.sum` layers give
  any finite DAG in topological order, `Node.weakenLeft` reads a wider input).
* `Persist`: a checkpoint codec under the trusted-storage model; `checkpoint_restore_from`:
  restore any held representation and advance over the suffix = recomputation at the head.
  Restart cost is the concrete codec's statement, not this one's.
* `RedGreen.node`: the generic memo node for any `Derivation` (a query computed from exactly
  its declared `deps`, and a delta's syntactic `touched` set with its frame law): a write
  stamps its touched inputs, a read on a green entry reads nothing, a miss reads its deps and
  remembers. Salsa's red-green without early cutoff; Adapton's demanded computation.

Deferred until an instance needs them (astra, round 1): typed output deltas per layer (the
DBSP chain rule / ILC derivative contract), early cutoff and durability.

Witnesses (ATLAS law 2), over `Theory.Store`'s example layout: a two-layer graph (a heap total
maintained from the guarded ops' own before/after values with no probes; a threshold flag
reading one post answer of the total) and a red-green memo of the same total. Satisfiable:
`Example.flag_reachable` (the flag rises and falls on a real admitted run),
`Example.memo_hit_reads_nothing` (a miss reads both dependencies, the remembered read reads
none, a write to a dependency turns it red). Teeth: `Maintained.stale_refuted`,
`Maintained.constant_refuted`, `Example.ignoring_update_refuted`, `Example.empty_deps_refuted`.
Premise inhabitation: `Example.holds_inhabited`.
-/
module

public import Theory.Store
import Theory.AssertAxioms

@[expose] public section

namespace Minidregg.Theory.Retained

set_option autoImplicit false

universe u v

/-! ## Delta systems and views -/

/-- States advanced by admitted deltas. `step δ s = none` is refusal. -/
structure DeltaSystem where
  State : Type u
  Delta : Type v
  step : Delta → State → Option State
  genesis : State

namespace DeltaSystem

variable (D : DeltaSystem.{u, v})

/-- An admitted run: every delta admitted at the state its prefix produced. -/
def run : D.State → List D.Delta → Option D.State
  | s, [] => some s
  | s, δ :: δs => match D.step δ s with
    | none => none
    | some s' => run s' δs

@[simp] theorem run_nil (s : D.State) : D.run s [] = some s := rfl

theorem run_cons (s : D.State) (δ : D.Delta) (δs : List D.Delta) :
    D.run s (δ :: δs) = (D.step δ s).bind (fun s' => D.run s' δs) := by
  simp only [run]; cases D.step δ s <;> rfl

theorem run_append (s : D.State) (left right : List D.Delta) :
    D.run s (left ++ right) = (D.run s left).bind (fun m => D.run m right) := by
  induction left generalizing s with
  | nil => rfl
  | cons δ rest ih =>
    simp only [List.cons_append, run]
    cases D.step δ s with
    | none => rfl
    | some s' => exact ih s'

/-- A state is reachable when some admitted run from genesis produces it. -/
def Reachable (s : D.State) : Prop := ∃ δs, D.run D.genesis δs = some s

end DeltaSystem

/-- Queries over a state, with their meaning: `spec` is the recomputation. -/
structure View (State : Type u) where
  Q : Type
  A : Q → Type
  spec : State → (q : Q) → A q

/-- Two views side by side: a layer exposes the layers below it. -/
abbrev View.sum {State : Type u} (In Out : View State) : View State where
  Q := In.Q ⊕ Out.Q
  A := fun q => match q with
    | .inl q => In.A q
    | .inr q => Out.A q
  spec := fun s q => match q with
    | .inl q => In.spec s q
    | .inr q => Out.spec s q

/-- Whether a probe reads the input before or after the delta. -/
inductive Phase
  | pre
  | post
  deriving DecidableEq, Repr

/-- The answers an update receives: exactly its declared probes, each at its phase. -/
abbrev Answers {State : Type u} (In : View State) (probes : List (Phase × In.Q)) : Type :=
  (p : Phase × In.Q) → p ∈ probes → In.A p.2

/-- The declared probes answered by two readers (before and after the delta). -/
def answersBy {State : Type u} {In : View State} (pre post : (q : In.Q) → In.A q)
    (probes : List (Phase × In.Q)) : Answers In probes :=
  fun p _ => match p with
    | (.pre, q) => pre q
    | (.post, q) => post q

/-- Read access to exactly a declared list of input queries: the only input a fetch or an
update ever sees. -/
abbrev Reads {State : Type u} (In : View State) (qs : List In.Q) : Type :=
  (i : In.Q) → i ∈ qs → In.A i

/-- The reads every query of a list answered by one reader. -/
def readsBy {State : Type u} {In : View State} (reader : (q : In.Q) → In.A q) (qs : List In.Q) :
    Reads In qs :=
  fun i _ => reader i

/-- Materialized answers, looked up by query (first match). -/
def lookup {Q : Type} [DecidableEq Q] {A : Q → Type} : List (Σ q, A q) → (i : Q) → Option (A i)
  | [], _ => none
  | ⟨q, a⟩ :: rest, i => if h : q = i then some (h ▸ a) else lookup rest i

theorem lookup_sound {Q : Type} [DecidableEq Q] {A : Q → Type} (f : (q : Q) → A q) :
    ∀ (l : List (Σ q, A q)), (∀ e ∈ l, e = ⟨e.1, f e.1⟩) → ∀ i a, lookup l i = some a → a = f i
  | [], _, _, _, h => by simp [lookup] at h
  | ⟨q, b⟩ :: rest, all, i, a, h => by
    simp only [lookup] at h
    split at h
    · rename_i same
      subst same
      cases h
      have := all ⟨q, b⟩ List.mem_cons_self
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
      exact this
    · exact lookup_sound f rest (fun e he => all e (List.mem_cons_of_mem _ he)) i a h

/-! ## Maintained implementations (closed) -/

/-- A view maintained beside an admitted run. A read is a `fetch`: it answers and may record
what it computed (a memo fill), returning the representation to keep. -/
structure Maintained (D : DeltaSystem.{u, v}) (V : View D.State) where
  Rep : Type
  Holds : Rep → D.State → Prop
  init : Rep
  init_holds : Holds init D.genesis
  fetch : Rep → (q : V.Q) → V.A q × Rep
  fetch_sound : ∀ {r s}, Holds r s → ∀ q, (fetch r q).1 = V.spec s q ∧ Holds (fetch r q).2 s
  advance : D.Delta → Rep → Rep
  advance_holds : ∀ {r s s'} (δ : D.Delta), Holds r s → D.step δ s = some s' →
    Holds (advance δ r) s'

namespace Maintained

variable {D : DeltaSystem.{u, v}} {V : View D.State} (M : Maintained D V)

/-- The answer of a read, discarding its fill. -/
def ask (r : M.Rep) (q : V.Q) : V.A q := (M.fetch r q).1

theorem ask_sound {r : M.Rep} {s : D.State} (h : M.Holds r s) (q : V.Q) : M.ask r q = V.spec s q :=
  (M.fetch_sound h q).1

/-- Read a list of queries, keeping every fill: the answers, materialized once. -/
def fetchAll : M.Rep → List V.Q → List (Σ q, V.A q) × M.Rep
  | r, [] => ([], r)
  | r, q :: qs =>
    let z := M.fetch r q
    let rest := fetchAll z.2 qs
    (⟨q, z.1⟩ :: rest.1, rest.2)

theorem fetchAll_sound : ∀ {r : M.Rep} {s : D.State} (qs : List V.Q), M.Holds r s →
    (∀ e ∈ (M.fetchAll r qs).1, e = ⟨e.1, V.spec s e.1⟩) ∧ M.Holds (M.fetchAll r qs).2 s
  | _, _, [], h => ⟨by simp [fetchAll], h⟩
  | r, s, q :: qs, h => by
    have hz := M.fetch_sound h q
    have ih := fetchAll_sound qs hz.2
    refine ⟨?_, ih.2⟩
    intro e he
    simp only [fetchAll, List.mem_cons] at he
    rcases he with rfl | he
    · simp only [hz.1]
    · exact ih.1 e he

/-- Advance over a run, delta by delta. -/
def advanceAll : List D.Delta → M.Rep → M.Rep
  | [], r => r
  | δ :: δs, r => advanceAll δs (M.advance δ r)

theorem run_holds : ∀ (δs : List D.Delta) {r : M.Rep} {s s' : D.State},
    M.Holds r s → D.run s δs = some s' → M.Holds (M.advanceAll δs r) s'
  | [], _, _, _, h, run => by
    simp only [DeltaSystem.run_nil, Option.some.injEq] at run; subst run; exact h
  | δ :: δs, _, s, _, h, run => by
    simp only [DeltaSystem.run] at run
    cases hstep : D.step δ s with
    | none => rw [hstep] at run; exact absurd run (by simp)
    | some m =>
      rw [hstep] at run
      exact run_holds δs (M.advance_holds δ h hstep) run

/-- **The keystone.** After any admitted run, from any representation holding at its start,
the maintained answers are the recomputation's answers at the state the run produced. -/
theorem maintained_eq_recompute (δs : List D.Delta) {r : M.Rep} {s s' : D.State}
    (h : M.Holds r s) (run : D.run s δs = some s') (q : V.Q) :
    M.ask (M.advanceAll δs r) q = V.spec s' q :=
  M.ask_sound (M.run_holds δs h run) q

/-- From genesis: at every reachable state the maintained answers are the recomputation's. -/
theorem reachable_eq_recompute (δs : List D.Delta) {s : D.State}
    (run : D.run D.genesis δs = some s) (q : V.Q) :
    M.ask (M.advanceAll δs M.init) q = V.spec s q :=
  M.maintained_eq_recompute δs M.init_holds run q

/-- Reads interleaved with writes: a read's fill never changes a later answer. -/
theorem fetch_then_recompute {r : M.Rep} {s : D.State} (h : M.Holds r s) (q q' : V.Q) :
    M.ask (M.fetch r q).2 q' = V.spec s q' :=
  M.ask_sound (M.fetch_sound h q).2 q'

/-- Teeth: a maintained view must move whenever the specification moves; an advance that
ignores a delta which changes an answer contradicts `advance_holds` + `fetch_sound`. -/
theorem stale_refuted {r : M.Rep} {s s' : D.State} {δ : D.Delta} (h : M.Holds r s)
    (step : D.step δ s = some s') (q : V.Q) (moved : V.spec s' q ≠ V.spec s q)
    (stale : M.advance δ r = r) : False :=
  moved (by rw [← M.ask_sound (M.advance_holds δ h step) q, stale, M.ask_sound h q])

/-- Teeth: no maintained view with a constant answer exists for a specification that differs
at two states the representation can hold. -/
theorem constant_refuted (q : V.Q) (a : V.A q) {r r' : M.Rep} {s s' : D.State}
    (h : M.Holds r s) (h' : M.Holds r' s') (differ : V.spec s q ≠ V.spec s' q)
    (constant : ∀ x, M.ask x q = a) : False :=
  differ ((M.ask_sound h q).symm.trans ((constant r).trans ((constant r').symm.trans (M.ask_sound h' q))))

/-! ### Checkpoints -/

/-- A checkpoint codec for a maintained representation. Under the trusted-storage threat
model (ember, 2026-10-31) the bytes read back are the bytes written; what is owed is that
decoding them yields a representation of the same state (not necessarily the same value: a
trie may be rebuilt), and that decoding a held representation's bytes never fails. Restart
COST is not stated here: a decode may rebuild; the concrete codec states what it carries. -/
structure Persist (Bytes : Type) where
  encode : M.Rep → Bytes
  decode : Bytes → Option M.Rep
  decode_holds : ∀ {r r' s}, M.Holds r s → decode (encode r) = some r' → M.Holds r' s
  decode_some : ∀ {r s}, M.Holds r s → (decode (encode r)).isSome

/-- **Checkpoint/restore**, from any held representation (after fills, at any sealed
height): restore and advance over the suffix answers what recomputation answers at the head.
The receiver owes that the suffix it advances over is exactly the one above the seal. -/
theorem checkpoint_restore_from {Bytes : Type} (P : M.Persist Bytes) (suffix : List D.Delta)
    {r restored : M.Rep} {s sn : D.State} (h : M.Holds r s)
    (restore : P.decode (P.encode r) = some restored) (run : D.run s suffix = some sn)
    (q : V.Q) : M.ask (M.advanceAll suffix restored) q = V.spec sn q :=
  M.maintained_eq_recompute suffix (P.decode_holds h restore) run q

/-- The genesis corollary: maintain through `pre`, checkpoint, restore, maintain through
`suffix`. -/
theorem checkpoint_restore {Bytes : Type} (P : M.Persist Bytes) (pre suffix : List D.Delta)
    {sk sn : D.State} (runPre : D.run D.genesis pre = some sk) (runSuf : D.run sk suffix = some sn)
    {restored : M.Rep} (restore : P.decode (P.encode (M.advanceAll pre M.init)) = some restored)
    (q : V.Q) : M.ask (M.advanceAll suffix restored) q = V.spec sn q :=
  M.checkpoint_restore_from P suffix (M.run_holds pre M.init_holds runPre) restore runSuf q

/-- Restore never fails on a checkpoint of a held representation. -/
theorem restore_exists {Bytes : Type} (P : M.Persist Bytes) {r : M.Rep} {s : D.State}
    (h : M.Holds r s) : ∃ restored, P.decode (P.encode r) = some restored :=
  Option.isSome_iff_exists.mp (P.decode_some h)

end Maintained

/-! ## Nodes (open over an input view) -/

/-- A derived structure over an input view. A read declares the input queries it needs given
its representation (`readProbes`: none on a memo hit, the dependencies on a miss) and sees
only their answers; an update declares its probes from the delta alone and sees only their
answers. The representation is free (it may hold anything); what is bounded is what a step
may read, against budgets stated per instance (`ReadFootprintBounded`, `ProbeFootprintBounded`). -/
structure Node (D : DeltaSystem.{u, v}) (In Out : View D.State) where
  Rep : Type
  Holds : Rep → D.State → Prop
  init : Rep
  init_holds : Holds init D.genesis
  readProbes : Rep → Out.Q → List In.Q
  fetch : (r : Rep) → (q : Out.Q) → Reads In (readProbes r q) → Out.A q × Rep
  fetch_sound : ∀ {r s}, Holds r s → ∀ q,
    (fetch r q (readsBy (In.spec s) _)).1 = Out.spec s q ∧
      Holds (fetch r q (readsBy (In.spec s) _)).2 s
  probes : D.Delta → List (Phase × In.Q)
  update : (δ : D.Delta) → Answers In (probes δ) → Rep → Rep
  update_holds : ∀ {r s s'} (δ : D.Delta), Holds r s → D.step δ s = some s' →
    Holds (update δ (answersBy (In.spec s) (In.spec s') (probes δ)) r) s'

namespace Node

variable {D : DeltaSystem.{u, v}} {In Out : View D.State}

/-- The per-delta read budget: a constant plus `k` probes per unit of delta size. -/
def ProbeFootprintBounded (N : Node D In Out) (size : D.Delta → Nat) (c k : Nat) : Prop :=
  ∀ δ, (N.probes δ).length ≤ c + k * size δ

/-- The per-read budget: a constant plus `k` input queries per unit of query size. -/
def ReadFootprintBounded (N : Node D In Out) (size : Out.Q → Nat) (c k : Nat) : Prop :=
  ∀ r q, (N.readProbes r q).length ≤ c + k * size q

/-- A node reads its input through a wider view's left half. -/
def weakenLeft (N : Node D In Out) (Extra : View D.State) : Node D (View.sum In Extra) Out where
  Rep := N.Rep
  Holds := N.Holds
  init := N.init
  init_holds := N.init_holds
  readProbes r q := (N.readProbes r q).map Sum.inl
  fetch r q reads := N.fetch r q (fun i h => reads (.inl i) (List.mem_map_of_mem h))
  fetch_sound := fun h q => N.fetch_sound h q
  probes δ := (N.probes δ).map fun p => (p.1, .inl p.2)
  update δ ans r := N.update δ (fun p h => ans (p.1, .inl p.2)
    (List.mem_map.mpr ⟨p, h, rfl⟩)) r
  update_holds := by
    intro r s s' δ h step
    refine (congrArg (fun a => N.Holds (N.update δ a r) s') ?_).mpr (N.update_holds δ h step)
    funext p hp
    rcases p with ⟨ph, q⟩
    cases ph <;> rfl

variable [DecidableEq In.Q]

/-- Answers materialized once: the pre-phase probes read before the input advances, the
post-phase probes after. -/
def phaseQueries (ph : Phase) (ps : List (Phase × In.Q)) : List In.Q :=
  (ps.filter (fun p => p.1 = ph)).map Prod.snd

/-- **The chain rule.** A node over a maintained input is maintained. Its reads and probes are
answered by the input's own fetches, materialized once, with the input's fills kept. -/
def stack (N : Node D In Out) (M : Maintained D In) : Maintained D (View.sum In Out) where
  Rep := M.Rep × N.Rep
  Holds p s := M.Holds p.1 s ∧ N.Holds p.2 s
  init := (M.init, N.init)
  init_holds := ⟨M.init_holds, N.init_holds⟩
  fetch p q := match q with
    | .inl q => let z := M.fetch p.1 q; (z.1, (z.2, p.2))
    | .inr q =>
      let got := M.fetchAll p.1 (N.readProbes p.2 q)
      let z := N.fetch p.2 q (fun i _ => (lookup got.1 i).getD (M.ask got.2 i))
      (z.1, (got.2, z.2))
  fetch_sound := by
    intro p s h q
    cases q with
    | inl q =>
      exact ⟨(M.fetch_sound h.1 q).1, (M.fetch_sound h.1 q).2, h.2⟩
    | inr q =>
      have got := M.fetchAll_sound (N.readProbes p.2 q) h.1
      have reads : (fun i (_ : i ∈ N.readProbes p.2 q) =>
          (lookup (M.fetchAll p.1 (N.readProbes p.2 q)).1 i).getD
            (M.ask (M.fetchAll p.1 (N.readProbes p.2 q)).2 i)) = readsBy (In.spec s) _ := by
        funext i _
        cases hl : lookup (M.fetchAll p.1 (N.readProbes p.2 q)).1 i with
        | none => exact M.ask_sound got.2 i
        | some a => exact lookup_sound (In.spec s) _ got.1 i a hl
      have hn := N.fetch_sound h.2 q
      refine ⟨?_, got.2, ?_⟩
      · show (N.fetch p.2 q _).1 = Out.spec s q
        rw [reads]; exact hn.1
      · show N.Holds (N.fetch p.2 q _).2 s
        rw [reads]; exact hn.2
  advance δ p :=
    let pre := M.fetchAll p.1 (phaseQueries .pre (N.probes δ))
    let m' := M.advance δ pre.2
    let post := M.fetchAll m' (phaseQueries .post (N.probes δ))
    let ans : Answers In (N.probes δ) := fun pq _ => match pq with
      | (.pre, i) => (lookup pre.1 i).getD (M.ask pre.2 i)
      | (.post, i) => (lookup post.1 i).getD (M.ask post.2 i)
    (post.2, N.update δ ans p.2)
  advance_holds := by
    intro p s s' δ h step
    have pre := M.fetchAll_sound (phaseQueries .pre (N.probes δ)) h.1
    have hm' := M.advance_holds δ pre.2 step
    have post := M.fetchAll_sound (phaseQueries .post (N.probes δ)) hm'
    refine ⟨post.2, ?_⟩
    have := N.update_holds δ h.2 step
    convert this using 2
    funext pq _
    rcases pq with ⟨ph, i⟩
    cases ph with
    | pre =>
      show (lookup _ i).getD _ = In.spec s i
      cases hl : lookup (M.fetchAll p.1 (phaseQueries .pre (N.probes δ))).1 i with
      | none => exact M.ask_sound pre.2 i
      | some a => exact lookup_sound (In.spec s) _ pre.1 i a hl
    | post =>
      show (lookup _ i).getD _ = In.spec s' i
      cases hl : lookup (M.fetchAll (M.advance δ (M.fetchAll p.1 (phaseQueries .pre (N.probes δ))).2)
          (phaseQueries .post (N.probes δ))).1 i with
      | none => exact M.ask_sound post.2 i
      | some a => exact lookup_sound (In.spec s') _ post.1 i a hl

end Node

/-! ## Red-green: the generic memo node for a derived query with declared reads -/

/-- A finite map with its two laws (a persistent tree or hash map at runtime; a function for
specification). -/
structure MapRep (K : Type) (V : K → Type) where
  M : Type
  empty : M
  get? : M → (k : K) → Option (V k)
  insert : M → (k : K) → V k → M
  get?_empty : ∀ k, get? empty k = none
  get?_insert_self : ∀ m k v, get? (insert m k v) k = some v
  get?_insert_ne : ∀ m k k' v, k' ≠ k → get? (insert m k v) k' = get? m k'

/-- The function-backed map: the specification representation (and a test instance). -/
def MapRep.ofFun (K : Type) [DecidableEq K] (V : K → Type) : MapRep K V where
  M := (k : K) → Option (V k)
  empty := fun _ => none
  get? m k := m k
  insert m k v := fun k' => if h : k' = k then h ▸ some v else m k'
  get?_empty _ := rfl
  get?_insert_self _ _ _ := by simp
  get?_insert_ne _ _ _ _ ne := by simp [ne]

/-- A derived query with declared reads. `compute` is the recomputation, and it can read only
the input queries `deps q` names (so the frame law is by construction); `touched` is a delta's
syntactic write set over the input (`touched_frame`: an input query a delta does not touch
answers the same after it). -/
structure Derivation (D : DeltaSystem.{u, v}) (In Out : View D.State) where
  deps : Out.Q → List In.Q
  compute : (q : Out.Q) → Reads In (deps q) → Out.A q
  compute_spec : ∀ s q, compute q (readsBy (In.spec s) _) = Out.spec s q
  touched : D.Delta → List In.Q
  touched_frame : ∀ {s s'} (δ : D.Delta), D.step δ s = some s' →
    ∀ i, i ∉ touched δ → In.spec s' i = In.spec s i

namespace Derivation

variable {D : DeltaSystem.{u, v}} {In Out : View D.State}

/-- The frame law, derived: two states agreeing on a query's dependencies agree on it. -/
theorem frame (R : Derivation D In Out) (q : Out.Q) (s s' : D.State)
    (same : ∀ i ∈ R.deps q, In.spec s i = In.spec s' i) : Out.spec s q = Out.spec s' q := by
  rw [← R.compute_spec s q, ← R.compute_spec s' q]
  congr 1
  funext i hi
  exact same i hi

/-- Teeth: a derivation that declares no reads has an answer that no state can move. -/
theorem empty_deps_constant (R : Derivation D In Out) (q : Out.Q) (empty : R.deps q = [])
    (s s' : D.State) : Out.spec s q = Out.spec s' q :=
  R.frame q s s' (by simp [empty])

end Derivation

/-- The red-green representation: a clock, the clock at which each input query was last
touched, and memo entries stamped with the clock at which they were computed. -/
structure RedGreenRep (In Out : Type) (OutA : Out → Type) (Stamps : MapRep In (fun _ => Nat))
    (Memo : MapRep Out (fun q => OutA q × Nat)) where
  clock : Nat
  stamps : Stamps.M
  memo : Memo.M

namespace RedGreen

variable {D : DeltaSystem.{u, v}} {In Out : View D.State}

/-- An entry is green when no input it reads was touched after it was stamped. -/
def green {Stamps : MapRep In.Q (fun _ => Nat)} (stamps : Stamps.M) (deps : List In.Q)
    (t : Nat) : Bool :=
  deps.all fun i => (Stamps.get? stamps i).getD 0 ≤ t

theorem green_iff {Stamps : MapRep In.Q (fun _ => Nat)} (stamps : Stamps.M) (deps : List In.Q)
    (t : Nat) : green (In := In) stamps deps t = true ↔ ∀ i ∈ deps, (Stamps.get? stamps i).getD 0 ≤ t := by
  simp [green]

/-- Touch every input a delta writes: stamp it with the next clock. -/
def touchAll {Stamps : MapRep In.Q (fun _ => Nat)} (stamps : Stamps.M) (clock : Nat) :
    List In.Q → Stamps.M
  | [] => stamps
  | i :: is => touchAll (Stamps.insert stamps i clock) clock is

theorem touchAll_get [DecidableEq In.Q] {Stamps : MapRep In.Q (fun _ => Nat)} :
    ∀ (stamps : Stamps.M) (clock : Nat) (is : List In.Q) (i : In.Q),
      Stamps.get? (touchAll stamps clock is) i =
        if i ∈ is then some clock else Stamps.get? stamps i
  | stamps, clock, [], i => by simp [touchAll]
  | stamps, clock, j :: js, i => by
    rw [touchAll, touchAll_get _ clock js i]
    by_cases hi : i ∈ js
    · simp [hi]
    · by_cases hij : i = j
      · subst hij; simp [Stamps.get?_insert_self]
      · simp [hi, hij, Stamps.get?_insert_ne _ _ _ _ hij]

variable [DecidableEq In.Q] (R : Derivation D In Out) (Stamps : MapRep In.Q (fun _ => Nat))
  (Memo : MapRep Out.Q (fun q => Out.A q × Nat))

/-- Whether a read is a hit (a green entry). -/
def hit (r : RedGreenRep In.Q Out.Q Out.A Stamps Memo) (q : Out.Q) : Option (Out.A q) :=
  match Memo.get? r.memo q with
  | some (v, t) => if green (In := In) r.stamps (R.deps q) t then some v else none
  | none => none

/-- The red-green invariant: stamps and entries never run ahead of the clock, and a green
entry is the specification's answer. -/
def Inv (r : RedGreenRep In.Q Out.Q Out.A Stamps Memo) (s : D.State) : Prop :=
  (∀ i, (Stamps.get? r.stamps i).getD 0 ≤ r.clock) ∧
  (∀ q v t, Memo.get? r.memo q = some (v, t) → t ≤ r.clock) ∧
  (∀ q v t, Memo.get? r.memo q = some (v, t) →
    (∀ i ∈ R.deps q, (Stamps.get? r.stamps i).getD 0 ≤ t) → v = Out.spec s q)

omit [DecidableEq In.Q] in
theorem hit_sound {r : RedGreenRep In.Q Out.Q Out.A Stamps Memo} {s : D.State}
    (h : Inv R Stamps Memo r s) (q : Out.Q) (v : Out.A q) (hv : hit R Stamps Memo r q = some v) :
    v = Out.spec s q := by
  unfold hit at hv
  split at hv
  · rename_i v' t hm
    split at hv
    · cases hv; exact h.2.2 q _ t hm ((green_iff _ _ _).1 (by assumption))
    · cases hv
  · cases hv

/-- The input queries a read needs: none on a hit, the dependencies on a miss. -/
def readProbes (r : RedGreenRep In.Q Out.Q Out.A Stamps Memo) (q : Out.Q) : List In.Q :=
  match hit R Stamps Memo r q with
  | some _ => []
  | none => R.deps q

omit [DecidableEq In.Q] in
theorem readProbes_miss {r : RedGreenRep In.Q Out.Q Out.A Stamps Memo} {q : Out.Q}
    (miss : hit R Stamps Memo r q = none) : readProbes R Stamps Memo r q = R.deps q := by
  simp [readProbes, miss]

/-- **The generic memo node.** No update probes: a write stamps the inputs the delta touches
(`touched`, from its syntax). A read on a green entry reads no input; a miss reads exactly its
dependencies, computes, and remembers the answer at the current clock. -/
def node : Node D In Out where
  Rep := RedGreenRep In.Q Out.Q Out.A Stamps Memo
  Holds := Inv R Stamps Memo
  init := ⟨0, Stamps.empty, Memo.empty⟩
  init_holds := by
    refine ⟨fun i => by simp [Stamps.get?_empty], fun q v t h => ?_, fun q v t h => ?_⟩ <;>
      simp [Memo.get?_empty] at h
  readProbes := readProbes R Stamps Memo
  fetch r q reads :=
    match hv : hit R Stamps Memo r q with
    | some v => (v, r)
    | none =>
      let a := R.compute q (fun i hi => reads i ((readProbes_miss R Stamps Memo hv).symm ▸ hi))
      (a, ⟨r.clock, r.stamps, Memo.insert r.memo q (a, r.clock)⟩)
  fetch_sound := by
    intro r s h q
    obtain ⟨hclock, hmemo, hval⟩ := h
    split
    · rename_i v hv
      exact ⟨hit_sound R Stamps Memo ⟨hclock, hmemo, hval⟩ q v hv, hclock, hmemo, hval⟩
    · rename_i hv
      have ca : R.compute q (fun i hi => readsBy (In.spec s) _ i
          ((readProbes_miss R Stamps Memo hv).symm ▸ hi)) = Out.spec s q := R.compute_spec s q
      refine ⟨ca, hclock, fun q' v t hq' => ?_, fun q' v t hq' _ => ?_⟩
      · by_cases e : q' = q
        · subst e; rw [Memo.get?_insert_self] at hq'; cases hq'; exact Nat.le_refl _
        · rw [Memo.get?_insert_ne _ _ _ _ e] at hq'; exact hmemo q' v t hq'
      · by_cases e : q' = q
        · subst e; rw [Memo.get?_insert_self] at hq'; cases hq'; exact ca
        · rw [Memo.get?_insert_ne _ _ _ _ e] at hq'
          exact hval q' v t hq' (by assumption)
  probes _ := []
  update δ _ r := ⟨r.clock + 1, touchAll r.stamps (r.clock + 1) (R.touched δ), r.memo⟩
  update_holds := by
    intro r s s' δ h step
    obtain ⟨hclock, hmemo, hval⟩ := h
    refine ⟨fun i => ?_, fun q v t hq => Nat.le_succ_of_le (hmemo q v t hq), fun q v t hq hgreen => ?_⟩
    · show (Stamps.get? (touchAll r.stamps (r.clock + 1) (R.touched δ)) i).getD 0 ≤ r.clock + 1
      rw [touchAll_get]
      split
      · simp
      · exact Nat.le_succ_of_le (hclock i)
    · -- every read input was untouched (its stamp ≤ t ≤ clock < clock + 1), so the entry was
      -- green before the delta and the answer did not move.
      have ht := hmemo q v t hq
      have untouched : ∀ i ∈ R.deps q, i ∉ R.touched δ := by
        intro i hi hmem
        have := hgreen i hi
        rw [touchAll_get] at this
        simp [hmem] at this; omega
      have before : ∀ i ∈ R.deps q, (Stamps.get? r.stamps i).getD 0 ≤ t := by
        intro i hi
        have := hgreen i hi
        rw [touchAll_get] at this
        simpa [untouched i hi] using this
      rw [hval q v t hq before]
      exact R.frame q s s' (fun i hi => (R.touched_frame δ step i (untouched i hi)).symm)

/-- A hit reads nothing; a miss reads exactly the declared dependencies. -/
theorem node_readFootprintBounded (c : Nat) (bound : ∀ q, (R.deps q).length ≤ c) :
    (node R Stamps Memo).ReadFootprintBounded (fun _ => 0) c 0 := by
  intro r q
  show (readProbes R Stamps Memo r q).length ≤ c + 0 * 0
  unfold readProbes
  split
  · simp
  · simpa using bound q

end RedGreen

/-! ## Leaves: the store itself -/

section StoreLeaf

variable (L : Store.Layout.{0, 0, 0})

open Minidregg.Theory.Store

/-- The store advanced by guarded patches: a patch is admitted exactly when it is valid from
the store it meets. -/
abbrev storeSystem (genesis : Store L) : DeltaSystem.{0, 0} where
  State := Store L
  Delta := Patch L
  step p s := if Patch.ValidFrom s p then some (Patch.run s p) else none
  genesis := genesis

/-- One address, one answer. -/
abbrev storeView (genesis : Store L) : View (storeSystem L genesis).State where
  Q := Address L
  A a := Option (L.Value a.1)
  spec (s : Store L) a := s a

/-- The held store is the leaf layer: its representation is the store. -/
def storeLeaf (genesis : Store L) : Maintained (storeSystem L genesis) (storeView L genesis) where
  Rep := Store L
  Holds r s := r = s
  init := genesis
  init_holds := rfl
  fetch r a := (r a, r)
  fetch_sound := by intro r s h q; subst h; exact ⟨rfl, rfl⟩
  advance p r := Patch.run r p
  advance_holds := by
    intro r s s' p h step
    subst h
    simp only [storeSystem] at step
    split at step
    · cases step; rfl
    · cases step

/-- A patch's syntactic write set touches every address it changes (`Patch.run_frame`). -/
theorem store_touched_frame (genesis : Store L) {s s' : Store L} (p : Patch L)
    (step : (storeSystem L genesis).step p s = some s') (a : Address L)
    (outside : a ∉ p.filterMap Op.writeAddress?) :
    (storeView L genesis).spec s' a = (storeView L genesis).spec s a := by
  simp only [storeSystem] at step
  split at step
  · cases step
    exact Patch.run_frame s p a (by simpa [Patch.writeFootprint] using outside)
  · cases step

end StoreLeaf


/-! ## Witnesses (ATLAS law 2) -/

namespace Example

open Minidregg.Theory.Store
open Minidregg.Theory.Store.Example

abbrev sys : DeltaSystem := storeSystem layout Example.empty
abbrev leaf := storeLeaf layout Example.empty

/-- Heap cell `k` as an integer (absent is 0). -/
def g (s : Store layout) (k : Nat) : Int := ((s ⟨Namespace.heap, k⟩).getD 0 : Nat)

/-- The derived value: the total of heap cells 0 and 1. -/
def pairTotal (s : Store layout) : Int := g s 0 + g s 1

/-- A guarded op's own change to the total, read off its before/after syntax. -/
def opDelta : Op layout → Int
  | .write .heap k b a => if k = 0 ∨ k = 1 then (a : Int) - b else 0
  | .allocate .heap k v => if k = 0 ∨ k = 1 then (v : Int) else 0
  | .free .heap k b => if k = 0 ∨ k = 1 then -(b : Int) else 0
  | _ => 0

def patchDelta (p : Patch layout) : Int := (p.map opDelta).sum

theorem g_set_same (s : Store layout) (k : Nat) (v : Option Nat) :
    g (s.set ⟨Namespace.heap, k⟩ v) k = ((v.getD 0 : Nat) : Int) := by
  simp [g, Store.set_eq]

theorem g_set_other (s : Store layout) (k j : Nat) (v : Option Nat) (ne : j ≠ k) :
    g (s.set ⟨Namespace.heap, k⟩ v) j = g s j := by
  unfold g; rw [Store.set_ne _ _ _ _ (by simp [ne])]

theorem g_set_ns (s : Store layout) (n : Namespace) (k j : Nat) (v : Option Nat)
    (ne : n ≠ Namespace.heap) : g (s.set ⟨n, k⟩ v) j = g s j := by
  unfold g; rw [Store.set_ne _ _ _ _ (by simp [Ne.symm ne])]

/-- The local update lemma: one enabled op moves the total by its own delta. -/
theorem op_total (s : Store layout) (op : Op layout) (enabled : op.Enabled s) :
    pairTotal (op.apply s) = pairTotal s + opDelta op := by
  cases op with
  | read => simp [Op.apply, opDelta]
  | write n k b a =>
    cases n with
    | heap =>
      have hb : g s k = (b : Int) := by simp [g, enabled.2]
      simp only [Op.apply, opDelta, pairTotal]
      by_cases h0 : k = 0
      · subst h0; rw [g_set_same, g_set_other _ _ _ _ (by decide)]; simp; omega
      · by_cases h1 : k = 1
        · subst h1; rw [g_set_same, g_set_other _ _ _ _ (by decide)]; simp; omega
        · rw [g_set_other _ _ _ _ (Ne.symm h0), g_set_other _ _ _ _ (Ne.symm h1)]; simp [h0, h1]
    | code => simp [Op.apply, opDelta, pairTotal, g_set_ns _ _ _ _ _ (by decide : Namespace.code ≠ _)]
    | log => simp [Op.apply, opDelta, pairTotal, g_set_ns _ _ _ _ _ (by decide : Namespace.log ≠ _)]
  | allocate n k v =>
    cases n with
    | heap =>
      have hb : g s k = 0 := by simp [g, show s ⟨Namespace.heap, k⟩ = none from enabled.2]
      simp only [Op.apply, opDelta, pairTotal]
      by_cases h0 : k = 0
      · subst h0; rw [g_set_same, g_set_other _ _ _ _ (by decide)]; simp; omega
      · by_cases h1 : k = 1
        · subst h1; rw [g_set_same, g_set_other _ _ _ _ (by decide)]; simp; omega
        · rw [g_set_other _ _ _ _ (Ne.symm h0), g_set_other _ _ _ _ (Ne.symm h1)]; simp [h0, h1]
    | code => simp [Op.apply, opDelta, pairTotal, g_set_ns _ _ _ _ _ (by decide : Namespace.code ≠ _)]
    | log => simp [Op.apply, opDelta, pairTotal, g_set_ns _ _ _ _ _ (by decide : Namespace.log ≠ _)]
  | free n k b =>
    cases n with
    | heap =>
      have hb : g s k = (b : Int) := by simp [g, enabled.2]
      simp only [Op.apply, opDelta, pairTotal]
      by_cases h0 : k = 0
      · subst h0; rw [g_set_same, g_set_other _ _ _ _ (by decide)]; simp; omega
      · by_cases h1 : k = 1
        · subst h1; rw [g_set_same, g_set_other _ _ _ _ (by decide)]; simp; omega
        · rw [g_set_other _ _ _ _ (Ne.symm h0), g_set_other _ _ _ _ (Ne.symm h1)]; simp [h0, h1]
    | code => simp [Op.apply, opDelta, pairTotal, g_set_ns _ _ _ _ _ (by decide : Namespace.code ≠ _)]
    | log => simp [Op.apply, opDelta, pairTotal, g_set_ns _ _ _ _ _ (by decide : Namespace.log ≠ _)]

theorem patch_total : ∀ (s : Store layout) (p : Patch layout), Patch.ValidFrom s p →
    pairTotal (Patch.run s p) = pairTotal s + patchDelta p
  | s, [], _ => by simp [Patch.run, patchDelta]
  | s, op :: rest, ⟨en, valid⟩ => by
    rw [Patch.run_cons, patch_total _ rest valid, op_total s op en]
    simp [patchDelta]; omega

/-- The total as a view: one query. -/
abbrev totalView : View sys.State where
  Q := Unit
  A _ := Int
  spec s _ := pairTotal s

/-- Layer 1: the total, maintained from the ops' own deltas. No probes. -/
def totalNode : Node sys (storeView layout Example.empty) totalView where
  Rep := Int
  Holds r s := r = pairTotal s
  init := 0
  init_holds := by simp [pairTotal, g, Example.empty]
  readProbes _ _ := []
  fetch r _ _ := (r, r)
  fetch_sound := by intro r s h q; exact ⟨h, h⟩
  probes _ := []
  update p _ r := r + patchDelta p
  update_holds := by
    intro r s s' p h step
    simp only at step
    split at step
    · rename_i valid; cases step; rw [h, patch_total s p valid]
    · cases step

abbrev layer1 := totalNode.stack leaf

/-- The flag as a view: is the total at least 10. -/
abbrev flagView : View sys.State where
  Q := Unit
  A _ := Bool
  spec s _ := decide (10 ≤ pairTotal s)

/-- Layer 2: the flag, reading ONE post answer of layer 1 per delta. -/
def flagNode : Node sys (View.sum (storeView layout Example.empty) totalView) flagView where
  Rep := Bool
  Holds r s := r = decide (10 ≤ pairTotal s)
  init := false
  init_holds := by simp [pairTotal, g, Example.empty]
  readProbes _ _ := []
  fetch r _ _ := (r, r)
  fetch_sound := by intro r s h q; exact ⟨h, h⟩
  probes _ := [(.post, .inr ())]
  update _ ans _ :=
    let total : Int := ans (.post, .inr ()) List.mem_cons_self
    decide (10 ≤ total)
  update_holds := by
    intro r s s' p h step
    rfl

abbrev graph := flagNode.stack layer1

theorem flagNode_probeFootprintBounded : flagNode.ProbeFootprintBounded (fun _ => 0) 1 0 := fun _ => by
  simp [flagNode]

theorem totalNode_probeFootprintBounded : totalNode.ProbeFootprintBounded (fun _ => 0) 0 0 := fun _ => by
  simp [totalNode]

/-- Premise inhabitation: the graph's representation relation holds at genesis. -/
theorem holds_inhabited : ∃ r s, graph.Holds r s := ⟨graph.init, _, graph.init_holds⟩

def runA : List (Patch layout) := [[allocate .heap 0 7], [allocate .heap 1 5], [write .heap 0 7 3]]

def s1 : Store layout := Patch.run Example.empty [allocate .heap 0 7]
def s2 : Store layout := Patch.run s1 [allocate .heap 1 5]
def s3 : Store layout := Patch.run s2 [write .heap 0 7 3]

abbrev graphView := View.sum (View.sum (storeView layout Example.empty) totalView) flagView
abbrev flagQ : graphView.Q := Sum.inr ()

/-- Satisfiable: on a real admitted run the graph's answers are the recomputation's, and they
are the values one expects (the flag rose to true at 12 and fell to false at 8). -/
theorem flag_reachable :
    sys.run sys.genesis runA = some s3 ∧
      graph.ask (graph.advanceAll runA graph.init) flagQ = false ∧
      graph.ask (graph.advanceAll (runA.take 2) graph.init) flagQ = true := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [graph.reachable_eq_recompute runA (s := s3) (by decide)]
    exact (show decide (10 ≤ pairTotal s3) = false by decide)
  · rw [graph.reachable_eq_recompute (runA.take 2) (s := s2) (by decide)]
    exact (show decide (10 ≤ pairTotal s2) = true by decide)

/-- Teeth: no maintained total ignores deltas (the first allocation moves the total). -/
theorem ignoring_update_refuted (M : Maintained sys totalView) (ignores : ∀ δ r, M.advance δ r = r) :
    False :=
  M.stale_refuted (s' := s1) M.init_holds (δ := [allocate .heap 0 7]) (by decide) () (by decide)
    (ignores _ _)

/-- The red-green derivation of the total over the store: reads heap 0 and 1, touched by a
patch's write footprint. -/
def totalDerivation : Derivation sys (storeView layout Example.empty) totalView where
  deps _ := [⟨Namespace.heap, 0⟩, ⟨Namespace.heap, 1⟩]
  compute _ reads :=
    (((reads ⟨Namespace.heap, 0⟩ (by simp)).getD 0 : Nat) : Int) +
      (((reads ⟨Namespace.heap, 1⟩ (by simp)).getD 0 : Nat) : Int)
  compute_spec _ _ := rfl
  touched p := p.filterMap Op.writeAddress?
  touched_frame δ step i h := store_touched_frame layout Example.empty δ step i h

/-- Teeth: a derivation of the total that declares no reads cannot exist. -/
theorem empty_deps_refuted (R : Derivation sys (storeView layout Example.empty) totalView)
    (empty : R.deps () = []) : False := by
  have := R.empty_deps_constant () empty Example.empty s1
  revert this; decide

abbrev memo := (RedGreen.node totalDerivation (MapRep.ofFun _ _) (MapRep.ofFun _ _)).stack leaf

/-- The red-green memo answers the recomputation after a run, and after a remembered read. -/
abbrev totalQ : (View.sum (storeView layout Example.empty) totalView).Q := Sum.inr ()

theorem memo_reachable :
    memo.ask (memo.fetch (memo.advanceAll (runA.take 2) memo.init) totalQ).2 totalQ = (12 : Int) := by
  rw [memo.fetch_then_recompute (memo.run_holds (runA.take 2) memo.init_holds (s' := s2) (by decide))]
  exact (show pairTotal s2 = 12 by decide)

abbrev memoNode := RedGreen.node totalDerivation (MapRep.ofFun _ _) (MapRep.ofFun _ _)

/-- Satisfiable, operationally: a cold read misses and reads both dependencies; once
remembered, the same read is a hit and reads no input; a write to heap 0 turns it red. -/
theorem memo_hit_reads_nothing :
    let r0 := (memo.advanceAll (runA.take 2) memo.init).2
    let r1 := (memo.fetch (memo.advanceAll (runA.take 2) memo.init) totalQ).2.2
    memoNode.readProbes r0 () = [⟨Namespace.heap, 0⟩, ⟨Namespace.heap, 1⟩] ∧
      memoNode.readProbes r1 () = [] ∧
      memoNode.readProbes (memo.advance [write .heap 0 7 3] (memo.fetch (memo.advanceAll (runA.take 2)
        memo.init) totalQ).2).2 () = [⟨Namespace.heap, 0⟩, ⟨Namespace.heap, 1⟩] := by
  decide

end Example

#assert_axioms DeltaSystem.run_append
#assert_axioms Maintained.run_holds
#assert_axioms Maintained.maintained_eq_recompute
#assert_axioms Maintained.reachable_eq_recompute
#assert_axioms Maintained.checkpoint_restore
#assert_axioms Maintained.stale_refuted
#assert_axioms Maintained.constant_refuted
#assert_axioms Node.stack
#assert_axioms Derivation.empty_deps_constant
#assert_axioms RedGreen.node
#assert_axioms storeLeaf
#assert_axioms Example.flag_reachable
#assert_axioms Example.ignoring_update_refuted
#assert_axioms Example.empty_deps_refuted
#assert_axioms Example.memo_reachable
#assert_axioms Example.memo_hit_reads_nothing
#assert_axioms Maintained.checkpoint_restore_from
#assert_axioms Node.weakenLeft
#assert_axioms RedGreen.node_readFootprintBounded
#assert_axioms Derivation.frame
#assert_axioms Example.holds_inhabited
#assert_axioms Example.flagNode_probeFootprintBounded

#assert_axioms DeltaSystem.run_cons
#assert_axioms lookup_sound
#assert_axioms Maintained.ask_sound
#assert_axioms Maintained.fetchAll_sound
#assert_axioms Maintained.fetch_then_recompute
#assert_axioms Maintained.restore_exists
#assert_axioms RedGreen.green_iff
#assert_axioms RedGreen.touchAll_get
#assert_axioms RedGreen.hit_sound
#assert_axioms RedGreen.readProbes_miss
#assert_axioms store_touched_frame
#assert_axioms Example.g_set_same
#assert_axioms Example.g_set_other
#assert_axioms Example.g_set_ns
#assert_axioms Example.op_total
#assert_axioms Example.patch_total
#assert_axioms Example.totalNode_probeFootprintBounded

end Minidregg.Theory.Retained
