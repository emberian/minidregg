/-
# Pred.SatisfiableTotal — `DiffProblem.decide` never says `unknown` on a translated law.

`Pred.Satisfiable` makes every answer safe: a witness is re-checked by `eval`, an `unsat`
carries a certificate `SysCert.check` accepts. This file proves the answer always comes:
for every law `Pred.difference?` translates, `decide` returns a witness or a certificate
(`decide_never_unknown`). Three facts carry it.

* **Bellman–Ford finds a potential or a negative cycle** (`solve_total`). After `i` rounds a
  node's distance is at most the weight of every walk of at most `i` constraints ending at it
  (`rounds_bound`), and every distance is the weight of the walk the table stores
  (`Inv`). If a constraint is still violated after `|nodes|` rounds, the stored walk through it
  is lighter than every walk short enough to repeat no node; cutting cycles out of it
  (`findNeg`) must therefore reach one of negative weight (`findNeg_finds`). If none is
  violated, the distances are a potential and the step built from them satisfies the system.
* **Each system implies the law** (`dnf_sound`): the converse of `difference_faithful`, so a
  step satisfying a system passes `eval`'s re-check.
* **Every translated system is well formed** (`dnf_wf`): constrained nodes are required
  present, and `zero` is never required absent, so the built step reads each node as the
  potential says.

Core Lean only, within the Pred boundary.
-/
import Pred.Satisfiable

namespace Minidregg.Pred.Sat

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-! ## §1. Walks -/

/-- The weight of a walk: the sum of its bounds. -/
def weight (w : List Con) : Int := (w.map Con.k).sum

/-- A walk, latest constraint first: each constraint's right node is the next one's left node. -/
def Linked : List Con → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => a.y = b.x ∧ Linked (b :: l)

/-- The walk ends at `v`: its latest constraint's left node is `v` (the empty walk ends anywhere). -/
def EndsAt (v : Node) (w : List Con) : Prop := ∀ e, w.head? = some e → e.x = v

theorem weight_cons (c : Con) (w : List Con) : weight (c :: w) = c.k + weight w := by
  simp [weight, List.sum_cons]

theorem weight_append (a b : List Con) : weight (a ++ b) = weight a + weight b := by
  simp [weight, List.sum_append]

theorem linked_append :
    ∀ (l₁ l₂ : List Con), Linked (l₁ ++ l₂) ↔
      Linked l₁ ∧ Linked l₂ ∧ ∀ a b, l₁.getLast? = some a → l₂.head? = some b → a.y = b.x
  | [], l₂ => by simp [Linked]
  | [a], [] => by simp [Linked]
  | [a], b :: l => by simp [Linked, and_comm]
  | a :: b :: l, l₂ => by
      have ih := linked_append (b :: l) l₂
      simp only [List.cons_append] at ih ⊢
      simp only [Linked, ih, List.getLast?_cons_cons]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩

theorem linked_tail {a : Con} {l : List Con} (h : Linked (a :: l)) : Linked l := by
  cases l with
  | nil => trivial
  | cons b l => exact h.2

theorem linked_tail_ends {a : Con} {l : List Con} (h : Linked (a :: l)) : EndsAt a.y l := by
  cases l with
  | nil => intro e he; cases he
  | cons b l => intro e he; cases he; exact h.1.symm

theorem linked_cons {c : Con} {w : List Con} (hl : Linked w) (he : EndsAt c.y w) :
    Linked (c :: w) := by
  cases w with
  | nil => trivial
  | cons b l => exact ⟨(he b rfl).symm, hl⟩

/-- The right nodes of a walk are its left nodes shifted by one, closed by the last right node. -/
theorem map_y_of_linked :
    ∀ (a : Con) (l : List Con) (b : Con), Linked (a :: l) → (a :: l).getLast? = some b →
      (a :: l).map Con.y = l.map Con.x ++ [b.y]
  | a, [], b, _, hb => by simp at hb; subst hb; rfl
  | a, c :: l, b, h, hb => by
      rw [List.getLast?_cons_cons] at hb
      have ih := map_y_of_linked c l b h.2 hb
      rw [List.map_cons, ih, h.1]
      rfl

/-- A closed walk's left nodes permute its right nodes. -/
theorem perm_of_closed {cyc : List Con} {a b : Con} (hl : Linked cyc) (ha : cyc.head? = some a)
    (hb : cyc.getLast? = some b) (hab : b.y = a.x) : (cyc.map Con.x).Perm (cyc.map Con.y) := by
  cases cyc with
  | nil => cases ha
  | cons a' l =>
      cases ha
      rw [map_y_of_linked a l b hl hb, hab, List.map_cons]
      exact (List.perm_append_singleton a.x (l.map Con.x)).symm

/-! ## §2. Cutting cycles out of a walk -/

theorem idxOfX_some {v : Node} :
    ∀ (l : List Con) (i : Nat), idxOfX v l = some i → ∃ c, l[i]? = some c ∧ c.x = v
  | [], _, h => by cases h
  | c :: rest, i, h => by
      simp only [idxOfX] at h
      split at h
      · cases h; rename_i hc; exact ⟨c, rfl, by simpa using hc⟩
      · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨c', h1, h2⟩ := idxOfX_some rest j hj
        exact ⟨c', by simpa using h1, h2⟩

theorem idxOfX_none {v : Node} : ∀ (l : List Con), idxOfX v l = none → ∀ c ∈ l, c.x ≠ v
  | [], _, _, h => by cases h
  | c :: rest, h, c', hc' => by
      simp only [idxOfX] at h
      split at h
      · cases h
      · rename_i hc
        rcases List.mem_cons.mp hc' with rfl | hm
        · simpa using hc
        · exact idxOfX_none rest (Option.map_eq_none_iff.mp h) c' hm

theorem splitCycle_some :
    ∀ (W acc pre cyc post : List Con), splitCycle acc W = some (pre, cyc, post) →
      acc ++ W = pre ++ cyc ++ post ∧
        ∃ a b, cyc.head? = some a ∧ cyc.getLast? = some b ∧ b.y = a.x
  | [], _, _, _, _, h => by cases h
  | e :: rest, acc, pre, cyc, post, h => by
      simp only [splitCycle] at h
      split at h
      · rename_i i hi
        cases h
        obtain ⟨c, hc, hcx⟩ := idxOfX_some _ i hi
        have hlt : i < (acc ++ [e]).length := by
          obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hc
          exact hlt
        refine ⟨?_, c, e, by rw [List.head?_drop]; exact hc, ?_, hcx.symm⟩
        · rw [List.take_append_drop]; simp
        · rw [List.getLast?_drop, if_neg (by omega)]; exact List.getLast?_concat
      · have := splitCycle_some rest (acc ++ [e]) pre cyc post h
        simpa using this

theorem splitCycle_none :
    ∀ (W acc : List Con), Linked (acc ++ W) → (acc.map Con.x).Nodup →
      (∀ a, acc.getLast? = some a → a.y ∉ acc.map Con.x) →
      splitCycle acc W = none → ((acc ++ W).map Con.x).Nodup
  | [], acc, _, hn, _, _ => by simpa using hn
  | e :: rest, acc, hl, hn, hlast, h => by
      simp only [splitCycle] at h
      split at h
      · cases h
      · rename_i hi
        have hy := idxOfX_none _ hi
        have hl' : Linked ((acc ++ [e]) ++ rest) := by simpa using hl
        have hex : e.x ∉ acc.map Con.x := by
          cases hacc : acc.getLast? with
          | none =>
              rw [List.getLast?_eq_none_iff] at hacc; subst hacc; simp
          | some a =>
              have hj := ((linked_append acc (e :: rest)).mp hl).2.2 a e hacc rfl
              rw [← hj]
              exact hlast a hacc
        have hn' : ((acc ++ [e]).map Con.x).Nodup := by
          rw [List.map_append, List.nodup_append]
          refine ⟨hn, by simp, ?_⟩
          intro a ha b hb
          simp at hb; subst hb
          intro hab; exact hex (hab ▸ ha)
        have hlast' : ∀ a, (acc ++ [e]).getLast? = some a → a.y ∉ (acc ++ [e]).map Con.x := by
          intro a ha
          rw [List.getLast?_concat] at ha
          cases ha
          intro hm
          obtain ⟨c, hc, hcx⟩ := List.mem_map.mp hm
          exact hy c hc hcx
        have := splitCycle_none rest (acc ++ [e]) hl' hn' hlast' h
        simpa using this

/-- A duplicate-free list inside `S` is no longer than `S`. -/
theorem nodup_length_le :
    ∀ (l S : List Node), l.Nodup → (∀ a ∈ l, a ∈ S) → l.length ≤ S.length
  | [], _, _, _ => by simp
  | a :: l, S, hn, hs => by
      rw [List.nodup_cons] at hn
      have haS := hs a (List.mem_cons_self ..)
      have ih := nodup_length_le l (S.erase a) hn.2 fun b hb =>
        (List.mem_erase_of_ne (fun e => hn.1 (by rw [← e]; exact hb))).mpr (hs b (List.mem_cons_of_mem _ hb))
      rw [List.length_erase_of_mem haS] at ih
      have : 0 < S.length := List.length_pos_of_mem haS
      simp only [List.length_cons]
      omega

/-- **`findNeg_finds`** — a walk lighter than every walk short enough to repeat no node
contains a negative cycle, and cutting cycles out of it finds one. -/
theorem findNeg_finds (cs : List Con) (vs : List Node) (hvs : ∀ c ∈ cs, c.x ∈ vs) (v : Node)
    (B : Int)
    (hB : ∀ W, Linked W → (∀ e ∈ W, e ∈ cs) → EndsAt v W → W.length ≤ vs.length → B ≤ weight W) :
    ∀ (fuel : Nat) (W : List Con), W.length < fuel → Linked W → (∀ e ∈ W, e ∈ cs) →
      EndsAt v W → weight W < B →
      ∃ cyc, findNeg fuel W = some cyc ∧ (∀ c ∈ cyc, c ∈ cs) ∧
        (cyc.map Con.x).Perm (cyc.map Con.y) ∧ weight cyc < 0
  | 0, _, hlen, _, _, _, _ => absurd hlen (Nat.not_lt_zero _)
  | f + 1, W, hlen, hl, hcs, hend, hw => by
      simp only [findNeg]
      split
      · rename_i hnone
        have hnd := splitCycle_none W [] (by simpa using hl) (by simp) (by simp) hnone
        simp only [List.nil_append] at hnd
        have hle := nodup_length_le _ vs hnd fun a ha => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
          exact hvs c (hcs c hc)
        simp only [List.length_map] at hle
        have := hB W hl hcs hend hle
        omega
      · rename_i pre cyc post hsome
        obtain ⟨heq, a, b, ha, hb, hab⟩ := splitCycle_some W [] pre cyc post hsome
        simp only [List.nil_append] at heq
        subst heq
        have hl3 := (linked_append (pre ++ cyc) post).mp hl
        have hl2 := (linked_append pre cyc).mp hl3.1
        have hcyc_cs : ∀ c ∈ cyc, c ∈ cs := fun c hc => hcs c (by simp [hc])
        have hperm := perm_of_closed hl2.2.1 ha hb hab
        split
        · rename_i hneg
          exact ⟨cyc, rfl, hcyc_cs, hperm, hneg⟩
        · rename_i hnn
          have hcne : cyc ≠ [] := by rintro rfl; cases ha
          have hcl : 0 < cyc.length := List.length_pos_iff.mpr hcne
          -- the walk with the cycle cut out
          have hl' : Linked (pre ++ post) := by
            refine (linked_append pre post).mpr ⟨hl2.1, hl3.2.1, ?_⟩
            intro x y hx hy
            have h1 := hl2.2.2 x a hx ha
            have h2 := hl3.2.2 b y (by rw [List.getLast?_append, hb]; rfl) hy
            rw [h1, ← hab, h2]
          have hcs' : ∀ e ∈ pre ++ post, e ∈ cs := fun e he => hcs e (by
            rcases List.mem_append.mp he with h | h <;> simp [h])
          have hend' : EndsAt v (pre ++ post) := by
            intro e he
            cases hpre : pre with
            | cons p ps =>
                rw [hpre] at he
                simp at he; subst he
                exact hend _ (by simp [hpre])
            | nil =>
                rw [hpre] at he
                have h2 := hl3.2.2 b e (by rw [List.getLast?_append, hb]; rfl) he
                have h0 := hend a (by simp [hpre, ha])
                rw [← h2, hab, h0]
          have hw' : weight (pre ++ post) < B := by
            have := weight_append (pre ++ cyc) post
            have := weight_append pre cyc
            have := weight_append pre post
            simp only [weight] at *
            omega
          have hlen' : (pre ++ post).length < f := by
            simp only [List.length_append] at hlen ⊢
            omega
          exact findNeg_finds cs vs hvs v B hB f (pre ++ post) hlen' hl' hcs' hend' hw'

/-! ## §3. The table -/

theorem look_set_ne (t : Table) (v u : Node) (e : Int × List Con) (h : u ≠ v) :
    (t.set v e).look u = t.look u := by
  induction t with
  | nil => rfl
  | cons p t ih =>
      simp only [Table.set, Table.look]
      by_cases hp : p.1 = v
      · simp only [hp, if_true, Ne.symm h, if_false, ih]
      · simp only [hp, if_false, ih]

theorem look_set_self (t : Table) (v : Node) (e : Int × List Con) :
    (t.set v e).look v = e ∨ (t.set v e).look v = t.look v := by
  induction t with
  | nil => exact .inr rfl
  | cons p t ih =>
      simp only [Table.set, Table.look]
      by_cases hp : p.1 = v
      · simp [hp]
      · simp only [hp, if_false]
        exact ih

theorem look_set_mem (t : Table) (v : Node) (e : Int × List Con) (h : v ∈ t.map Prod.fst) :
    (t.set v e).look v = e := by
  induction t with
  | nil => cases h
  | cons p t ih =>
      simp only [Table.set, Table.look]
      by_cases hp : p.1 = v
      · simp [hp]
      · simp only [hp, if_false]
        simp only [List.map_cons, List.mem_cons] at h
        exact ih (h.resolve_left (Ne.symm hp))

theorem keys_set (t : Table) (v : Node) (e : Int × List Con) :
    (t.set v e).map Prod.fst = t.map Prod.fst := by
  induction t with
  | nil => rfl
  | cons p t ih =>
      simp only [Table.set, List.map_cons, ih]
      by_cases hp : p.1 = v <;> simp [hp]

theorem keys_relax (t : Table) (c : Con) : (relax t c).map Prod.fst = t.map Prod.fst := by
  simp only [relax]; split
  · exact keys_set ..
  · rfl

theorem relax_le (t : Table) (c : Con) (u : Node) : ((relax t c).look u).1 ≤ (t.look u).1 := by
  simp only [relax]
  split
  · rename_i hlt
    by_cases hu : u = c.x
    · subst hu
      rcases look_set_self t c.x ((t.look c.y).1 + c.k, c :: (t.look c.y).2) with h | h
      · rw [h]; dsimp only; omega
      · rw [h]
    · rw [look_set_ne t c.x u _ hu]
  · exact Int.le_refl _

theorem relax_edge (t : Table) (c : Con) (hx : c.x ∈ t.map Prod.fst) :
    ((relax t c).look c.x).1 ≤ (t.look c.y).1 + c.k := by
  simp only [relax]
  split
  · rw [look_set_mem t c.x _ hx]
  · omega

/-- Every distance is the weight of a walk of the system's constraints that ends at its node. -/
def Inv (cs : List Con) (t : Table) : Prop :=
  ∀ v, (t.look v).1 = weight (t.look v).2 ∧ Linked (t.look v).2 ∧
    (∀ e ∈ (t.look v).2, e ∈ cs) ∧ EndsAt v (t.look v).2

theorem relax_inv (cs : List Con) (t : Table) (c : Con) (hc : c ∈ cs) (h : Inv cs t) :
    Inv cs (relax t c) := by
  intro u
  simp only [relax]
  split
  · by_cases hu : u = c.x
    · subst hu
      obtain ⟨hw, hl, hcs, he⟩ := h c.y
      rcases look_set_self t c.x ((t.look c.y).1 + c.k, c :: (t.look c.y).2) with h' | h'
      · rw [h']
        refine ⟨?_, linked_cons hl he, ?_, fun e he' => by cases he'; rfl⟩
        · simp only [weight_cons]; omega
        · intro e he'
          rcases List.mem_cons.mp he' with rfl | he'
          · exact hc
          · exact hcs e he'
      · rw [h']; exact h c.x
    · rw [look_set_ne t c.x u _ hu]; exact h u
  · exact h u

theorem foldl_keys (t : Table) : ∀ L : List Con, (L.foldl relax t).map Prod.fst = t.map Prod.fst := by
  intro L
  induction L generalizing t with
  | nil => rfl
  | cons c L ih => rw [List.foldl_cons, ih, keys_relax]

theorem foldl_le (u : Node) : ∀ (L : List Con) (t : Table), ((L.foldl relax t).look u).1 ≤ (t.look u).1
  | [], _ => Int.le_refl _
  | c :: L, t => by
      rw [List.foldl_cons]
      exact Int.le_trans (foldl_le u L (relax t c)) (relax_le t c u)

theorem foldl_inv (cs : List Con) :
    ∀ (L : List Con) (t : Table), (∀ c ∈ L, c ∈ cs) → Inv cs t → Inv cs (L.foldl relax t)
  | [], _, _, h => h
  | c :: L, t, hL, h => by
      rw [List.foldl_cons]
      exact foldl_inv cs L _ (fun c' hc' => hL c' (List.mem_cons_of_mem _ hc'))
        (relax_inv cs t c (hL c (List.mem_cons_self ..)) h)

theorem foldl_edge (e : Con) :
    ∀ (L : List Con) (t : Table), e ∈ L → e.x ∈ t.map Prod.fst →
      ((L.foldl relax t).look e.x).1 ≤ (t.look e.y).1 + e.k
  | [], _, h, _ => by cases h
  | c :: L, t, h, hx => by
      rw [List.foldl_cons]
      by_cases hec : e = c
      · subst hec
        have := relax_edge t e hx
        have := foldl_le e.x L (relax t e)
        omega
      · have hm : e ∈ L := (List.mem_cons.mp h).resolve_left hec
        have := foldl_edge e L (relax t c) hm (by rw [keys_relax]; exact hx)
        have := relax_le t c e.y
        omega

theorem rounds_succ (cs : List Con) :
    ∀ (i : Nat) (t : Table), rounds cs (i + 1) t = cs.foldl relax (rounds cs i t)
  | 0, _ => rfl
  | i + 1, t => by
      show rounds cs (i + 1) (cs.foldl relax t) = _
      rw [rounds_succ cs i]
      rfl

theorem rounds_keys (cs : List Con) (t : Table) :
    ∀ i, (rounds cs i t).map Prod.fst = t.map Prod.fst
  | 0 => rfl
  | i + 1 => by rw [rounds_succ, foldl_keys, rounds_keys cs t i]

theorem rounds_le (cs : List Con) (t : Table) (u : Node) :
    ∀ i, ((rounds cs i t).look u).1 ≤ (t.look u).1
  | 0 => Int.le_refl _
  | i + 1 => by
      rw [rounds_succ]
      exact Int.le_trans (foldl_le u _ _) (rounds_le cs t u i)

theorem rounds_inv (cs : List Con) (t : Table) (h : Inv cs t) : ∀ i, Inv cs (rounds cs i t)
  | 0 => h
  | i + 1 => by
      rw [rounds_succ]
      exact foldl_inv cs cs _ (fun c hc => hc) (rounds_inv cs t h i)

/-- **`rounds_bound`** — after `i` rounds a node's distance is at most the weight of every walk
of at most `i` constraints ending at it. -/
theorem rounds_bound (cs : List Con) (t : Table) (hk : ∀ c ∈ cs, c.x ∈ t.map Prod.fst)
    (hpos : ∀ v, (t.look v).1 ≤ 0) :
    ∀ (i : Nat) (v : Node) (W : List Con), Linked W → (∀ e ∈ W, e ∈ cs) → EndsAt v W →
      W.length ≤ i → ((rounds cs i t).look v).1 ≤ weight W
  | i, v, [], _, _, _, _ => by
      have := rounds_le cs t v i
      have := hpos v
      simp only [weight, List.map_nil, List.sum_nil]
      omega
  | 0, _, _ :: _, _, _, _, hlen => by simp at hlen
  | i + 1, v, e :: W, hl, hcs, hend, hlen => by
      have hev : e.x = v := hend e rfl
      subst hev
      have ih := rounds_bound cs t hk hpos i e.y W (linked_tail hl)
        (fun e' he' => hcs e' (List.mem_cons_of_mem _ he')) (linked_tail_ends hl)
        (by simp at hlen; omega)
      rw [rounds_succ]
      have := foldl_edge e cs (rounds cs i t) (hcs e (List.mem_cons_self ..))
        (by rw [rounds_keys]; exact hk e (hcs e (List.mem_cons_self ..)))
      rw [weight_cons]
      omega

/-! ## §4. One system: a potential or a certificate -/

/-- Constrained nodes are required present (or are `zero`), and `zero` is never required absent. -/
def Sys.WF (s : Sys) : Prop :=
  (∀ c ∈ s.cons, (c.x = .zero ∨ c.x ∈ s.present) ∧ (c.y = .zero ∨ c.y ∈ s.present)) ∧
    Node.zero ∉ s.absent

theorem mem_foldl_dedup (v : Node) :
    ∀ (l acc : List Node),
      v ∈ l.foldl (fun acc w => if acc.contains w then acc else acc ++ [w]) acc ↔ v ∈ acc ∨ v ∈ l
  | [], acc => by simp
  | w :: l, acc => by
      rw [List.foldl_cons, mem_foldl_dedup v l]
      by_cases hw : acc.contains w = true
      · have hwm : w ∈ acc := List.contains_iff_mem.mp hw
        simp only [hw, if_true, List.mem_cons]
        constructor
        · rintro (h | h)
          · exact .inl h
          · exact .inr (.inr h)
        · rintro (h | h | h)
          · exact .inl h
          · exact .inl (h ▸ hwm)
          · exact .inr h
      · simp only [hw, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons,
          List.mem_nil_iff, or_false]
        exact or_assoc

theorem mem_nodes (s : Sys) (v : Node) :
    v ∈ s.nodes ↔ v = .zero ∨ v ∈ s.present ∨ ∃ c ∈ s.cons, v = c.x ∨ v = c.y := by
  simp only [Sys.nodes, dedupNodes, mem_foldl_dedup, List.not_mem_nil, false_or, List.mem_cons,
    List.mem_append, List.mem_flatMap, List.mem_singleton, List.mem_nil_iff, or_false, or_assoc]

theorem cons_x_mem_nodes (s : Sys) (c : Con) (hc : c ∈ s.cons) : c.x ∈ s.nodes :=
  (mem_nodes s c.x).mpr (.inr (.inr ⟨c, hc, .inl rfl⟩))

theorem cons_y_mem_nodes (s : Sys) (c : Con) (hc : c ∈ s.cons) : c.y ∈ s.nodes :=
  (mem_nodes s c.y).mpr (.inr (.inr ⟨c, hc, .inr rfl⟩))

/-- The initial table: every node at distance `0`. -/
def table0 (vs : List Node) : Table := vs.map fun v => (v, 0, [])

theorem keys_table0 (vs : List Node) : (table0 vs).map Prod.fst = vs := by
  simp [table0, List.map_map, Function.comp_def]

theorem look_table0 (vs : List Node) (v : Node) : (table0 vs).look v = (0, []) := by
  induction vs with
  | nil => rfl
  | cons w vs ih =>
      simp only [table0, List.map_cons, Table.look] at ih ⊢
      split <;> simp [ih]

theorem inv_table0 (cs : List Con) (vs : List Node) : Inv cs (table0 vs) := by
  intro v
  rw [look_table0]
  exact ⟨rfl, trivial, by simp, by simp [EndsAt]⟩

theorem get_cons (a : Slot) (x : Int) (l : List (Slot × Int)) (k : Slot) :
    State.get ⟨(a, x) :: l⟩ k = if a = k then some x else State.get ⟨l⟩ k := by
  simp only [State.get, List.find?_cons]
  by_cases h : a = k
  · simp [h]
  · have : (a == k) = false := by simpa using h
    simp only [this, h, if_false]

theorem get_built_old (val : Node → Int) (sl : Slot) :
    ∀ vs : List Node, (stateOf Node.oldSlot val vs).get sl =
      if Node.old sl ∈ vs then some (val (.old sl)) else none
  | [] => rfl
  | v :: vs => by
      have ih := get_built_old val sl vs
      cases v with
      | zero => simpa [stateOf, Node.oldSlot] using ih
      | new s' => simpa [stateOf, Node.oldSlot] using ih
      | old s' =>
          have : stateOf Node.oldSlot val (Node.old s' :: vs) =
              ⟨(s', val (.old s')) :: (stateOf Node.oldSlot val vs).slots⟩ := rfl
          rw [this, get_cons]
          by_cases h : s' = sl
          · subst h; simp
          · simp only [h, if_false, List.mem_cons, Node.old.injEq, Ne.symm h, false_or]
            exact ih

theorem get_built_new (val : Node → Int) (sl : Slot) :
    ∀ vs : List Node, (stateOf Node.newSlot val vs).get sl =
      if Node.new sl ∈ vs then some (val (.new sl)) else none
  | [] => rfl
  | v :: vs => by
      have ih := get_built_new val sl vs
      cases v with
      | zero => simpa [stateOf, Node.newSlot] using ih
      | old s' => simpa [stateOf, Node.newSlot] using ih
      | new s' =>
          have : stateOf Node.newSlot val (Node.new s' :: vs) =
              ⟨(s', val (.new s')) :: (stateOf Node.newSlot val vs).slots⟩ := rfl
          rw [this, get_cons]
          by_cases h : s' = sl
          · subst h; simp
          · simp only [h, if_false, List.mem_cons, Node.new.injEq, Ne.symm h, false_or]
            exact ih

/-- The step built from a potential reads every listed node at its potential, and nothing else. -/
theorem read_built (val : Node → Int) (h0 : val .zero = 0) (vs : List Node) (v : Node) :
    v.read (stateOf Node.oldSlot val vs) (stateOf Node.newSlot val vs) =
      if v = .zero ∨ v ∈ vs then some (val v) else none := by
  cases v with
  | zero => simp [Node.read, h0]
  | old sl => rw [Node.read, get_built_old]; simp
  | new sl => rw [Node.read, get_built_new]; simp

/-- **`solve_total`** — a well-formed system gets a certificate the checker accepts, or a step
that satisfies it. -/
theorem solve_total (s : Sys) (hwf : s.WF) :
    (∃ c, s.solve = .cert c ∧ c.check s = true) ∨ (∃ o n, s.solve = .sat o n ∧ s.Holds o n) := by
  unfold Sys.solve
  split
  · rename_i v hv
    refine .inl ⟨.clash v, rfl, ?_⟩
    simp only [SysCert.check, Bool.and_eq_true, List.contains_iff_mem]
    exact ⟨List.mem_of_find?_eq_some hv, List.contains_iff_mem.mp (List.find?_some hv)⟩
  · rename_i hclash
    have hnc : ∀ v ∈ s.present, v ∉ s.absent := fun v hv ha =>
      List.find?_eq_none.mp hclash v hv (List.contains_iff_mem.mpr ha)
    have ht0 : (s.nodes.map fun v => ((v, 0, []) : Node × Int × List Con)) = table0 s.nodes := rfl
    simp only [ht0]
    generalize ht : rounds s.cons s.nodes.length (table0 s.nodes) = t
    have hinv : Inv s.cons t := ht ▸ rounds_inv s.cons _ (inv_table0 s.cons s.nodes) _
    have hbound := ht ▸ rounds_bound s.cons (table0 s.nodes)
      (fun c hc => by rw [keys_table0]; exact cons_x_mem_nodes s c hc)
      (fun v => by rw [look_table0]) s.nodes.length
    split
    · rename_i hok
      refine .inr ⟨_, _, rfl, ?_⟩
      have hval : ∀ v, (v = .zero ∨ v ∈ s.nodes) →
          Node.val (stateOf Node.oldSlot (fun v => (t.look v).1 - (t.look .zero).1) s.nodes)
            (stateOf Node.newSlot (fun v => (t.look v).1 - (t.look .zero).1) s.nodes) v =
            (t.look v).1 - (t.look .zero).1 := by
        intro v hv
        simp only [Node.val]
        rw [read_built _ (by simp) s.nodes v, if_pos hv] <;> rfl
      refine ⟨fun v hv => ?_, fun v hv => ?_, fun c hc => ?_⟩
      · rw [read_built _ (by simp) s.nodes v, if_pos (.inr ((mem_nodes s v).mpr (.inr (.inl hv))))] <;> rfl
      · rw [read_built _ (by simp) s.nodes v, if_neg]
        rintro (rfl | hm)
        · exact hwf.2 hv
        · rcases (mem_nodes s v).mp hm with rfl | hp | ⟨c, hc, rfl | rfl⟩
          · exact hwf.2 hv
          · exact hnc v hp hv
          · rcases (hwf.1 c hc).1 with h | h
            · exact hwf.2 (h ▸ hv)
            · exact hnc _ h hv
          · rcases (hwf.1 c hc).2 with h | h
            · exact hwf.2 (h ▸ hv)
            · exact hnc _ h hv
      · have hc' := List.find?_eq_none.mp hok c hc
        simp only [Bool.not_eq_true', decide_eq_false_iff_not, Classical.not_not] at hc'
        simp only [Con.Holds]
        rw [hval c.x (.inr (cons_x_mem_nodes s c hc)), hval c.y (.inr (cons_y_mem_nodes s c hc))]
        omega
    · rename_i c hc
      have hcm := List.mem_of_find?_eq_some hc
      have hviol := List.find?_some hc
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hviol
      obtain ⟨hw, hl, hcs, he⟩ := hinv c.y
      obtain ⟨cyc, hf, hsub, hperm, hneg⟩ := findNeg_finds s.cons s.nodes
        (fun c hc => cons_x_mem_nodes s c hc) c.x (t.look c.x).1
        (fun W hl hcs he hlen => hbound c.x W hl hcs he hlen)
        ((c :: (t.look c.y).2).length + 1) (c :: (t.look c.y).2) (Nat.lt_succ_self _)
        (linked_cons hl he)
        (fun e he' => by
          rcases List.mem_cons.mp he' with rfl | he'
          · exact hcm
          · exact hcs e he')
        (fun e he' => by cases he'; rfl)
        (by rw [weight_cons, ← hw]; omega)
      refine .inl ⟨.cycle cyc, by simp only [hf], ?_⟩
      simp only [SysCert.check, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
        List.isPerm_iff, decide_eq_true_eq]
      exact ⟨⟨hsub, hperm⟩, hneg⟩

/-! ## §5. Each system implies the law; each system is well formed -/

section Sound
variable {o n : State}

/-- The simp set that turns a concrete atom system's `Holds` into arithmetic on the reads. -/
macro "back_simp" : tactic => `(tactic| simp_all [evalWith, Sys.merge, Sys.Holds, Sys.pres,
  Sys.gone, Con.Holds, Con.upper, Con.lower, Node.val, Node.read])

theorem memT_sound {s : Slot} {xs : List Int} {t : Sys} (ht : t ∈ Atom.memT s xs)
    (hh : t.Holds o n) : evalWith failClosed (.memberOf s xs) o n = true := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
  obtain ⟨hp, _, hc⟩ := hh
  have hpres := hp (.new s) (by simp [Sys.pres])
  have h1 := hc _ (by simp [Sys.pres] : Con.upper (.new s) x ∈ (Sys.pres _ _).cons)
  have h2 := hc _ (by simp [Sys.pres] : Con.lower (.new s) x ∈ (Sys.pres _ _).cons)
  cases hg : n.get s with
  | none => simp [Node.read, hg] at hpres
  | some v =>
      simp only [Con.Holds, Con.upper, Con.lower, Node.val, Node.read, hg] at h1 h2
      simp only [Option.getD_some] at h1 h2
      have : v = x := by omega
      subst this
      simp [evalWith, hg, List.contains_iff_mem, hx]

theorem memF_sound {s : Slot} {xs : List Int} {t : Sys} (ht : t ∈ Atom.memF s xs)
    (hh : t.Holds o n) : evalWith failClosed (.memberOf s xs) o n = false := by
  simp only [Atom.memF, List.mem_cons, List.mem_map] at ht
  rcases ht with h1 | h2 | ⟨x, hx, h3⟩
  · subst h1
    have := hh.2.1 (.new s) (by simp [Sys.gone])
    simp only [Node.read] at this
    simp [evalWith, this]
  · subst h2
    obtain ⟨hp, _, hc⟩ := hh
    have hpres := hp (.new s) (by simp [Sys.pres])
    cases hg : n.get s with
    | none => simp [Node.read, hg] at hpres
    | some v =>
        simp only [evalWith, hg]
        cases hm : xs.contains v with
        | false => rfl
        | true =>
            have hv := List.contains_iff_mem.mp hm
            have := hc _ (by simp only [Sys.pres]; exact List.mem_map.mpr ⟨v, hv, rfl⟩)
            simp [Con.Holds, Con.upper, Node.val, Node.read, hg] at this
  · subst h3
    obtain ⟨hp, _, hc⟩ := hh
    have hpres := hp (.new s) (by simp [Sys.pres])
    cases hg : n.get s with
    | none => simp [Node.read, hg] at hpres
    | some v =>
        simp only [evalWith, hg]
        cases hm : xs.contains v with
        | false => rfl
        | true =>
            have hv := List.contains_iff_mem.mp hm
            have hlo := hc _ (by simp [Sys.pres] : Con.lower (.new s) (x + 1) ∈ (Sys.pres _ _).cons)
            simp [Con.Holds, Con.lower, Node.val, Node.read, hg] at hlo
            have hup := hc (Con.upper (.new s) (v - 1)) (by
              simp only [Sys.pres, List.mem_cons, List.mem_map, List.mem_filter, decide_eq_true_eq]
              exact .inr ⟨v, ⟨hv, by omega⟩, rfl⟩)
            simp [Con.Holds, Con.upper, Node.val, Node.read, hg] at hup

theorem atom_sound (b : Bool) (p : Pred) (l : List Sys) (h : atomDnf b p = some l) :
    ∀ t ∈ l, t.Holds o n → evalWith failClosed p o n = b := by
  cases p with
  | memberOf s xs =>
      simp only [atomDnf, Option.some.injEq] at h; subst h
      cases b
      · exact fun t ht hh => memF_sound ht hh
      · exact fun t ht hh => memT_sound ht hh
  | eq s v | le s v =>
      simp only [atomDnf, Option.some.injEq] at h; subst h
      cases b <;> simp only [Bool.false_eq_true, if_false, if_true, Atom.eqT, Atom.eqF, Atom.leT,
        Atom.leF, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] <;>
        and_intros <;> intro hh <;> cases hg : n.get s <;> back_simp <;> omega
  | writeOnce s | monotone s =>
      simp only [atomDnf, Option.some.injEq] at h; subst h
      cases b <;> simp only [Bool.false_eq_true, if_false, if_true, Atom.woT, Atom.woF, Atom.monoT,
        Atom.monoF, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.mem_nil_iff,
        or_false, forall_eq_or_imp, forall_eq] <;>
        and_intros <;> intro hh <;> cases ho : o.get s <;> cases hg : n.get s <;> back_simp <;> omega
  | eqSlots x y | leSlots x y =>
      simp only [atomDnf, Option.some.injEq] at h; subst h
      cases b <;> simp only [Bool.false_eq_true, if_false, if_true, Atom.eqsT, Atom.eqsF, Atom.offT,
        Atom.offF, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] <;>
        and_intros <;> intro hh <;> cases hx : n.get x <;> cases hy : n.get y <;> back_simp <;> omega
  | leSlotsOff x y k =>
      simp only [atomDnf, Option.some.injEq] at h; subst h
      cases b <;> simp only [Bool.false_eq_true, if_false, if_true, Atom.offT,
        Atom.offF, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] <;>
        and_intros <;> intro hh <;> cases hx : n.get x <;> cases hy : n.get y <;> back_simp <;> omega
  | witnessed _ | hashEq _ _ _ | ran _ | not _ | allL _ | anyL _ => simp [atomDnf] at h

theorem mem_capped {cap : Nat} {l ss : List Sys} (h : capped cap l = some ss) {t : Sys}
    (ht : t ∈ ss) : t ∈ l := by
  unfold capped at h; split at h <;> cases h; exact ht

theorem mem_product {cap : Nat} {a b ss : List Sys} (h : product cap a b = some ss) {t : Sys}
    (ht : t ∈ ss) : ∃ t₁ ∈ a, ∃ t₂ ∈ b, t = t₁.merge t₂ := by
  have := mem_capped h ht
  obtain ⟨t₁, h₁, h₂⟩ := List.mem_flatMap.mp this
  obtain ⟨t₂, h₃, h₄⟩ := List.mem_map.mp h₂
  exact ⟨t₁, h₁, t₂, h₃, h₄.symm⟩

theorem mem_union {cap : Nat} {a b ss : List Sys} (h : union cap a b = some ss) {t : Sys}
    (ht : t ∈ ss) : t ∈ a ∨ t ∈ b :=
  List.mem_append.mp (mem_capped h ht)

theorem evalAll_of_allAre (ps : PredList) (h : AllAre true o n ps) :
    evalWithAll failClosed ps o n = true := by
  induction ps using PredList.rec' with
  | nil => rfl
  | cons q rest ih => simp only [evalWithAll, Bool.and_eq_true]; exact ⟨h.1, ih h.2⟩

theorem evalAny_of_allAre (ps : PredList) (h : AllAre false o n ps) :
    evalWithAny failClosed ps o n = false := by
  induction ps using PredList.rec' with
  | nil => rfl
  | cons q rest ih => simp only [evalWithAny, Bool.or_eq_false_iff]; exact ⟨h.1, ih h.2⟩

theorem evalAny_of_someIs (ps : PredList) (h : SomeIs true o n ps) :
    evalWithAny failClosed ps o n = true := by
  induction ps using PredList.rec' with
  | nil => exact h.elim
  | cons q rest ih =>
      simp only [evalWithAny, Bool.or_eq_true]
      exact h.elim .inl fun h => .inr (ih h)

theorem evalAll_of_someIs (ps : PredList) (h : SomeIs false o n ps) :
    evalWithAll failClosed ps o n = false := by
  induction ps using PredList.rec' with
  | nil => exact h.elim
  | cons q rest ih =>
      simp only [evalWithAll, Bool.and_eq_false_iff]
      exact h.elim .inl fun h => .inr (ih h)

mutual
/-- **`dnf_sound`** — the converse of `dnf_covers`: a step satisfying any system of `dnf b p`
evaluates `p` to `b`. -/
theorem dnf_sound (cap : Nat) :
    (b : Bool) → (p : Pred) → (ss : List Sys) → dnf cap b p = some ss →
      ∀ t ∈ ss, t.Holds o n → evalWith failClosed p o n = b
  | b, .not q, ss, h, t, ht, hh => by
      simp only [dnf] at h
      simp only [evalWith, dnf_sound cap (!b) q ss h t ht hh, Bool.not_not]
  | b, .allL ps, ss, h, t, ht, hh => by
      simp only [dnf] at h
      simp only [evalWith]
      cases b with
      | true => exact evalAll_of_allAre ps (dnfAnd_sound cap true ps ss h t ht hh)
      | false => exact evalAll_of_someIs ps (dnfOr_sound cap false ps ss h t ht hh)
  | b, .anyL ps, ss, h, t, ht, hh => by
      simp only [dnf] at h
      simp only [evalWith]
      cases b with
      | true => exact evalAny_of_someIs ps (dnfOr_sound cap true ps ss h t ht hh)
      | false => exact evalAny_of_allAre ps (dnfAnd_sound cap false ps ss h t ht hh)
  | b, .eq s v, ss, h, t, ht, hh | b, .le s v, ss, h, t, ht, hh
  | b, .memberOf s v, ss, h, t, ht, hh | b, .eqSlots s v, ss, h, t, ht, hh
  | b, .leSlots s v, ss, h, t, ht, hh => by
      simp only [dnf, Option.bind_eq_some_iff] at h
      obtain ⟨l, hl, hc⟩ := h
      exact atom_sound b _ l hl t (mem_capped hc ht) hh
  | b, .writeOnce s, ss, h, t, ht, hh | b, .monotone s, ss, h, t, ht, hh => by
      simp only [dnf, Option.bind_eq_some_iff] at h
      obtain ⟨l, hl, hc⟩ := h
      exact atom_sound b _ l hl t (mem_capped hc ht) hh
  | b, .leSlotsOff x y k, ss, h, t, ht, hh => by
      simp only [dnf, Option.bind_eq_some_iff] at h
      obtain ⟨l, hl, hc⟩ := h
      exact atom_sound b _ l hl t (mem_capped hc ht) hh
  | _, .witnessed _, _, h, _, _, _ | _, .hashEq _ _ _, _, h, _, _, _ | _, .ran _, _, h, _, _, _ => by
      simp [dnf] at h
theorem dnfAnd_sound (cap : Nat) :
    (b : Bool) → (ps : PredList) → (ss : List Sys) → dnfAnd cap b ps = some ss →
      ∀ t ∈ ss, t.Holds o n → AllAre b o n ps
  | _, .nil, _, _, _, _, _ => trivial
  | b, .cons q rest, ss, h, t, ht, hh => by
      simp only [dnfAnd] at h
      split at h
      · rename_i a r ha hr
        obtain ⟨t₁, h₁, t₂, h₂, rfl⟩ := mem_product h ht
        obtain ⟨k₁, k₂⟩ := Sys.holds_merge.mp hh
        exact ⟨dnf_sound cap b q a ha t₁ h₁ k₁, dnfAnd_sound cap b rest r hr t₂ h₂ k₂⟩
      · cases h
theorem dnfOr_sound (cap : Nat) :
    (b : Bool) → (ps : PredList) → (ss : List Sys) → dnfOr cap b ps = some ss →
      ∀ t ∈ ss, t.Holds o n → SomeIs b o n ps
  | _, .nil, ss, h, t, ht, _ => by
      simp only [dnfOr, Option.some.injEq] at h; subst h; cases ht
  | b, .cons q rest, ss, h, t, ht, hh => by
      simp only [dnfOr] at h
      split at h
      · rename_i a r ha hr
        rcases mem_union h ht with h₁ | h₂
        · exact .inl (dnf_sound cap b q a ha t h₁ hh)
        · exact .inr (dnfOr_sound cap b rest r hr t h₂ hh)
      · cases h
end

end Sound

theorem wf_merge {a b : Sys} (ha : a.WF) (hb : b.WF) : (a.merge b).WF := by
  refine ⟨fun c hc => ?_, ?_⟩
  · simp only [Sys.merge, List.mem_append] at hc ⊢
    rcases hc with hc | hc
    · obtain ⟨h1, h2⟩ := ha.1 c hc
      exact ⟨h1.imp_right .inl, h2.imp_right .inl⟩
    · obtain ⟨h1, h2⟩ := hb.1 c hc
      exact ⟨h1.imp_right .inr, h2.imp_right .inr⟩
  · simp only [Sys.merge, List.mem_append, not_or]
    exact ⟨ha.2, hb.2⟩

theorem atom_wf (b : Bool) (p : Pred) (l : List Sys) (h : atomDnf b p = some l) :
    ∀ t ∈ l, t.WF := by
  cases p with
  | memberOf s xs =>
      simp only [atomDnf, Option.some.injEq] at h; subst h
      cases b
      · intro t ht
        simp only [Bool.false_eq_true, if_false, Atom.memF, List.mem_cons, List.mem_map] at ht
        rcases ht with rfl | rfl | ⟨x, _, rfl⟩
        · simp [Sys.WF, Sys.gone]
        · simp [Sys.WF, Sys.pres, Con.upper]
        · refine ⟨fun c hc => ?_, by simp [Sys.pres]⟩
          simp only [Sys.pres, List.mem_cons, List.mem_map] at hc
          rcases hc with rfl | ⟨y, _, rfl⟩ <;> simp [Con.upper, Con.lower, Sys.pres]
      · intro t ht
        simp only [if_true, Atom.memT] at ht
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht
        simp [Sys.WF, Sys.pres, Con.upper, Con.lower]
  | witnessed _ | hashEq _ _ _ | ran _ | not _ | allL _ | anyL _ => simp [atomDnf] at h
  | _ =>
      simp only [atomDnf, Option.some.injEq] at h; subst h
      cases b <;> simp [Sys.WF, Atom.eqT, Atom.eqF, Atom.leT, Atom.leF, Atom.woT, Atom.woF,
        Atom.monoT, Atom.monoF, Atom.eqsT, Atom.eqsF, Atom.offT, Atom.offF, Sys.merge, Sys.pres,
        Sys.gone, Con.upper, Con.lower]

mutual
theorem dnf_wf (cap : Nat) :
    (b : Bool) → (p : Pred) → (ss : List Sys) → dnf cap b p = some ss → ∀ t ∈ ss, t.WF
  | b, .not q, ss, h => by
      simp only [dnf] at h
      exact dnf_wf cap (!b) q ss h
  | b, .allL ps, ss, h => by
      simp only [dnf] at h
      cases b with
      | true => exact dnfAnd_wf cap true ps ss h
      | false => exact dnfOr_wf cap false ps ss h
  | b, .anyL ps, ss, h => by
      simp only [dnf] at h
      cases b with
      | true => exact dnfOr_wf cap true ps ss h
      | false => exact dnfAnd_wf cap false ps ss h
  | b, .eq s v, ss, h | b, .le s v, ss, h | b, .memberOf s v, ss, h | b, .eqSlots s v, ss, h
  | b, .leSlots s v, ss, h => by
      simp only [dnf, Option.bind_eq_some_iff] at h
      obtain ⟨l, hl, hc⟩ := h
      exact fun t ht => atom_wf b _ l hl t (mem_capped hc ht)
  | b, .writeOnce s, ss, h | b, .monotone s, ss, h => by
      simp only [dnf, Option.bind_eq_some_iff] at h
      obtain ⟨l, hl, hc⟩ := h
      exact fun t ht => atom_wf b _ l hl t (mem_capped hc ht)
  | b, .leSlotsOff x y k, ss, h => by
      simp only [dnf, Option.bind_eq_some_iff] at h
      obtain ⟨l, hl, hc⟩ := h
      exact fun t ht => atom_wf b _ l hl t (mem_capped hc ht)
  | _, .witnessed _, _, h | _, .hashEq _ _ _, _, h | _, .ran _, _, h => by simp [dnf] at h
theorem dnfAnd_wf (cap : Nat) :
    (b : Bool) → (ps : PredList) → (ss : List Sys) → dnfAnd cap b ps = some ss → ∀ t ∈ ss, t.WF
  | _, .nil, ss, h => by
      simp only [dnfAnd, Option.some.injEq] at h; subst h
      intro t ht
      simp only [List.mem_singleton] at ht; subst ht
      simp [Sys.WF, Sys.top]
  | b, .cons q rest, ss, h => by
      simp only [dnfAnd] at h
      split at h
      · rename_i a r ha hr
        intro t ht
        obtain ⟨t₁, h₁, t₂, h₂, rfl⟩ := mem_product h ht
        exact wf_merge (dnf_wf cap b q a ha t₁ h₁) (dnfAnd_wf cap b rest r hr t₂ h₂)
      · cases h
theorem dnfOr_wf (cap : Nat) :
    (b : Bool) → (ps : PredList) → (ss : List Sys) → dnfOr cap b ps = some ss → ∀ t ∈ ss, t.WF
  | _, .nil, ss, h => by
      simp only [dnfOr, Option.some.injEq] at h; subst h
      intro t ht; cases ht
  | b, .cons q rest, ss, h => by
      simp only [dnfOr] at h
      split at h
      · rename_i a r ha hr
        intro t ht
        rcases mem_union h ht with h₁ | h₂
        · exact dnf_wf cap b q a ha t h₁
        · exact dnfOr_wf cap b rest r hr t h₂
      · cases h
end

/-! ## §6. Totality -/

theorem certs_of_no_witness (p : Pred) :
    ∀ ss : List Sys,
      (∀ t ∈ ss, (∃ c, t.solve = .cert c ∧ c.check t = true) ∨
        (∃ o n, t.solve = .sat o n ∧ eval p o n = true)) →
      firstWitness p ss = none → ∃ cs, certsOf ss = some cs ∧ checkAll ss cs = true
  | [], _, _ => ⟨[], rfl, rfl⟩
  | t :: ss, h, hw => by
      simp only [firstWitness] at hw
      rcases h t (List.mem_cons_self ..) with ⟨c, hc, hck⟩ | ⟨o, n, hs, he⟩
      · rw [hc] at hw
        obtain ⟨cs, hcs, hall⟩ :=
          certs_of_no_witness p ss (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')) hw
        refine ⟨c :: cs, ?_, ?_⟩
        · simp only [certsOf, hc, hcs]
        · simp only [checkAll, hck, hall, Bool.and_self]
      · simp [hs, he] at hw

/-- **`decide_never_unknown`** — on every law `Pred.difference?` translates, `decide` returns
a witness or a certificate. -/
theorem decide_never_unknown {p : Pred} {d : DiffProblem} (hd : p.difference? = some d) :
    d.decide ≠ .unknown := by
  simp only [Pred.difference?, Option.map_eq_some_iff] at hd
  obtain ⟨ss, hss, rfl⟩ := hd
  have hsys : ∀ t ∈ ss, (∃ c, t.solve = .cert c ∧ c.check t = true) ∨
      (∃ o n, t.solve = .sat o n ∧ eval p o n = true) := by
    intro t ht
    rcases solve_total t (dnf_wf dnfCap true p ss hss t ht) with h | ⟨o, n, hs, hh⟩
    · exact .inl h
    · exact .inr ⟨o, n, hs, dnf_sound dnfCap true p ss hss t ht hh⟩
  simp only [DiffProblem.decide]
  split
  · intro h; cases h
  · rename_i hw
    obtain ⟨cs, hcs, hall⟩ := certs_of_no_witness p ss hsys hw
    simp only [hcs, hall, if_true]
    intro h; cases h

/-- **`decide_finds_witness`** — a law that admits some step gets a witness. -/
theorem decide_finds_witness {p : Pred} {d : DiffProblem} (hd : p.difference? = some d)
    (hsat : ∃ o n, eval p o n = true) : ∃ o n, d.decide = .witness o n := by
  obtain ⟨o, n, he⟩ := hsat
  cases h : d.decide with
  | witness o' n' => exact ⟨o', n', rfl⟩
  | unsat c => rw [certificate_unsat hd h o n] at he; cases he
  | unknown => exact absurd h (decide_never_unknown hd)

/-- **`decide_unsat_iff`** — `decide` certifies unsatisfiability exactly when the law admits no
step. -/
theorem decide_unsat_iff {p : Pred} {d : DiffProblem} (hd : p.difference? = some d) :
    (∃ c, d.decide = .unsat c) ↔ ∀ o n, eval p o n = false := by
  constructor
  · rintro ⟨c, hc⟩; exact certificate_unsat hd hc
  · intro hno
    cases h : d.decide with
    | witness o n => exact absurd (witness_sound hd h) (by rw [hno o n]; simp)
    | unsat c => exact ⟨c, rfl⟩
    | unknown => exact absurd h (decide_never_unknown hd)

end Minidregg.Pred.Sat

/-- info: 'Minidregg.Pred.Sat.decide_never_unknown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Minidregg.Pred.Sat.decide_never_unknown
/-- info: 'Minidregg.Pred.Sat.decide_finds_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Minidregg.Pred.Sat.decide_finds_witness
/-- info: 'Minidregg.Pred.Sat.decide_unsat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Minidregg.Pred.Sat.decide_unsat_iff
