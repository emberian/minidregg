import Theory.NockCost

/-!
# Theory.NockCost.Summaries — loop summaries: `cost` in O(program), the bound a polynomial

NC-1's `cost` prices a value-indexed loop by unrolling it: the abstract interpreter walks the loop
once per value in the declared range, so pricing forge at a declared maximum `V` is `O(V)` work at
birth (`V = 1000`: seconds; `V = 2⁶⁴`: never). This file proves the two loops forge's compiled
Hoon actually runs ONCE, in closed form, and hands the closed forms to the interpreter as an
oracle (`acostWith`, `OracleSound`), so `costSym` never unrolls them.

The two loop shapes, as they appear in forge's nouns (hoon.hoon at the nockchain pin, compiled by
`hoonc`; read from `forgeProgram`, the stdlib core is axis 1023 of forge's gate):

* **count-up** (`++dec`'s trap, `=+ b=0  |-  ?:  =(a +(b))  b  $(b +(b))`):
  `decTrap = [6 [5 [0 30] [4 0 6]] [0 6] [9 2 [10 [6 [4 0 6]] [0 1]]]]`, run on the trap core
  `[decTrap [b gate]]`: `b` at axis 6, the gate's sample `a` at axis 30, the battery at axis 2.
  `trap_runs`: from `b` with `a = b + 1 + n` it answers `a - 1` in exactly `6 + 10·n` steps.
* **decrement-both** (`++sub`, `?:  =(0 b)  a  $(a (dec a), b (dec b))`): the gate battery
  `subBody` at arm 79 of the stdlib core, sample `[a b]` at axes 12/13, recursing through `dec`
  (arm 2398 of the same core, `decArm`) on both. `sub_runs`: for `b ≤ a` it answers `a - b` in
  exactly `9 + 74·b + 10·a·b` steps.

Constants come from the step poles (`%0`, `%1` one step; `%4` = 2 with its operand; a `%9` slam
is one step plus its core and arm; a dynamic hint is one step plus its clue) and are checked here
by the kernel, not asserted: each count is the induction's own arithmetic over `Runs`.
-/

namespace Minidregg.Theory
namespace NockCost

open Noun Nock

/-! ## Exact runs, one Nock rule at a time

`Runs s f v n` (`Theory.Nock`): `*[s f] = v` in exactly `n` steps at every budget and depth
`≥ n`. These are `step_runs`'s cases with the counts named. -/

theorem runs_congr {s f v v' : Noun} {n m : Nat} (h : Runs s f v n) (hv : v = v') (hn : n = m) :
    Runs s f v' m := hv ▸ hn ▸ h

theorem runs_slot {s v : Noun} {a : Nat} (hax : axis a s = some v) :
    Runs s (cell (atom 0) (atom a)) v 1 := by
  refine Runs.of_succ (n := 0) fun d b _ _ => ?_
  have hp : parse (cell (atom 0) (atom a)) = some (.slot a) := parse_toNoun (.slot a)
  simp only [exec, hp, hax, Nat.sub_zero]

theorem runs_quote (s x : Noun) : Runs s (cell (atom 1) x) x 1 := by
  refine Runs.of_succ (n := 0) fun d b _ _ => ?_
  have hp : parse (cell (atom 1) x) = some (.quote x) := parse_toNoun (.quote x)
  simp only [exec, hp, Nat.sub_zero]

theorem runs_cons {s x y z hv tv : Noun} {k₁ k₂ : Nat} (h₁ : Runs s (cell x y) hv k₁)
    (h₂ : Runs s z tv k₂) : Runs s (cell (cell x y) z) (cell hv tv) (k₁ + k₂ + 1) := by
  refine Runs.of_succ fun d b hb hd => ?_
  have hp : parse (cell (cell x y) z) = some (.cons x y z) := parse_toNoun (.cons x y z)
  simp only [exec, hp, Res.bind, h₁ d b (by omega) (by omega), h₂ d (b - k₁) (by omega) (by omega)]
  congr 1; omega

theorem runs_lus {s x : Noun} {n k : Nat} (h : Runs s x (atom n) k) :
    Runs s (cell (atom 4) x) (atom (n + 1)) (k + 1) := by
  refine Runs.of_succ fun d b hb hd => ?_
  have hp : parse (cell (atom 4) x) = some (.lus x) := parse_toNoun (.lus x)
  simp only [exec, hp, Res.bind, h d b (by omega) (by omega)]

theorem runs_tis {s x y v w : Noun} {k₁ k₂ : Nat} (h₁ : Runs s x v k₁) (h₂ : Runs s y w k₂) :
    Runs s (cell (atom 5) (cell x y)) (loob (decide (v = w))) (k₁ + k₂ + 1) := by
  refine Runs.of_succ fun d b hb hd => ?_
  have hp : parse (cell (atom 5) (cell x y)) = some (.tis x y) := parse_toNoun (.tis x y)
  simp only [exec, hp, Res.bind, h₁ d b (by omega) (by omega), h₂ d (b - k₁) (by omega) (by omega)]
  congr 1; omega

theorem runs_sixYes {s x y z v : Noun} {k₁ k₂ : Nat} (h₁ : Runs s x (atom 0) k₁)
    (h₂ : Runs s y v k₂) : Runs s (cell (atom 6) (cell x (cell y z))) v (k₁ + k₂ + 1) := by
  refine Runs.of_succ fun d b hb hd => ?_
  have hp : parse (cell (atom 6) (cell x (cell y z))) = some (.six x y z) :=
    parse_toNoun (.six x y z)
  simp only [exec, hp, Res.bind, h₁ d b (by omega) (by omega), h₂ d (b - k₁) (by omega) (by omega)]
  congr 1; omega

theorem runs_sixNo {s x y z v : Noun} {k₁ k₂ : Nat} (h₁ : Runs s x (atom 1) k₁)
    (h₂ : Runs s z v k₂) : Runs s (cell (atom 6) (cell x (cell y z))) v (k₁ + k₂ + 1) := by
  refine Runs.of_succ fun d b hb hd => ?_
  have hp : parse (cell (atom 6) (cell x (cell y z))) = some (.six x y z) :=
    parse_toNoun (.six x y z)
  simp only [exec, hp, Res.bind, h₁ d b (by omega) (by omega), h₂ d (b - k₁) (by omega) (by omega)]
  congr 1; omega

theorem runs_seven {s x y s' v : Noun} {k₁ k₂ : Nat} (h₁ : Runs s x s' k₁) (h₂ : Runs s' y v k₂) :
    Runs s (cell (atom 7) (cell x y)) v (k₁ + k₂ + 1) := by
  refine Runs.of_succ fun d b hb hd => ?_
  have hp : parse (cell (atom 7) (cell x y)) = some (.seven x y) := parse_toNoun (.seven x y)
  simp only [exec, hp, Res.bind, h₁ d b (by omega) (by omega), h₂ d (b - k₁) (by omega) (by omega)]
  congr 1; omega

theorem runs_eight {s x y p v : Noun} {k₁ k₂ : Nat} (h₁ : Runs s x p k₁)
    (h₂ : Runs (cell p s) y v k₂) : Runs s (cell (atom 8) (cell x y)) v (k₁ + k₂ + 1) := by
  refine Runs.of_succ fun d b hb hd => ?_
  have hp : parse (cell (atom 8) (cell x y)) = some (.eight x y) := parse_toNoun (.eight x y)
  simp only [exec, hp, Res.bind, h₁ d b (by omega) (by omega), h₂ d (b - k₁) (by omega) (by omega)]
  congr 1; omega

theorem runs_nine {s c core f' v : Noun} {a k₁ k₂ : Nat} (h₁ : Runs s c core k₁)
    (hax : axis a core = some f') (h₂ : Runs core f' v k₂) :
    Runs s (cell (atom 9) (cell (atom a) c)) v (k₁ + k₂ + 1) := by
  refine Runs.of_succ fun d b hb hd => ?_
  have hp : parse (cell (atom 9) (cell (atom a) c)) = some (.nine a c) := parse_toNoun (.nine a c)
  simp only [exec, hp, Res.bind, h₁ d b (by omega) (by omega), hax,
    h₂ d (b - k₁) (by omega) (by omega)]
  congr 1; omega

theorem runs_ten {s c z t p v : Noun} {a k₁ k₂ : Nat} (h₁ : Runs s z t k₁) (h₂ : Runs s c p k₂)
    (he : edit a p t = some v) : Runs s (cell (atom 10) (cell (cell (atom a) c) z)) v (k₁ + k₂ + 1) := by
  refine Runs.of_succ fun d b hb hd => ?_
  have hp : parse (cell (atom 10) (cell (cell (atom a) c) z)) = some (.ten a c z) :=
    parse_toNoun (.ten a c z)
  simp only [exec, hp, Res.bind, h₁ d b (by omega) (by omega), h₂ d (b - k₁) (by omega) (by omega),
    he]
  congr 1; omega

theorem runs_hintD {s c z hv v : Noun} {tag k₁ k₂ : Nat} (h₁ : Runs s c hv k₁) (h₂ : Runs s z v k₂) :
    Runs s (cell (atom 11) (cell (cell (atom tag) c) z)) v (k₁ + k₂ + 1) := by
  refine Runs.of_succ fun d b hb hd => ?_
  have hp : parse (cell (atom 11) (cell (cell (atom tag) c) z)) = some (.hintD tag c z) :=
    parse_toNoun (.hintD tag c z)
  simp only [exec, hp, Res.bind, h₁ d b (by omega) (by omega), h₂ d (b - k₁) (by omega) (by omega)]
  congr 1; omega

theorem crashRuns_slot {s : Noun} {a : Nat} (hax : axis a s = none) :
    CrashRuns s (cell (atom 0) (atom a)) 1 := by
  refine CrashRuns.of_succ (n := 0) fun d b _ _ => ?_
  have hp : parse (cell (atom 0) (atom a)) = some (.slot a) := parse_toNoun (.slot a)
  simp only [exec, hp, hax, Nat.sub_zero]

theorem crashRuns_tisB {s x y : Noun} {k : Nat} (h : CrashRuns s x k) :
    CrashRuns s (cell (atom 5) (cell x y)) (k + 1) := by
  refine CrashRuns.of_succ fun d b hb hd => ?_
  have hp : parse (cell (atom 5) (cell x y)) = some (.tis x y) := parse_toNoun (.tis x y)
  simp only [exec, hp, Res.bind, h d b (by omega) (by omega)]

theorem crashRuns_sixT {s x y z : Noun} {k : Nat} (h : CrashRuns s x k) :
    CrashRuns s (cell (atom 6) (cell x (cell y z))) (k + 1) := by
  refine CrashRuns.of_succ fun d b hb hd => ?_
  have hp : parse (cell (atom 6) (cell x (cell y z))) = some (.six x y z) :=
    parse_toNoun (.six x y z)
  simp only [exec, hp, Res.bind, h d b (by omega) (by omega)]

/-! ## From an exact run to a price -/

/-- An exact run of `n ≤ B` steps is a price `B` for its product's shape. -/
theorem Sound.of_runs {s f v : Noun} {n B : Nat} {o : Shape} (h : Runs s f v n)
    (hv : fits v o = true) (hB : n ≤ B) : Sound B o s f := by
  intro d b
  refine ⟨?_, fun hd hb => by rw [h d b (by omega) (by omega)]; simp⟩
  cases hx : exec d b s f with
  | exhausted => trivial
  | ok v' r =>
    have e := exec_shift d (max d n) (le_max_left _ _) b n s f (by rw [hx]; simp)
    rw [hx, h (max d n) (b + n) (by omega) (le_max_right _ _)] at e
    simp only [Res.shift, Res.ok.injEq] at e
    obtain ⟨rfl, hr⟩ := e
    exact ⟨hv, by omega⟩
  | crash r =>
    have e := exec_shift d (max d n) (le_max_left _ _) b n s f (by rw [hx]; simp)
    rw [hx, h (max d n) (b + n) (by omega) (le_max_right _ _)] at e
    simp [Res.shift] at e

/-- An exact crash after `n ≤ B` steps is a price `B` for any product shape. -/
theorem Sound.of_crashRuns {s f : Noun} {n B : Nat} {o : Shape} (h : CrashRuns s f n)
    (hB : n ≤ B) : Sound B o s f := by
  intro d b
  refine ⟨?_, fun hd hb => by rw [h d b (by omega) (by omega)]; simp⟩
  cases hx : exec d b s f with
  | exhausted => trivial
  | ok v' r =>
    have e := exec_shift d (max d n) (le_max_left _ _) b n s f (by rw [hx]; simp)
    rw [hx, h (max d n) (b + n) (by omega) (le_max_right _ _)] at e
    simp [Res.shift] at e
  | crash r =>
    have e := exec_shift d (max d n) (le_max_left _ _) b n s f (by rw [hx]; simp)
    rw [hx, h (max d n) (b + n) (by omega) (le_max_right _ _)] at e
    simp only [Res.shift, Res.crash.injEq] at e
    show b ≤ r + B
    omega

/-! ## The nouns (hoon.hoon at the nockchain pin, as `hoonc` compiled them into forge) -/

/-- A null-terminated list of atoms (a Hoon `tape`). -/
def tapeNoun : List Nat → Noun
  | [] => atom 0
  | c :: rest => cell (atom c) (tapeNoun rest)

/-- `~_  leaf+"…"`'s clue: `[[1 [[1 %leaf] 7 [0 1] 8 [1 1 tape] 9 2 0 1]] 0 1]`. -/
def meanClue (msg : List Nat) : Noun :=
  cell (op 1 (cell (op 1 (atom 1717658988)) (op 7 (cell (op 0 (atom 1))
    (op 8 (cell (op 1 (cell (atom 1) (tapeNoun msg))) (op 9 (cell (atom 2) (op 0 (atom 1))))))))))
    (op 0 (atom 1))

/-- `%mean` (the `~_` hint tag). -/
def meanTag : Nat := 1851876717
/-- `%fast` (the `~/` jet-registration hint tag). -/
def fastTag : Nat := 1953718630

/-- "decrement-underflow" -/
def decMsg : List Nat :=
  [100, 101, 99, 114, 101, 109, 101, 110, 116, 45, 117, 110, 100, 101, 114, 102, 108, 111, 119]
/-- "subtract-underflow" -/
def subMsg : List Nat :=
  [115, 117, 98, 116, 114, 97, 99, 116, 45, 117, 110, 100, 101, 114, 102, 108, 111, 119]

/-- `=(a +(b))` in the trap: `[5 [0 30] [4 0 6]]`. -/
def trapTest : Noun := op 5 (cell (op 0 (atom 30)) (op 4 (op 0 (atom 6))))

/-- `$(b +(b))`'s core: `[10 [6 [4 0 6]] [0 1]]`. -/
def trapStep : Noun := op 10 (cell (cell (atom 6) (op 4 (op 0 (atom 6)))) (op 0 (atom 1)))

/-- **Loop shape 1, count-up** (`++dec`'s trap):
`[6 [5 [0 30] [4 0 6]] [0 6] [9 2 [10 [6 [4 0 6]] [0 1]]]]`. -/
def decTrap : Noun := op 6 (cell trapTest (cell (op 0 (atom 6)) (op 9 (cell (atom 2) trapStep))))

/-- `++dec`'s gate battery: `~_  leaf+"decrement-underflow"  ?<  =(0 a)  =+  b=0  |- …`. -/
def decBody : Noun :=
  op 11 (cell (cell (atom meanTag) (meanClue decMsg))
    (op 6 (cell (op 5 (cell (op 1 (atom 0)) (op 0 (atom 6))))
      (cell (op 0 (atom 0))
        (op 8 (cell (op 1 (atom 0))
          (op 8 (cell (op 1 decTrap) (op 9 (cell (atom 2) (op 0 (atom 1))))))))))))

/-- `++dec`'s arm (axis 2398 of the stdlib core): builds the gate `[decBody [0 core]]` under its
`~/  %dec` hint. -/
def decArm : Noun :=
  op 7 (cell (op 8 (cell (op 1 (atom 0)) (cell (op 1 decBody) (op 0 (atom 1)))))
    (op 11 (cell (cell (atom fastTag) (op 1 (cell (atom 6514020) (cell (op 0 (atom 7)) (atom 0)))))
      (op 0 (atom 1)))))

/-- `(dec /[X])` inside a gate whose context (axis 7) is the stdlib core:
`[8 [9 2398 [0 7]] [9 2 [10 [6 [0 X]] [0 2]]]]`. -/
def decCall (x : Nat) : Noun :=
  op 8 (cell (op 9 (cell (atom 2398) (op 0 (atom 7))))
    (op 9 (cell (atom 2) (op 10 (cell (cell (atom 6) (op 0 (atom x))) (op 0 (atom 2)))))))

/-- **Loop shape 2, decrement-both** (`++sub`'s gate battery): `~_  leaf+"subtract-underflow"
?:  =(0 b)  a  $(a (dec a), b (dec b))` — `[a b]` at axes 12/13, the recursion re-entering the
battery with the sample edited at axis 6. -/
def subBody : Noun :=
  op 11 (cell (cell (atom meanTag) (meanClue subMsg))
    (op 6 (cell (op 5 (cell (op 1 (atom 0)) (op 0 (atom 13))))
      (cell (op 0 (atom 12))
        (op 9 (cell (atom 2) (op 10 (cell (cell (atom 6) (cell (decCall 28) (decCall 29)))
          (op 0 (atom 1))))))))))

/-- `++sub`'s arm (axis 79 of the stdlib core). -/
def subArm : Noun :=
  op 7 (cell (op 8 (cell (op 1 (cell (atom 0) (atom 0))) (cell (op 1 subBody) (op 0 (atom 1)))))
    (op 11 (cell (cell (atom fastTag) (op 1 (cell (atom 6452595) (cell (op 0 (atom 7)) (atom 0)))))
      (op 0 (atom 1)))))

/-! ## Summary 1: the count-up loop -/

theorem trap_test_runs {b a : Nat} {g : Noun} (ha : axis 6 g = some (atom a)) :
    Runs (cell decTrap (cell (atom b) g)) trapTest (loob (decide (atom a = atom (b + 1)))) 4 :=
  runs_tis (runs_slot (a := 30) (by rw [← ha]; rfl)) (runs_lus (runs_slot (a := 6) rfl))

/-- **`trap_runs`** (count-up, proved once): on the trap core `[decTrap [b g]]` with
`/[6 g] = b + 1 + n`, the loop answers `b + n` in exactly `6 + 10·n` steps. -/
theorem trap_runs : ∀ (n b : Nat) (g : Noun), axis 6 g = some (atom (b + 1 + n)) →
    Runs (cell decTrap (cell (atom b) g)) decTrap (atom (b + n)) (6 + 10 * n)
  | 0, b, g, ha => by
    have ht := trap_test_runs (b := b) ha
    have hy := runs_sixYes (z := op 9 (cell (atom 2) trapStep))
      (runs_congr ht (by simp [loob]) rfl) (runs_slot (s := cell decTrap (cell (atom b) g)) (a := 6) rfl)
    exact runs_congr hy (by simp) rfl
  | n + 1, b, g, ha => by
    have ht := trap_test_runs (b := b) ha
    have hne : decide (atom (b + 1 + (n + 1)) = atom (b + 1)) = false := by simp
    rw [hne] at ht
    have hc : Runs (cell decTrap (cell (atom b) g)) trapStep (cell decTrap (cell (atom (b + 1)) g)) 4 :=
      runs_ten (runs_slot (a := 1) rfl) (runs_lus (runs_slot (a := 6) rfl)) rfl
    have ih := trap_runs n (b + 1) g (by rw [ha]; congr 2; omega)
    have hz := runs_nine (a := 2) hc rfl ih
    have hn := runs_sixNo (y := op 0 (atom 6)) ht hz
    exact runs_congr hn (by congr 1; omega) (by omega)

/-- A trap core without an axis 30 crashes at the test, after 3 steps. -/
theorem trap_crash {s : Noun} (h : axis 30 s = none) : CrashRuns s decTrap 3 :=
  crashRuns_sixT (crashRuns_tisB (crashRuns_slot h))

theorem axis30_some {s v : Noun} (h : axis 30 s = some v) :
    ∃ x y g, s = cell x (cell y g) ∧ axis 6 g = some v := by
  rcases s with _ | ⟨x, _ | ⟨y, g⟩⟩
  · simp [axis, axisAux] at h
  · simp [axis, axisAux] at h
  · exact ⟨x, y, g, rfl, by rw [← h]; rfl⟩

/-- The product shape of the count-up loop over `a ∈ [al, ah]`: `a - 1`. -/
def trapOut (al ah : Nat) : Shape :=
  if al = ah then .exact (.atom (al - 1)) else .range (al - 1) (ah - 1)

/-- `sh` is exactly the noun `n`. -/
def isExact (n : Noun) : Shape → Bool
  | .exact m => decide (m = n)
  | _ => false

theorem isExact_eq {n : Noun} {sh : Shape} (h : isExact n sh = true) : sh = .exact n := by
  cases sh <;> simp_all [isExact]

/-- The recogniser for shape 1: the formula is `decTrap`, the subject's battery (axis 2) is
`decTrap`, the counter `b` (axis 6) and the bound `a` (axis 30) have interval shapes, and every
`b` is below every `a` (so the loop terminates: `++dec`'s `?<  =(0 a)` establishes it). -/
def trapSummary (sh : Shape) (f : Noun) : Option (Nat × Shape) :=
  if f = decTrap ∧ isExact decTrap (sAxis 2 sh) = true then
    (asRange (sAxis 6 sh)).bind fun b =>
    (asRange (sAxis 30 sh)).bind fun a =>
    if b.2 < a.1 then some (6 + 10 * (a.2 - 1 - b.1), trapOut a.1 a.2) else none
  else none

/-- **`trap_summary_sound`** — `B(n) = 6 + 10·n` with `n = ah - 1 - bl`. -/
theorem trap_summary_sound : OracleSound trapSummary := by
  intro sh f B o h s hs
  unfold trapSummary at h
  by_cases hc : f = decTrap ∧ isExact decTrap (sAxis 2 sh) = true
  swap
  · rw [if_neg hc] at h; simp at h
  rw [if_pos hc] at h
  obtain ⟨rfl, hL⟩ := hc
  have hL := isExact_eq hL
  obtain ⟨⟨bl, bh⟩, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨al, ah⟩, ha, h⟩ := Option.bind_eq_some_iff.mp h
  simp only at h
  split_ifs at h with hlt
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  cases h30 : axis 30 s with
  | none => exact Sound.of_crashRuns (trap_crash h30) (by omega)
  | some v =>
    obtain ⟨a, rfl, hal, hah⟩ := asRange_sound (sAxis_sound hs h30) ha
    obtain ⟨x, y, g, rfl, hg⟩ := axis30_some h30
    have hx : x = decTrap := by
      have := sAxis_sound (a := 2) hs rfl
      rw [hL, fits_exact] at this
      exact this
    subst hx
    obtain ⟨b, rfl, hbl, hbh⟩ := asRange_sound (sAxis_sound (a := 6) hs rfl) hb
    have hrun := trap_runs (a - 1 - b) b g (by rw [hg]; congr 2; omega)
    refine Sound.of_runs hrun ?_ (by omega)
    unfold trapOut
    split_ifs with heq
    · simp only [fits_exact]; congr 1; omega
    · simp only [fits, decide_eq_true_eq]; omega

/-! ## Summary 2: the decrement-both loop -/

/-- The gate `++dec`'s arm builds on a core `c`. -/
def decGate (c : Noun) : Noun := cell decBody (cell (atom 0) c)

theorem decArm_runs (c : Noun) : Runs c decArm (decGate c) 9 := by
  have hx : Runs c (op 8 (cell (op 1 (atom 0)) (cell (op 1 decBody) (op 0 (atom 1)))))
      (decGate c) 5 :=
    runs_eight (runs_quote c (atom 0)) (runs_cons (runs_quote _ decBody) (runs_slot (a := 1) rfl))
  have hy := runs_hintD (tag := fastTag) (runs_quote (decGate c) (cell (atom 6514020)
    (cell (op 0 (atom 7)) (atom 0)))) (runs_slot (s := decGate c) (a := 1) rfl)
  exact runs_seven hx hy

theorem meanClue_runs (s : Noun) (msg : List Nat) : ∃ v, Runs s (meanClue msg) v 3 :=
  ⟨_, runs_cons (runs_quote _ _) (runs_slot (a := 1) rfl)⟩

/-- `++dec`'s gate on `m + 1` answers `m` in `20 + 10·m` steps (the trap plus its entry). -/
theorem decBody_runs (m : Nat) (c : Noun) :
    Runs (cell decBody (cell (atom (m + 1)) c)) decBody (atom m) (20 + 10 * m) := by
  obtain ⟨_, hclue⟩ := meanClue_runs (cell decBody (cell (atom (m + 1)) c)) decMsg
  have ht := runs_tis (runs_quote (cell decBody (cell (atom (m + 1)) c)) (atom 0))
    (runs_slot (s := cell decBody (cell (atom (m + 1)) c)) (v := atom (m + 1)) (a := 6) rfl)
  have hne : decide (atom 0 = atom (m + 1)) = false := by simp
  rw [hne] at ht
  have htrap := trap_runs m 0 (cell decBody (cell (atom (m + 1)) c))
    (by rw [show 0 + 1 + m = m + 1 by omega]; rfl)
  have h9 := runs_nine (a := 2) (runs_slot (s := cell decTrap (cell (atom 0)
    (cell decBody (cell (atom (m + 1)) c)))) (a := 1) rfl) rfl htrap
  have h8 := runs_eight (runs_quote _ decTrap) h9
  have h8' := runs_eight (runs_quote _ (atom 0)) h8
  have h6 := runs_sixNo (y := op 0 (atom 0)) ht h8'
  have h11 := runs_hintD (tag := meanTag) hclue h6
  exact runs_congr h11 (by simp) (by omega)

/-- `(dec /[X])` from a gate whose context `/[7]` holds `decArm` at 2398, on `m + 1`. -/
theorem decCall_runs {s c : Noun} {x m : Nat} (h7 : axis 7 s = some c)
    (harm : axis 2398 c = some decArm) (hx : axis x (cell (decGate c) s) = some (atom (m + 1))) :
    Runs s (decCall x) (atom m) (36 + 10 * m) := by
  have hg := runs_nine (a := 2398) (runs_slot h7) harm (decArm_runs c)
  have hed : edit 6 (atom (m + 1)) (decGate c) = some (cell decBody (cell (atom (m + 1)) c)) := rfl
  have hten := runs_ten (runs_slot (s := cell (decGate c) s) (a := 2) rfl) (runs_slot hx) hed
  have h9 := runs_nine (a := 2) hten rfl (decBody_runs m c)
  exact runs_congr (runs_eight hg h9) rfl (by omega)

/-- The sub gate over sample `[a b]` and stdlib core `c`. -/
def subGate (a b : Nat) (c : Noun) : Noun := cell subBody (cell (cell (atom a) (atom b)) c)

/-- **`sub_runs`** (decrement-both, proved once by induction on `b`): for `b ≤ a`, `++sub`
answers `a - b` in exactly `9 + 74·b + 10·a·b` steps. -/
theorem sub_runs (c : Noun) (harm : axis 2398 c = some decArm) :
    ∀ (b a : Nat), b ≤ a → Runs (subGate a b c) subBody (atom (a - b)) (9 + 74 * b + 10 * a * b)
  | 0, a, _ => by
    obtain ⟨_, hclue⟩ := meanClue_runs (subGate a 0 c) subMsg
    have ht := runs_tis (runs_quote (subGate a 0 c) (atom 0)) (runs_slot (s := subGate a 0 c)
      (v := atom 0) (a := 13) rfl)
    have hy := runs_sixYes (z := op 9 (cell (atom 2) (op 10 (cell (cell (atom 6)
      (cell (decCall 28) (decCall 29))) (op 0 (atom 1))))))
      (runs_congr ht (by simp [loob]) rfl) (runs_slot (s := subGate a 0 c) (v := atom a) (a := 12) rfl)
    exact runs_congr (runs_hintD (tag := meanTag) hclue hy) (by simp) (by omega)
  | b + 1, a, hab => by
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨_, hclue⟩ := meanClue_runs (subGate (a' + 1) (b + 1) c) subMsg
    have ht := runs_tis (runs_quote (subGate (a' + 1) (b + 1) c) (atom 0))
      (runs_slot (s := subGate (a' + 1) (b + 1) c) (v := atom (b + 1)) (a := 13) rfl)
    have hne : decide (atom 0 = atom (b + 1)) = false := by simp
    rw [hne] at ht
    have hda := decCall_runs (s := subGate (a' + 1) (b + 1) c) (x := 28) (m := a') rfl harm rfl
    have hdb := decCall_runs (s := subGate (a' + 1) (b + 1) c) (x := 29) (m := b) rfl harm rfl
    have hed : edit 6 (cell (atom a') (atom b)) (subGate (a' + 1) (b + 1) c) = some (subGate a' b c) :=
      rfl
    have hten := runs_ten (runs_slot (s := subGate (a' + 1) (b + 1) c) (a := 1) rfl)
      (runs_cons hda hdb) hed
    have ih := sub_runs c harm b a' (by omega)
    have h9 := runs_nine (a := 2) hten rfl ih
    have h6 := runs_sixNo (y := op 0 (atom 12)) ht h9
    exact runs_congr (runs_hintD (tag := meanTag) hclue h6) (by congr 1; omega) (by ring)

/-- The product shape of `++sub` over `a ∈ [al, ah]`, `b ∈ [bl, bh]`, `bh ≤ al`: `a - b`. -/
def subOut (al ah bl bh : Nat) : Shape :=
  if al - bh = ah - bl then .exact (.atom (al - bh)) else .range (al - bh) (ah - bl)

/-- The closed form at the box's corner: `9 + 74·bh + 10·ah·bh`. -/
def subBound (ah bh : Nat) : Nat := 9 + 74 * bh + 10 * ah * bh

/-- The parts of a sub-gate shape `[L [[a b] c]]` with an exact battery and context. -/
def gateParts : Shape → Option (Noun × Shape × Shape × Noun)
  | .cell (.exact L) (.cell (.cell as bs) (.exact c)) => some (L, as, bs, c)
  | _ => none

theorem gateParts_some {sh : Shape} {L c : Noun} {as bs : Shape}
    (h : gateParts sh = some (L, as, bs, c)) :
    sh = .cell (.exact L) (.cell (.cell as bs) (.exact c)) := by
  unfold gateParts at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl
  · cases h

/-- The recogniser for shape 2: the formula is `subBody`, the subject is the sub gate
`[subBody [[a b] c]]` with interval shapes for `a`, `b`, an exact context core whose arm 2398 is
`decArm`, and every `b` at most every `a` (no underflow). -/
def subSummary (sh : Shape) (f : Noun) : Option (Nat × Shape) :=
  if f = subBody then
    (gateParts sh).bind fun p =>
    (asRange p.2.1).bind fun a =>
    (asRange p.2.2.1).bind fun b =>
    if p.1 = subBody ∧ axis 2398 p.2.2.2 = some decArm ∧ b.2 ≤ a.1 then
      some (subBound a.2 b.2, subOut a.1 a.2 b.1 b.2)
    else none
  else none

/-- **`sub_summary_sound`** — `B = 9 + 74·bh + 10·ah·bh`, bilinear in the declared maxima. -/
theorem sub_summary_sound : OracleSound subSummary := by
  intro sh f B o h s hs
  unfold subSummary at h
  by_cases hf : f = subBody
  swap
  · rw [if_neg hf] at h; simp at h
  rw [if_pos hf] at h
  subst hf
  obtain ⟨⟨L, as, bs, c⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨al, ah⟩, ha, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨bl, bh⟩, hb, h⟩ := Option.bind_eq_some_iff.mp h
  simp only at h ha hb
  split_ifs at h with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨rfl, harm, hle⟩ := hc
  rw [gateParts_some hp] at hs
  rcases s with _ | ⟨L', _ | ⟨_ | ⟨x, y⟩, c'⟩⟩ <;> simp [fits] at hs
  obtain ⟨rfl, ⟨hx, hy⟩, rfl⟩ := hs
  obtain ⟨a, rfl, hal, hah⟩ := asRange_sound hx ha
  obtain ⟨b, rfl, hbl, hbh⟩ := asRange_sound hy hb
  have hrun := sub_runs c' harm b a (by omega)
  refine Sound.of_runs hrun ?_ ?_
  · unfold subOut
    split_ifs with heq
    · simp only [fits_exact]; congr 1; omega
    · simp only [fits, decide_eq_true_eq]; omega
  · unfold subBound
    have h1 : a * b ≤ ah * bh := Nat.mul_le_mul hah hbh
    have h2 : 10 * a * b ≤ 10 * ah * bh := by
      rw [Nat.mul_assoc, Nat.mul_assoc]; exact Nat.mul_le_mul_left 10 h1
    omega

/-! ## The oracle and `costSym` -/

/-- The summaries `costSym` consults: count-up first, then decrement-both. -/
def summaries : Oracle := fun sh f =>
  match trapSummary sh f with
  | some r => some r
  | none => subSummary sh f

theorem summaries_sound : OracleSound summaries := by
  intro sh f B o h s hs
  unfold summaries at h
  cases ht : trapSummary sh f with
  | some r => rw [ht] at h; cases h; exact trap_summary_sound sh f B o ht s hs
  | none => rw [ht] at h; exact sub_summary_sound sh f B o h s hs

/-- **`costSym`**: `cost` with the loop summaries — O(program) work on forge, whatever the
declared maxima; the bound is the summaries' polynomials composed by the interpreter's `+`/`max`. -/
def costSym (sh : Shape) (f : Noun) : Option Nat := (acostWith summaries costFuel sh f).map (·.1)

/-- **`cost_sym_sound`**: the same guarantee as `cost_sound`. -/
theorem cost_sym_sound {sh : Shape} {f s : Noun} {B : Nat} (h : costSym sh f = some B)
    (hs : HasShape s sh) : ∀ fuel, B ≤ fuel →
      Nock.run fuel s f ≠ .error .exhausted ∧ Nock.steps fuel s f ≤ B := by
  intro fuel hfuel
  unfold costSym at h
  obtain ⟨⟨B', o⟩, ha, hB⟩ := Option.map_eq_some_iff.mp h
  simp only at hB; subst hB
  have S := acostWith_sound summaries_sound _ _ _ _ _ ha s hs fuel fuel
  have hne := S.2 hfuel hfuel
  refine ⟨fun he => hne (run_eq_exhausted.mp he), ?_⟩
  have hw := S.1
  unfold Nock.steps
  cases hx : exec fuel fuel s f with
  | ok v r => rw [hx] at hw; dsimp only; have := hw.2; omega
  | crash r => rw [hx] at hw; simp only [Res.within] at hw; dsimp only; omega
  | exhausted => exact absurd hx hne

/-! ## Poles, kernel-checked

The count-up loop alone (no stdlib): `[decTrap [0 [_ [a _]]]]`, so `a` sits at axis 30. -/

/-- The trap core with counter `0` and bound `a` (a dec gate's shape). -/
def trapSubject (a : Nat) : Noun :=
  cell decTrap (cell (atom 0) (cell (atom 0) (cell (atom a) (atom 0))))

def trapShape (lo hi : Nat) : Shape :=
  .cell (.exact decTrap) (.cell (.exact (atom 0)) (.cell .any (.cell (.range lo hi) .any)))

/-- The run the summary prices: `a = 5` is 4 iterations, `6 + 10·4 = 46` steps. -/
theorem pole_trap_steps : steps 100 (trapSubject 5) decTrap = 46 := by decide +kernel

/-- One step under is exhaustion: 46 is the count, not a slack bound. -/
theorem pole_trap_exhausted_45 : run 45 (trapSubject 5) decTrap = .error .exhausted := by
  decide +kernel

/-- The unrolled interpreter and the summary agree on `[1, 5]`: 46 both. -/
theorem pole_trap_unrolled : cost (trapShape 1 5) decTrap = some 46 := by decide +kernel

theorem pole_trap_symbolic_5 : costSym (trapShape 1 5) decTrap = some 46 := by decide +kernel

/-- **The summary at `2⁶⁴`**: kernel-checked by `decide` — the recogniser fires at the root and
the bound is the closed form; the unrolled `cost` would walk `2⁶⁴` iterations. -/
theorem pole_trap_symbolic_2_64 :
    costSym (trapShape 1 (2 ^ 64)) decTrap = some (6 + 10 * (2 ^ 64 - 1)) := by decide +kernel

/-- So every run of the trap on a bound up to `2⁶⁴` finishes within `6 + 10·(2⁶⁴ - 1)` steps. -/
theorem trap_priced_2_64 {s : Noun} (hs : HasShape s (trapShape 1 (2 ^ 64))) :
    run (6 + 10 * (2 ^ 64 - 1)) s decTrap ≠ .error .exhausted :=
  (cost_sym_sound pole_trap_symbolic_2_64 hs _ le_rfl).1

/-- The refutable pole of the summary itself: it can never answer one step under the count at
`a = 5`, since `cost_sym_sound` would then prove `pole_trap_exhausted_45` false. -/
theorem cost_sym_never_under_counts_trap : costSym (trapShape 5 5) decTrap ≠ some 45 := fun h =>
  (cost_sym_sound h (by decide +kernel) 45 le_rfl).1 pole_trap_exhausted_45

/-! ## An exact run fixes the metered count -/

theorem steps_of_runs {s f v : Noun} {n fuel : Nat} (h : Runs s f v n) (hf : n ≤ fuel) :
    steps fuel s f = n := by
  unfold steps; rw [h fuel fuel hf hf]; dsimp only; omega

/-! ## Forge (the 566 KB noun: `native_decide`, flagged)

`forgeProgram` is NC-1's cue of `forge.jam`. Its gate is `*[P [9 2 0 1]]`; the hoon stdlib core the
gate's arms call into (`[9 38 0 16383]` = gte, `[9 79 0 16383]` = sub, `[9 2398 0 16383]` = dec, from
four pushes deep) is axis 1023 of the gate. The two `forge_*_arm` facts pin that the nouns above ARE
forge's: everything about `decArm`/`subBody` proved above then holds of forge's own stdlib. -/

/-- forge's gate: `*[P [9 2 0 1]]` (the arm `slam 2` takes). -/
def forgeGate : Noun :=
  match exec 100000 100000 forgeProgram (op 9 (cell (atom 2) (op 0 (atom 1)))) with
  | .ok g _ => g
  | _ => atom 0

/-- The hoon stdlib core of forge's gate (axis 1023). -/
def forgeStdlib : Noun := (axis 1023 forgeGate).getD (atom 0)

theorem forge_dec_arm : axis 2398 forgeStdlib = some decArm := by native_decide
theorem forge_sub_arm : axis 79 forgeStdlib = some subArm := by native_decide

/-- **`sub` on forge's own stdlib, for every `b ≤ a`**: `9 + 74·b + 10·a·b` steps, exactly — the
closed form, instantiated on the real core (only `forge_dec_arm` is native). -/
theorem forge_sub_steps (a b : Nat) (h : b ≤ a) :
    steps (9 + 74 * b + 10 * a * b) (subGate a b forgeStdlib) subBody = 9 + 74 * b + 10 * a * b :=
  steps_of_runs (sub_runs forgeStdlib forge_dec_arm b a h) le_rfl

/-- The closed form against the interpreter, not the proof: `a = 5, b = 3` is 381 steps. -/
theorem pole_sub_steps : steps 1000 (subGate 5 3 forgeStdlib) subBody = 381 := by native_decide

/-- One step under exhausts: the closed form is the count, not a slack bound. -/
theorem pole_sub_exhausted_380 : run 380 (subGate 5 3 forgeStdlib) subBody = .error .exhausted := by
  native_decide

/-- The sub gate over `a ∈ [alo, ahi]`, `b ∈ [blo, bhi]`, forge's stdlib. -/
def subShape (alo ahi blo bhi : Nat) : Shape :=
  .cell (.exact subBody) (.cell (.cell (.range alo ahi) (.range blo bhi)) (.exact forgeStdlib))

/-- **Summary 2 at `2⁶⁴ × 2³²`**: `a ∈ [2⁶³, 2⁶⁴]`, `b ≤ 2³²` — `9 + 74·2³² + 10·2⁶⁴·2³²`. -/
theorem pole_sub_symbolic :
    costSym (subShape (2 ^ 63) (2 ^ 64) 0 (2 ^ 32)) subBody = some (subBound (2 ^ 64) (2 ^ 32)) := by
  native_decide

/-- **THE NUMBER, again**: with the summaries, forge at the sample's own maxima is still 1,345. -/
theorem pole_forge_sym_bound : costSym (forgeShape 3 2 0) (slam 2) = some 1345 := by native_decide

theorem pole_forge_sym_3 : costSym (forgeShape 3 3 3) (slam 2) = some 1365 := by native_decide

theorem pole_forge_sym_1000 : costSym (forgeShape 1000 1000 1000) (slam 2) = some 61185 := by
  native_decide

/-- The symbolic and the unrolled interpreter agree on forge where both run. -/
theorem cost_sym_eq_cost_320 : costSym (forgeShape 3 2 0) (slam 2) = cost (forgeShape 3 2 0) (slam 2) :=
  pole_forge_sym_bound.trans pole_forge_bound.symm

theorem cost_sym_eq_cost_3 : costSym (forgeShape 3 3 3) (slam 2) = cost (forgeShape 3 3 3) (slam 2) :=
  pole_forge_sym_3.trans pole_forge_bound_3.symm

theorem cost_sym_eq_cost_1000 :
    costSym (forgeShape 1000 1000 1000) (slam 2) = cost (forgeShape 1000 1000 1000) (slam 2) :=
  pole_forge_sym_1000.trans pole_forge_bound_1000.symm

theorem pole_forge_sym_10_6 :
    costSym (forgeShape (10 ^ 6) (10 ^ 6) (10 ^ 6)) (slam 2) = some (1185 + 60 * 10 ^ 6) := by
  native_decide

theorem pole_forge_sym_2_32 :
    costSym (forgeShape (2 ^ 32) (2 ^ 32) (2 ^ 32)) (slam 2) = some (1185 + 60 * 2 ^ 32) := by
  native_decide

/-- **`pole_forge_symbolic`** — the exit number: forge with every field declared `≤ 2⁶⁴` is priced
at `1185 + 60·2⁶⁴` without unrolling (NC-1's `cost` would walk `2⁶⁴` decrements). -/
theorem pole_forge_symbolic :
    costSym (forgeShape (2 ^ 64) (2 ^ 64) (2 ^ 64)) (slam 2) = some (1185 + 60 * 2 ^ 64) := by
  native_decide

/-- The price, as a theorem: every sample of forge's shape at `2⁶⁴` runs within `1185 + 60·2⁶⁴`. -/
theorem forge_priced_2_64 {s : Noun} (hs : HasShape s (forgeShape (2 ^ 64) (2 ^ 64) (2 ^ 64)))
    (fuel : Nat) (h : 1185 + 60 * 2 ^ 64 ≤ fuel) :
    run fuel s (slam 2) ≠ .error .exhausted ∧ steps fuel s (slam 2) ≤ 1185 + 60 * 2 ^ 64 :=
  cost_sym_sound pole_forge_symbolic hs fuel h

/-! ## Axioms -/

open Minidregg.Theory.AssertAxioms

#assert_axioms runs_congr
#assert_axioms runs_slot
#assert_axioms runs_quote
#assert_axioms runs_cons
#assert_axioms runs_lus
#assert_axioms runs_tis
#assert_axioms runs_sixYes
#assert_axioms runs_sixNo
#assert_axioms runs_seven
#assert_axioms runs_eight
#assert_axioms runs_nine
#assert_axioms runs_ten
#assert_axioms runs_hintD
#assert_axioms crashRuns_slot
#assert_axioms crashRuns_tisB
#assert_axioms crashRuns_sixT
#assert_axioms Sound.of_runs
#assert_axioms Sound.of_crashRuns
#assert_axioms trap_test_runs
#assert_axioms trap_runs
#assert_axioms trap_crash
#assert_axioms axis30_some
#assert_axioms isExact_eq
#assert_axioms trap_summary_sound
#assert_axioms decArm_runs
#assert_axioms meanClue_runs
#assert_axioms decBody_runs
#assert_axioms decCall_runs
#assert_axioms sub_runs
#assert_axioms gateParts_some
#assert_axioms sub_summary_sound
#assert_axioms summaries_sound
#assert_axioms cost_sym_sound
#assert_axioms pole_trap_steps
#assert_axioms pole_trap_exhausted_45
#assert_axioms pole_trap_unrolled
#assert_axioms pole_trap_symbolic_5
#assert_axioms pole_trap_symbolic_2_64
#assert_axioms trap_priced_2_64
#assert_axioms cost_sym_never_under_counts_trap
#assert_axioms steps_of_runs

/-! The forge facts are `native_decide` (the kernel cannot reduce `cue`/`exec` on 566 KB); each pins
exactly its own compiler-trust axiom, and the derived ones inherit only those. -/
/-- info: 'Minidregg.Theory.NockCost.forge_dec_arm' depends on axioms: [propext, Classical.choice, Quot.sound, forge_dec_arm._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms forge_dec_arm
/-- info: 'Minidregg.Theory.NockCost.forge_sub_arm' depends on axioms: [propext, Classical.choice, Quot.sound, forge_sub_arm._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms forge_sub_arm
/-- info: 'Minidregg.Theory.NockCost.pole_sub_steps' depends on axioms: [propext, Classical.choice, Quot.sound, pole_sub_steps._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms pole_sub_steps
/-- info: 'Minidregg.Theory.NockCost.pole_sub_exhausted_380' depends on axioms: [propext, Classical.choice, Quot.sound, pole_sub_exhausted_380._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms pole_sub_exhausted_380
/-- info: 'Minidregg.Theory.NockCost.pole_sub_symbolic' depends on axioms: [propext, Classical.choice, Quot.sound, pole_sub_symbolic._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms pole_sub_symbolic
/-- info: 'Minidregg.Theory.NockCost.pole_forge_sym_bound' depends on axioms: [propext, Classical.choice, Quot.sound, pole_forge_sym_bound._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms pole_forge_sym_bound
/-- info: 'Minidregg.Theory.NockCost.pole_forge_sym_3' depends on axioms: [propext, Classical.choice, Quot.sound, pole_forge_sym_3._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms pole_forge_sym_3
/-- info: 'Minidregg.Theory.NockCost.pole_forge_sym_1000' depends on axioms: [propext, Classical.choice, Quot.sound, pole_forge_sym_1000._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms pole_forge_sym_1000
/-- info: 'Minidregg.Theory.NockCost.pole_forge_sym_10_6' depends on axioms: [propext, Classical.choice, Quot.sound, pole_forge_sym_10_6._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms pole_forge_sym_10_6
/-- info: 'Minidregg.Theory.NockCost.pole_forge_sym_2_32' depends on axioms: [propext, Classical.choice, Quot.sound, pole_forge_sym_2_32._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms pole_forge_sym_2_32
/-- info: 'Minidregg.Theory.NockCost.pole_forge_symbolic' depends on axioms: [propext, Classical.choice, Quot.sound, pole_forge_symbolic._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms pole_forge_symbolic
/-- info: 'Minidregg.Theory.NockCost.forge_priced_2_64' depends on axioms: [propext, Classical.choice, Quot.sound, pole_forge_symbolic._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms forge_priced_2_64
/-- info: 'Minidregg.Theory.NockCost.forge_sub_steps' depends on axioms: [propext, Classical.choice, Quot.sound, forge_dec_arm._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms forge_sub_steps

end NockCost
end Minidregg.Theory
