/-
# Theory.Nock — Nock 4K as an inductive relation, and a fueled interpreter

`Step s f v` is `*[s f] = v`; `Crash s f` is "evaluating `*[s f]` reaches a
rule whose precondition fails" — `++mink`'s `[%2 trace]`. Both are inductive,
with the evaluation ORDER of `nockvm` at nockchain `cbd9298f`
(`crates/nockvm/rust/nockvm/src/interpreter.rs`): cons head before tail, `%2`
subject before formula, `%5` left before right, `%10` the tree `d` BEFORE the
patch `c` (`Todo10::ComputeTree` first), `%11` clue before body.

Opcodes are exactly the pin's decode (`push_formula_with_space`,
interpreter.rs:1458-1690): a formula is a cell; a cell head is autocons; an
atom head `0`–`11` has the argument shapes below; `12` (scry) has NO rule here
(level 0: no scry namespace) and so is a `Crash`, as is any other opcode.
Hints (`%11`) are evaluated for effect-freedom and then DROPPED: a static hint
is `*[a c]`; a dynamic hint `[11 [b c] d]` evaluates `c` (a crash there
crashes) and returns `*[a d]`. Nothing in a hint is trusted.

`exec d b s f` is the interpreter: `b` is the step budget (one unit per rule
application — the count NOCK §2.5 meters), `d` a structural depth bound that
never binds first when `b ≤ d` (as in `run`, where both are the fuel). It
returns `ok v rem`, `crash rem`, or `exhausted`. `exhausted` is ours: Nock
has no fuel, so exhaustion says nothing about the term
(`exhausted_says_nothing`, `loop_diverges`), while `crash` is a property of
the term: `run_crash_iff`.
-/
import Theory.Noun

namespace Minidregg.Theory
namespace Nock

open Noun

/-- A decoded formula: exactly the shapes `nockvm`'s decoder accepts. -/
inductive Form where
  | cons (b c d : Noun)            -- [[b c] d]
  | slot (a : Nat)                 -- [0 a]
  | quote (x : Noun)               -- [1 x]
  | eval (b c : Noun)              -- [2 b c]
  | wut (b : Noun)                 -- [3 b]
  | lus (b : Noun)                 -- [4 b]
  | tis (b c : Noun)               -- [5 b c]
  | six (b c d : Noun)             -- [6 b c d]
  | seven (b c : Noun)             -- [7 b c]
  | eight (b c : Noun)             -- [8 b c]
  | nine (a : Nat) (c : Noun)      -- [9 a c]
  | ten (a : Nat) (c d : Noun)     -- [10 [a c] d]
  | hintS (tag : Nat) (d : Noun)   -- [11 tag d]
  | hintD (tag : Nat) (c d : Noun) -- [11 [tag c] d]
  deriving DecidableEq, Repr

/-- `nockvm`'s formula decoder; `none` is a crash (`BAIL_EXIT`). -/
def parse : Noun → Option Form
  | cell (cell b c) d => some (.cons b c d)
  | cell (atom 0) (atom a) => some (.slot a)
  | cell (atom 1) x => some (.quote x)
  | cell (atom 2) (cell b c) => some (.eval b c)
  | cell (atom 3) b => some (.wut b)
  | cell (atom 4) b => some (.lus b)
  | cell (atom 5) (cell b c) => some (.tis b c)
  | cell (atom 6) (cell b (cell c d)) => some (.six b c d)
  | cell (atom 7) (cell b c) => some (.seven b c)
  | cell (atom 8) (cell b c) => some (.eight b c)
  | cell (atom 9) (cell (atom a) c) => some (.nine a c)
  | cell (atom 10) (cell (cell (atom a) c) d) => some (.ten a c d)
  | cell (atom 11) (cell (atom t) d) => some (.hintS t d)
  | cell (atom 11) (cell (cell (atom t) c) d) => some (.hintD t c d)
  | _ => none

/-- Notation-free constructors for formulas. -/
def nat (n : Nat) : Noun := atom n
def op (n : Nat) (x : Noun) : Noun := cell (atom n) x

/-! ## The spec -/

/-- `Step s f v` ≙ `*[s f] = v`: the rules of Nock 4K, one constructor each. -/
inductive Step : Noun → Noun → Noun → Prop
  /-- `*[a [b c] d] = [*[a b c] *[a d]]` -/
  | cons {s b c d hv tv} : Step s (cell b c) hv → Step s d tv →
      Step s (cell (cell b c) d) (cell hv tv)
  /-- `*[a 0 b] = /[b a]` -/
  | slot {s a v} : axis a s = some v → Step s (cell (atom 0) (atom a)) v
  /-- `*[a 1 b] = b` -/
  | quote {s x} : Step s (cell (atom 1) x) x
  /-- `*[a 2 b c] = *[*[a b] *[a c]]` -/
  | eval {s b c s' f' v} : Step s b s' → Step s c f' → Step s' f' v →
      Step s (cell (atom 2) (cell b c)) v
  /-- `*[a 3 b] = ?*[a b]` (0 for a cell, 1 for an atom) -/
  | wut {s b r} : Step s b r → Step s (cell (atom 3) b) (loob r.isCell)
  /-- `*[a 4 b] = +*[a b]`; `+` of a cell has no rule -/
  | lus {s b n} : Step s b (atom n) → Step s (cell (atom 4) b) (atom (n + 1))
  /-- `*[a 5 b c] = =[*[a b] *[a c]]` -/
  | tis {s b c x y} : Step s b x → Step s c y →
      Step s (cell (atom 5) (cell b c)) (loob (decide (x = y)))
  /-- `*[a 6 b c d]` with `*[a b] = 0` is `*[a c]` -/
  | sixYes {s b c d v} : Step s b (atom 0) → Step s c v →
      Step s (cell (atom 6) (cell b (cell c d))) v
  /-- `*[a 6 b c d]` with `*[a b] = 1` is `*[a d]`; any other test has no rule -/
  | sixNo {s b c d v} : Step s b (atom 1) → Step s d v →
      Step s (cell (atom 6) (cell b (cell c d))) v
  /-- `*[a 7 b c] = *[*[a b] c]` -/
  | seven {s b c s' v} : Step s b s' → Step s' c v → Step s (cell (atom 7) (cell b c)) v
  /-- `*[a 8 b c] = *[[*[a b] a] c]` -/
  | eight {s b c p v} : Step s b p → Step (cell p s) c v → Step s (cell (atom 8) (cell b c)) v
  /-- `*[a 9 b c] = *[*[a c] 2 [0 1] 0 b]` -/
  | nine {s a c core f' v} : Step s c core → axis a core = some f' → Step core f' v →
      Step s (cell (atom 9) (cell (atom a) c)) v
  /-- `*[a 10 [b c] d] = #[b *[a c] *[a d]]` -/
  | ten {s a c d t p v} : Step s d t → Step s c p → edit a p t = some v →
      Step s (cell (atom 10) (cell (cell (atom a) c) d)) v
  /-- `*[a 11 b c] = *[a c]` (static hint, dropped) -/
  | hintS {s tag d v} : Step s d v → Step s (cell (atom 11) (cell (atom tag) d)) v
  /-- `*[a 11 [b c] d] = *[[*[a c] *[a d]] 0 3]` (dynamic hint: evaluated, dropped) -/
  | hintD {s tag c d hv v} : Step s c hv → Step s d v →
      Step s (cell (atom 11) (cell (cell (atom tag) c) d)) v

/-- `Crash s f`: evaluation of `*[s f]`, in the order above, reaches a rule
whose precondition fails. -/
inductive Crash : Noun → Noun → Prop
  | malformed {s f} : parse f = none → Crash s f
  | consHd {s b c d} : Crash s (cell b c) → Crash s (cell (cell b c) d)
  | consTl {s b c d hv} : Step s (cell b c) hv → Crash s d → Crash s (cell (cell b c) d)
  | slot {s a} : axis a s = none → Crash s (cell (atom 0) (atom a))
  | evalB {s b c} : Crash s b → Crash s (cell (atom 2) (cell b c))
  | evalC {s b c s'} : Step s b s' → Crash s c → Crash s (cell (atom 2) (cell b c))
  | evalR {s b c s' f'} : Step s b s' → Step s c f' → Crash s' f' →
      Crash s (cell (atom 2) (cell b c))
  | wut {s b} : Crash s b → Crash s (cell (atom 3) b)
  | lus {s b} : Crash s b → Crash s (cell (atom 4) b)
  | lusCell {s b x y} : Step s b (cell x y) → Crash s (cell (atom 4) b)
  | tisB {s b c} : Crash s b → Crash s (cell (atom 5) (cell b c))
  | tisC {s b c x} : Step s b x → Crash s c → Crash s (cell (atom 5) (cell b c))
  | sixT {s b c d} : Crash s b → Crash s (cell (atom 6) (cell b (cell c d)))
  | sixBad {s b c d r} : Step s b r → r ≠ atom 0 → r ≠ atom 1 →
      Crash s (cell (atom 6) (cell b (cell c d)))
  | sixYes {s b c d} : Step s b (atom 0) → Crash s c → Crash s (cell (atom 6) (cell b (cell c d)))
  | sixNo {s b c d} : Step s b (atom 1) → Crash s d → Crash s (cell (atom 6) (cell b (cell c d)))
  | sevenB {s b c} : Crash s b → Crash s (cell (atom 7) (cell b c))
  | sevenC {s b c s'} : Step s b s' → Crash s' c → Crash s (cell (atom 7) (cell b c))
  | eightB {s b c} : Crash s b → Crash s (cell (atom 8) (cell b c))
  | eightC {s b c p} : Step s b p → Crash (cell p s) c → Crash s (cell (atom 8) (cell b c))
  | nineC {s a c} : Crash s c → Crash s (cell (atom 9) (cell (atom a) c))
  | nineAxis {s a c core} : Step s c core → axis a core = none →
      Crash s (cell (atom 9) (cell (atom a) c))
  | nineR {s a c core f'} : Step s c core → axis a core = some f' → Crash core f' →
      Crash s (cell (atom 9) (cell (atom a) c))
  | tenD {s a c d} : Crash s d → Crash s (cell (atom 10) (cell (cell (atom a) c) d))
  | tenC {s a c d t} : Step s d t → Crash s c →
      Crash s (cell (atom 10) (cell (cell (atom a) c) d))
  | tenEdit {s a c d t p} : Step s d t → Step s c p → edit a p t = none →
      Crash s (cell (atom 10) (cell (cell (atom a) c) d))
  | hintS {s tag d} : Crash s d → Crash s (cell (atom 11) (cell (atom tag) d))
  | hintDC {s tag c d} : Crash s c → Crash s (cell (atom 11) (cell (cell (atom tag) c) d))
  | hintDD {s tag c d hv} : Step s c hv → Crash s d →
      Crash s (cell (atom 11) (cell (cell (atom tag) c) d))

/-! ## The interpreter -/

/-- An interpreter result: a value or a crash with the budget remaining, or
exhaustion. -/
inductive Res where
  | ok (v : Noun) (rem : Nat)
  | crash (rem : Nat)
  | exhausted
  deriving DecidableEq, Repr

def Res.bind : Res → (Noun → Nat → Res) → Res
  | .ok v r, k => k v r
  | .crash r, _ => .crash r
  | .exhausted, _ => .exhausted

/-- The fueled interpreter. `b` = step budget (one unit per rule applied);
`d` = structural depth bound (never binds first when `b ≤ d`). -/
def exec : Nat → Nat → Noun → Noun → Res
  | 0, _, _, _ => .exhausted
  | _ + 1, 0, _, _ => .exhausted
  | d + 1, b + 1, s, f =>
    match parse f with
    | none => .crash b
    | some (.cons x y z) =>
      (exec d b s (cell x y)).bind fun hv r => (exec d r s z).bind fun tv r' => .ok (cell hv tv) r'
    | some (.slot a) =>
      match axis a s with
      | some v => .ok v b
      | none => .crash b
    | some (.quote x) => .ok x b
    | some (.eval x y) =>
      (exec d b s x).bind fun s' r => (exec d r s y).bind fun f' r' => exec d r' s' f'
    | some (.wut x) => (exec d b s x).bind fun v r => .ok (loob v.isCell) r
    | some (.lus x) =>
      (exec d b s x).bind fun v r =>
        match v with
        | atom n => .ok (atom (n + 1)) r
        | cell _ _ => .crash r
    | some (.tis x y) =>
      (exec d b s x).bind fun v r => (exec d r s y).bind fun w r' => .ok (loob (decide (v = w))) r'
    | some (.six x y z) =>
      (exec d b s x).bind fun v r =>
        match v with
        | atom 0 => exec d r s y
        | atom 1 => exec d r s z
        | _ => .crash r
    | some (.seven x y) => (exec d b s x).bind fun s' r => exec d r s' y
    | some (.eight x y) => (exec d b s x).bind fun p r => exec d r (cell p s) y
    | some (.nine a c) =>
      (exec d b s c).bind fun core r =>
        match axis a core with
        | some f' => exec d r core f'
        | none => .crash r
    | some (.ten a c z) =>
      (exec d b s z).bind fun t r => (exec d r s c).bind fun p r' =>
        match edit a p t with
        | some v => .ok v r'
        | none => .crash r'
    | some (.hintS _ z) => exec d b s z
    | some (.hintD _ c z) => (exec d b s c).bind fun _ r => exec d r s z

inductive Outcome where
  | crash
  | exhausted
  deriving DecidableEq, Repr

/-- `*[s f]` with a budget of `fuel` rule applications. -/
def run (fuel : Nat) (s f : Noun) : Except Outcome Noun :=
  match exec fuel fuel s f with
  | .ok v _ => .ok v
  | .crash _ => .error .crash
  | .exhausted => .error .exhausted

/-- Rule applications performed (the metered count): for an answer or a crash,
the budget spent; for exhaustion, all of it. -/
def steps (fuel : Nat) (s f : Noun) : Nat :=
  match exec fuel fuel s f with
  | .ok _ r => fuel - r
  | .crash r => fuel - r
  | .exhausted => fuel

/-- NockApp's slam formula (`crates/nockapp/src/noun/ops.rs:31-34`):
`[8 [9 arm 0 2] 9 2 10 [6 0 7] 0 2]`. -/
def slam (arm : Nat) : Noun :=
  op 8 (cell (op 9 (cell (atom arm) (op 0 (atom 2))))
    (op 9 (cell (atom 2) (op 10 (cell (cell (atom 6) (op 0 (atom 7))) (op 0 (atom 2)))))))


/-! ## Decoder facts -/

def Form.toNoun : Form → Noun
  | .cons b c d => cell (cell b c) d
  | .slot a => cell (atom 0) (atom a)
  | .quote x => cell (atom 1) x
  | .eval b c => cell (atom 2) (cell b c)
  | .wut b => cell (atom 3) b
  | .lus b => cell (atom 4) b
  | .tis b c => cell (atom 5) (cell b c)
  | .six b c d => cell (atom 6) (cell b (cell c d))
  | .seven b c => cell (atom 7) (cell b c)
  | .eight b c => cell (atom 8) (cell b c)
  | .nine a c => cell (atom 9) (cell (atom a) c)
  | .ten a c d => cell (atom 10) (cell (cell (atom a) c) d)
  | .hintS t d => cell (atom 11) (cell (atom t) d)
  | .hintD t c d => cell (atom 11) (cell (cell (atom t) c) d)

theorem parse_some {f : Noun} {x : Form} (h : parse f = some x) : f = x.toNoun := by
  unfold parse at h
  split at h <;> cases h <;> rfl

theorem parse_toNoun (x : Form) : parse x.toNoun = some x := by
  cases x <;> rfl

/-! ## `Res` plumbing -/

theorem Res.bind_eq_ok {x : Res} {k : Noun → Nat → Res} {v : Noun} {r : Nat} :
    x.bind k = .ok v r ↔ ∃ v₁ r₁, x = .ok v₁ r₁ ∧ k v₁ r₁ = .ok v r := by
  cases x <;> simp [Res.bind]

theorem Res.bind_eq_crash {x : Res} {k : Noun → Nat → Res} {r : Nat} :
    x.bind k = .crash r ↔ x = .crash r ∨ ∃ v₁ r₁, x = .ok v₁ r₁ ∧ k v₁ r₁ = .crash r := by
  cases x <;> simp [Res.bind]

def Res.shift (j : Nat) : Res → Res
  | .ok v r => .ok v (r + j)
  | .crash r => .crash (r + j)
  | .exhausted => .exhausted

theorem Res.bind_shift {x x' : Res} {k k' : Noun → Nat → Res} {j : Nat}
    (hne : x.bind k ≠ .exhausted) (hx : x ≠ .exhausted → x' = x.shift j)
    (hk : ∀ v r, x = .ok v r → k v r ≠ .exhausted → k' v (r + j) = (k v r).shift j) :
    x'.bind k' = (x.bind k).shift j := by
  cases x with
  | exhausted => simp [Res.bind] at hne
  | ok v r =>
    rw [hx (by simp)]
    exact hk v r rfl hne
  | crash r => rw [hx (by simp)]; rfl

theorem Res.bind_ne_exhausted {x : Res} {k : Noun → Nat → Res} (h : x.bind k ≠ .exhausted) :
    x ≠ .exhausted := by
  intro hx; subst hx; exact h rfl

/-! ## More fuel never changes an answer -/

/-- Extra depth and `j` extra budget shift the remaining budget by `j` and
change nothing else, unless the smaller run was exhausted. -/
theorem exec_shift : ∀ (d d' : Nat), d ≤ d' → ∀ (b j : Nat) (s f : Noun),
    exec d b s f ≠ .exhausted → exec d' (b + j) s f = (exec d b s f).shift j
  | 0, _, _, _, _, _, _, h => by simp [exec] at h
  | _ + 1, _, _, 0, _, _, _, h => by simp [exec] at h
  | d + 1, d' + 1, hd, b + 1, j, s, f, h => by
    have IH : ∀ (b j : Nat) (s f : Noun), exec d b s f ≠ .exhausted →
        exec d' (b + j) s f = (exec d b s f).shift j :=
      exec_shift d d' (by omega)
    rw [show b + 1 + j = (b + j) + 1 by omega]
    simp only [exec] at h ⊢
    cases hp : parse f with
    | none => rfl
    | some x =>
      simp only [hp] at h ⊢
      cases x with
      | cons x y z =>
        exact Res.bind_shift h (IH _ _ _ _) fun v r _ hk =>
          Res.bind_shift hk (IH _ _ _ _) fun _ _ _ _ => rfl
      | slot a => simp only; split <;> rfl
      | quote x => rfl
      | eval x y =>
        exact Res.bind_shift h (IH _ _ _ _) fun v r _ hk =>
          Res.bind_shift hk (IH _ _ _ _) fun _ _ _ hk' => IH _ _ _ _ hk'
      | wut x => exact Res.bind_shift h (IH _ _ _ _) fun _ _ _ _ => rfl
      | lus x => exact Res.bind_shift h (IH _ _ _ _) fun v _ _ _ => by cases v <;> rfl
      | tis x y =>
        exact Res.bind_shift h (IH _ _ _ _) fun v r _ hk =>
          Res.bind_shift hk (IH _ _ _ _) fun _ _ _ _ => rfl
      | six x y z =>
        exact Res.bind_shift h (IH _ _ _ _) fun v r _ hk => by
          rcases v with (_ | _ | n) | _
          · exact IH _ _ _ _ hk
          · exact IH _ _ _ _ hk
          · rfl
          · rfl
      | seven x y => exact Res.bind_shift h (IH _ _ _ _) fun _ _ _ hk => IH _ _ _ _ hk
      | eight x y => exact Res.bind_shift h (IH _ _ _ _) fun _ _ _ hk => IH _ _ _ _ hk
      | nine a c =>
        exact Res.bind_shift h (IH _ _ _ _) fun core r _ hk => by
          split
          · rename_i heq; rw [heq] at hk; exact IH _ _ _ _ hk
          · rfl
      | ten a c z =>
        exact Res.bind_shift h (IH _ _ _ _) fun t r _ hk =>
          Res.bind_shift hk (IH _ _ _ _) fun p r' _ _ => by
            split <;> rfl
      | hintS t z => exact IH _ _ _ _ h
      | hintD t c z => exact Res.bind_shift h (IH _ _ _ _) fun _ _ _ hk => IH _ _ _ _ hk

/-! ## Soundness: every answer is a derivation, every crash a `Crash` -/

theorem exec_sound : ∀ (d b : Nat) (s f : Noun),
    (∀ v r, exec d b s f = .ok v r → Step s f v) ∧ (∀ r, exec d b s f = .crash r → Crash s f)
  | 0, _, _, _ => ⟨fun _ _ h => by simp [exec] at h, fun _ h => by simp [exec] at h⟩
  | _ + 1, 0, _, _ => ⟨fun _ _ h => by simp [exec] at h, fun _ h => by simp [exec] at h⟩
  | d + 1, b + 1, s, f => by
    have IH := exec_sound d
    cases hp : parse f with
    | none =>
      refine ⟨fun v r h => ?_, fun r _ => Crash.malformed hp⟩
      simp [exec, hp] at h
    | some x =>
      have hf := parse_some hp
      subst hf
      simp only [exec, hp]
      cases x with
      | cons x y z =>
        refine ⟨fun v r h => ?_, fun r h => ?_⟩
        · obtain ⟨hv, r1, h1, h2⟩ := Res.bind_eq_ok.mp h
          obtain ⟨tv, r2, h3, h4⟩ := Res.bind_eq_ok.mp h2
          cases h4
          exact Step.cons ((IH _ _ _).1 _ _ h1) ((IH _ _ _).1 _ _ h3)
        · rcases Res.bind_eq_crash.mp h with h1 | ⟨hv, r1, h1, h2⟩
          · exact Crash.consHd ((IH _ _ _).2 _ h1)
          · rcases Res.bind_eq_crash.mp h2 with h3 | ⟨tv, r2, h3, h4⟩
            · exact Crash.consTl ((IH _ _ _).1 _ _ h1) ((IH _ _ _).2 _ h3)
            · cases h4
      | slot a =>
        refine ⟨fun v r h => ?_, fun r h => ?_⟩
        · simp only at h; split at h
          · rename_i hax; cases h; exact Step.slot hax
          · cases h
        · simp only at h; split at h
          · cases h
          · rename_i hax; exact Crash.slot hax
      | quote x =>
        refine ⟨fun v r h => ?_, fun r h => ?_⟩
        · cases h; exact Step.quote
        · cases h
      | eval x y =>
        refine ⟨fun v r h => ?_, fun r h => ?_⟩
        · obtain ⟨s', r1, h1, h2⟩ := Res.bind_eq_ok.mp h
          obtain ⟨f', r2, h3, h4⟩ := Res.bind_eq_ok.mp h2
          exact Step.eval ((IH _ _ _).1 _ _ h1) ((IH _ _ _).1 _ _ h3) ((IH _ _ _).1 _ _ h4)
        · rcases Res.bind_eq_crash.mp h with h1 | ⟨s', r1, h1, h2⟩
          · exact Crash.evalB ((IH _ _ _).2 _ h1)
          · rcases Res.bind_eq_crash.mp h2 with h3 | ⟨f', r2, h3, h4⟩
            · exact Crash.evalC ((IH _ _ _).1 _ _ h1) ((IH _ _ _).2 _ h3)
            · exact Crash.evalR ((IH _ _ _).1 _ _ h1) ((IH _ _ _).1 _ _ h3) ((IH _ _ _).2 _ h4)
      | wut x =>
        refine ⟨fun v r h => ?_, fun r h => ?_⟩
        · obtain ⟨w, r1, h1, h2⟩ := Res.bind_eq_ok.mp h
          cases h2; exact Step.wut ((IH _ _ _).1 _ _ h1)
        · rcases Res.bind_eq_crash.mp h with h1 | ⟨w, r1, h1, h2⟩
          · exact Crash.wut ((IH _ _ _).2 _ h1)
          · cases h2
      | lus x =>
        refine ⟨fun v r h => ?_, fun r h => ?_⟩
        · obtain ⟨w, r1, h1, h2⟩ := Res.bind_eq_ok.mp h
          cases w with
          | atom n => cases h2; exact Step.lus ((IH _ _ _).1 _ _ h1)
          | cell => cases h2
        · rcases Res.bind_eq_crash.mp h with h1 | ⟨w, r1, h1, h2⟩
          · exact Crash.lus ((IH _ _ _).2 _ h1)
          · cases w with
            | atom n => cases h2
            | cell => exact Crash.lusCell ((IH _ _ _).1 _ _ h1)
      | tis x y =>
        refine ⟨fun v r h => ?_, fun r h => ?_⟩
        · obtain ⟨w1, r1, h1, h2⟩ := Res.bind_eq_ok.mp h
          obtain ⟨w2, r2, h3, h4⟩ := Res.bind_eq_ok.mp h2
          cases h4; exact Step.tis ((IH _ _ _).1 _ _ h1) ((IH _ _ _).1 _ _ h3)
        · rcases Res.bind_eq_crash.mp h with h1 | ⟨w1, r1, h1, h2⟩
          · exact Crash.tisB ((IH _ _ _).2 _ h1)
          · rcases Res.bind_eq_crash.mp h2 with h3 | ⟨w2, r2, h3, h4⟩
            · exact Crash.tisC ((IH _ _ _).1 _ _ h1) ((IH _ _ _).2 _ h3)
            · cases h4
      | six x y z =>
        refine ⟨fun v r h => ?_, fun r h => ?_⟩
        · obtain ⟨w, r1, h1, h2⟩ := Res.bind_eq_ok.mp h
          rcases w with (_ | _ | n) | _
          · exact Step.sixYes ((IH _ _ _).1 _ _ h1) ((IH _ _ _).1 _ _ h2)
          · exact Step.sixNo ((IH _ _ _).1 _ _ h1) ((IH _ _ _).1 _ _ h2)
          · cases h2
          · cases h2
        · rcases Res.bind_eq_crash.mp h with h1 | ⟨w, r1, h1, h2⟩
          · exact Crash.sixT ((IH _ _ _).2 _ h1)
          · rcases w with (_ | _ | n) | _
            · exact Crash.sixYes ((IH _ _ _).1 _ _ h1) ((IH _ _ _).2 _ h2)
            · exact Crash.sixNo ((IH _ _ _).1 _ _ h1) ((IH _ _ _).2 _ h2)
            · exact Crash.sixBad ((IH _ _ _).1 _ _ h1) (by simp) (by simp)
            · exact Crash.sixBad ((IH _ _ _).1 _ _ h1) (by simp) (by simp)
      | seven x y =>
        refine ⟨fun v r h => ?_, fun r h => ?_⟩
        · obtain ⟨s', r1, h1, h2⟩ := Res.bind_eq_ok.mp h
          exact Step.seven ((IH _ _ _).1 _ _ h1) ((IH _ _ _).1 _ _ h2)
        · rcases Res.bind_eq_crash.mp h with h1 | ⟨s', r1, h1, h2⟩
          · exact Crash.sevenB ((IH _ _ _).2 _ h1)
          · exact Crash.sevenC ((IH _ _ _).1 _ _ h1) ((IH _ _ _).2 _ h2)
      | eight x y =>
        refine ⟨fun v r h => ?_, fun r h => ?_⟩
        · obtain ⟨p, r1, h1, h2⟩ := Res.bind_eq_ok.mp h
          exact Step.eight ((IH _ _ _).1 _ _ h1) ((IH _ _ _).1 _ _ h2)
        · rcases Res.bind_eq_crash.mp h with h1 | ⟨p, r1, h1, h2⟩
          · exact Crash.eightB ((IH _ _ _).2 _ h1)
          · exact Crash.eightC ((IH _ _ _).1 _ _ h1) ((IH _ _ _).2 _ h2)
      | nine a c =>
        refine ⟨fun v r h => ?_, fun r h => ?_⟩
        · obtain ⟨core, r1, h1, h2⟩ := Res.bind_eq_ok.mp h
          split at h2
          · rename_i f' hax; exact Step.nine ((IH _ _ _).1 _ _ h1) hax ((IH _ _ _).1 _ _ h2)
          · cases h2
        · rcases Res.bind_eq_crash.mp h with h1 | ⟨core, r1, h1, h2⟩
          · exact Crash.nineC ((IH _ _ _).2 _ h1)
          · split at h2
            · rename_i f' hax; exact Crash.nineR ((IH _ _ _).1 _ _ h1) hax ((IH _ _ _).2 _ h2)
            · rename_i hax; exact Crash.nineAxis ((IH _ _ _).1 _ _ h1) hax
      | ten a c z =>
        refine ⟨fun v r h => ?_, fun r h => ?_⟩
        · obtain ⟨t, r1, h1, h2⟩ := Res.bind_eq_ok.mp h
          obtain ⟨p, r2, h3, h4⟩ := Res.bind_eq_ok.mp h2
          split at h4
          · rename_i w hed; cases h4; exact Step.ten ((IH _ _ _).1 _ _ h1) ((IH _ _ _).1 _ _ h3) hed
          · cases h4
        · rcases Res.bind_eq_crash.mp h with h1 | ⟨t, r1, h1, h2⟩
          · exact Crash.tenD ((IH _ _ _).2 _ h1)
          · rcases Res.bind_eq_crash.mp h2 with h3 | ⟨p, r2, h3, h4⟩
            · exact Crash.tenC ((IH _ _ _).1 _ _ h1) ((IH _ _ _).2 _ h3)
            · split at h4
              · cases h4
              · rename_i hed; exact Crash.tenEdit ((IH _ _ _).1 _ _ h1) ((IH _ _ _).1 _ _ h3) hed
      | hintS t z =>
        exact ⟨fun v r h => Step.hintS ((IH _ _ _).1 _ _ h), fun r h => Crash.hintS ((IH _ _ _).2 _ h)⟩
      | hintD t c z =>
        refine ⟨fun v r h => ?_, fun r h => ?_⟩
        · obtain ⟨hv, r1, h1, h2⟩ := Res.bind_eq_ok.mp h
          exact Step.hintD ((IH _ _ _).1 _ _ h1) ((IH _ _ _).1 _ _ h2)
        · rcases Res.bind_eq_crash.mp h with h1 | ⟨hv, r1, h1, h2⟩
          · exact Crash.hintDC ((IH _ _ _).2 _ h1)
          · exact Crash.hintDD ((IH _ _ _).1 _ _ h1) ((IH _ _ _).2 _ h2)

/-! ## Completeness: every derivation is reached by some fuel, in a fixed number of steps -/

/-- `*[s f] = v` in exactly `n` steps, at every budget `≥ n` and depth `≥ n`. -/
def Runs (s f v : Noun) (n : Nat) : Prop :=
  ∀ d b, n ≤ b → n ≤ d → exec d b s f = .ok v (b - n)

/-- `*[s f]` crashes after exactly `n` steps, at every budget and depth `≥ n`. -/
def CrashRuns (s f : Noun) (n : Nat) : Prop :=
  ∀ d b, n ≤ b → n ≤ d → exec d b s f = .crash (b - n)

theorem Runs.of_succ {s f v : Noun} {n : Nat}
    (h : ∀ d b, n ≤ b → n ≤ d → exec (d + 1) (b + 1) s f = .ok v (b - n)) : Runs s f v (n + 1) := by
  intro d b hb hd
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [h d b (by omega) (by omega)]; congr 1; omega

theorem CrashRuns.of_succ {s f : Noun} {n : Nat}
    (h : ∀ d b, n ≤ b → n ≤ d → exec (d + 1) (b + 1) s f = .crash (b - n)) : CrashRuns s f (n + 1) := by
  intro d b hb hd
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [h d b (by omega) (by omega)]; congr 1; omega

theorem step_runs {s f v : Noun} (h : Step s f v) : ∃ n, Runs s f v n := by
  induction h with
  | @cons s x y z hv tv _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
    refine ⟨n1 + n2 + 1, Runs.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (cell x y) z) = some (.cons x y z) := parse_toNoun (.cons x y z)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega
  | @slot s a v hax =>
    refine ⟨0 + 1, Runs.of_succ fun d b _ _ => ?_⟩
    have hp : parse (cell (atom 0) (atom a)) = some (.slot a) := parse_toNoun (.slot a)
    simp only [exec, hp, hax, Nat.sub_zero]
  | @quote s x =>
    refine ⟨0 + 1, Runs.of_succ fun d b _ _ => ?_⟩
    have hp : parse (cell (atom 1) x) = some (.quote x) := parse_toNoun (.quote x)
    simp only [exec, hp, Nat.sub_zero]
  | @eval s x y s' f' v _ _ _ ih1 ih2 ih3 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2; obtain ⟨n3, h3⟩ := ih3
    refine ⟨n1 + n2 + n3 + 1, Runs.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 2) (cell x y)) = some (.eval x y) := parse_toNoun (.eval x y)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega), h3 d (b - n1 - n2) (by omega) (by omega)]
    congr 1; omega
  | @wut s x r _ ih1 =>
    obtain ⟨n1, h1⟩ := ih1
    refine ⟨n1 + 1, Runs.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 3) x) = some (.wut x) := parse_toNoun (.wut x)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega)]
  | @lus s x n _ ih1 =>
    obtain ⟨n1, h1⟩ := ih1
    refine ⟨n1 + 1, Runs.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 4) x) = some (.lus x) := parse_toNoun (.lus x)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega)]
  | @tis s x y v w _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
    refine ⟨n1 + n2 + 1, Runs.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 5) (cell x y)) = some (.tis x y) := parse_toNoun (.tis x y)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega
  | @sixYes s x y z v _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
    refine ⟨n1 + n2 + 1, Runs.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 6) (cell x (cell y z))) = some (.six x y z) :=
      parse_toNoun (.six x y z)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega
  | @sixNo s x y z v _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
    refine ⟨n1 + n2 + 1, Runs.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 6) (cell x (cell y z))) = some (.six x y z) :=
      parse_toNoun (.six x y z)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega
  | @seven s x y s' v _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
    refine ⟨n1 + n2 + 1, Runs.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 7) (cell x y)) = some (.seven x y) := parse_toNoun (.seven x y)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega
  | @eight s x y p v _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
    refine ⟨n1 + n2 + 1, Runs.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 8) (cell x y)) = some (.eight x y) := parse_toNoun (.eight x y)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega
  | @nine s a c core f' v _ hax _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
    refine ⟨n1 + n2 + 1, Runs.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 9) (cell (atom a) c)) = some (.nine a c) :=
      parse_toNoun (.nine a c)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega), hax,
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega
  | @ten s a c z t p v _ _ hed ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
    refine ⟨n1 + n2 + 1, Runs.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 10) (cell (cell (atom a) c) z)) = some (.ten a c z) :=
      parse_toNoun (.ten a c z)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega), hed]
    congr 1; omega
  | @hintS s tag z v _ ih1 =>
    obtain ⟨n1, h1⟩ := ih1
    refine ⟨n1 + 1, Runs.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 11) (cell (atom tag) z)) = some (.hintS tag z) :=
      parse_toNoun (.hintS tag z)
    simp only [exec, hp, h1 d b (by omega) (by omega)]
  | @hintD s tag c z hv v _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1; obtain ⟨n2, h2⟩ := ih2
    refine ⟨n1 + n2 + 1, Runs.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 11) (cell (cell (atom tag) c) z)) = some (.hintD tag c z) :=
      parse_toNoun (.hintD tag c z)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega

theorem crash_runs {s f : Noun} (h : Crash s f) : ∃ n, CrashRuns s f n := by
  induction h with
  | @malformed s f hp =>
    exact ⟨0 + 1, CrashRuns.of_succ fun d b _ _ => by simp only [exec, hp, Nat.sub_zero]⟩
  | @consHd s x y z _ ih =>
    obtain ⟨n1, h1⟩ := ih
    refine ⟨n1 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (cell x y) z) = some (.cons x y z) := parse_toNoun (.cons x y z)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega)]
  | @consTl s x y z hv hs _ ih =>
    obtain ⟨n1, h1⟩ := step_runs hs; obtain ⟨n2, h2⟩ := ih
    refine ⟨n1 + n2 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (cell x y) z) = some (.cons x y z) := parse_toNoun (.cons x y z)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega
  | @slot s a hax =>
    refine ⟨0 + 1, CrashRuns.of_succ fun d b _ _ => ?_⟩
    have hp : parse (cell (atom 0) (atom a)) = some (.slot a) := parse_toNoun (.slot a)
    simp only [exec, hp, hax, Nat.sub_zero]
  | @evalB s x y _ ih =>
    obtain ⟨n1, h1⟩ := ih
    refine ⟨n1 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 2) (cell x y)) = some (.eval x y) := parse_toNoun (.eval x y)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega)]
  | @evalC s x y s' hs _ ih =>
    obtain ⟨n1, h1⟩ := step_runs hs; obtain ⟨n2, h2⟩ := ih
    refine ⟨n1 + n2 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 2) (cell x y)) = some (.eval x y) := parse_toNoun (.eval x y)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega
  | @evalR s x y s' f' hs1 hs2 _ ih =>
    obtain ⟨n1, h1⟩ := step_runs hs1; obtain ⟨n2, h2⟩ := step_runs hs2; obtain ⟨n3, h3⟩ := ih
    refine ⟨n1 + n2 + n3 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 2) (cell x y)) = some (.eval x y) := parse_toNoun (.eval x y)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega), h3 d (b - n1 - n2) (by omega) (by omega)]
    congr 1; omega
  | @wut s x _ ih =>
    obtain ⟨n1, h1⟩ := ih
    refine ⟨n1 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 3) x) = some (.wut x) := parse_toNoun (.wut x)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega)]
  | @lus s x _ ih =>
    obtain ⟨n1, h1⟩ := ih
    refine ⟨n1 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 4) x) = some (.lus x) := parse_toNoun (.lus x)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega)]
  | @lusCell s x p q hs =>
    obtain ⟨n1, h1⟩ := step_runs hs
    refine ⟨n1 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 4) x) = some (.lus x) := parse_toNoun (.lus x)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega)]
  | @tisB s x y _ ih =>
    obtain ⟨n1, h1⟩ := ih
    refine ⟨n1 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 5) (cell x y)) = some (.tis x y) := parse_toNoun (.tis x y)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega)]
  | @tisC s x y w hs _ ih =>
    obtain ⟨n1, h1⟩ := step_runs hs; obtain ⟨n2, h2⟩ := ih
    refine ⟨n1 + n2 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 5) (cell x y)) = some (.tis x y) := parse_toNoun (.tis x y)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega
  | @sixT s x y z _ ih =>
    obtain ⟨n1, h1⟩ := ih
    refine ⟨n1 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 6) (cell x (cell y z))) = some (.six x y z) :=
      parse_toNoun (.six x y z)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega)]
  | @sixBad s x y z r hs h0 h1' =>
    obtain ⟨n1, h1⟩ := step_runs hs
    refine ⟨n1 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 6) (cell x (cell y z))) = some (.six x y z) :=
      parse_toNoun (.six x y z)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega)]
  | @sixYes s x y z hs _ ih =>
    obtain ⟨n1, h1⟩ := step_runs hs; obtain ⟨n2, h2⟩ := ih
    refine ⟨n1 + n2 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 6) (cell x (cell y z))) = some (.six x y z) :=
      parse_toNoun (.six x y z)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega
  | @sixNo s x y z hs _ ih =>
    obtain ⟨n1, h1⟩ := step_runs hs; obtain ⟨n2, h2⟩ := ih
    refine ⟨n1 + n2 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 6) (cell x (cell y z))) = some (.six x y z) :=
      parse_toNoun (.six x y z)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega
  | @sevenB s x y _ ih =>
    obtain ⟨n1, h1⟩ := ih
    refine ⟨n1 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 7) (cell x y)) = some (.seven x y) := parse_toNoun (.seven x y)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega)]
  | @sevenC s x y s' hs _ ih =>
    obtain ⟨n1, h1⟩ := step_runs hs; obtain ⟨n2, h2⟩ := ih
    refine ⟨n1 + n2 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 7) (cell x y)) = some (.seven x y) := parse_toNoun (.seven x y)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega
  | @eightB s x y _ ih =>
    obtain ⟨n1, h1⟩ := ih
    refine ⟨n1 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 8) (cell x y)) = some (.eight x y) := parse_toNoun (.eight x y)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega)]
  | @eightC s x y p hs _ ih =>
    obtain ⟨n1, h1⟩ := step_runs hs; obtain ⟨n2, h2⟩ := ih
    refine ⟨n1 + n2 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 8) (cell x y)) = some (.eight x y) := parse_toNoun (.eight x y)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega
  | @nineC s a c _ ih =>
    obtain ⟨n1, h1⟩ := ih
    refine ⟨n1 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 9) (cell (atom a) c)) = some (.nine a c) :=
      parse_toNoun (.nine a c)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega)]
  | @nineAxis s a c core hs hax =>
    obtain ⟨n1, h1⟩ := step_runs hs
    refine ⟨n1 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 9) (cell (atom a) c)) = some (.nine a c) :=
      parse_toNoun (.nine a c)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega), hax]
  | @nineR s a c core f' hs hax _ ih =>
    obtain ⟨n1, h1⟩ := step_runs hs; obtain ⟨n2, h2⟩ := ih
    refine ⟨n1 + n2 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 9) (cell (atom a) c)) = some (.nine a c) :=
      parse_toNoun (.nine a c)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega), hax,
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega
  | @tenD s a c z _ ih =>
    obtain ⟨n1, h1⟩ := ih
    refine ⟨n1 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 10) (cell (cell (atom a) c) z)) = some (.ten a c z) :=
      parse_toNoun (.ten a c z)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega)]
  | @tenC s a c z t hs _ ih =>
    obtain ⟨n1, h1⟩ := step_runs hs; obtain ⟨n2, h2⟩ := ih
    refine ⟨n1 + n2 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 10) (cell (cell (atom a) c) z)) = some (.ten a c z) :=
      parse_toNoun (.ten a c z)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega
  | @tenEdit s a c z t p hs1 hs2 hed =>
    obtain ⟨n1, h1⟩ := step_runs hs1; obtain ⟨n2, h2⟩ := step_runs hs2
    refine ⟨n1 + n2 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 10) (cell (cell (atom a) c) z)) = some (.ten a c z) :=
      parse_toNoun (.ten a c z)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega), hed]
    congr 1; omega
  | @hintS s tag z _ ih =>
    obtain ⟨n1, h1⟩ := ih
    refine ⟨n1 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 11) (cell (atom tag) z)) = some (.hintS tag z) :=
      parse_toNoun (.hintS tag z)
    simp only [exec, hp, h1 d b (by omega) (by omega)]
  | @hintDC s tag c z _ ih =>
    obtain ⟨n1, h1⟩ := ih
    refine ⟨n1 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 11) (cell (cell (atom tag) c) z)) = some (.hintD tag c z) :=
      parse_toNoun (.hintD tag c z)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega)]
  | @hintDD s tag c z hv hs _ ih =>
    obtain ⟨n1, h1⟩ := step_runs hs; obtain ⟨n2, h2⟩ := ih
    refine ⟨n1 + n2 + 1, CrashRuns.of_succ fun d b hb hd => ?_⟩
    have hp : parse (cell (atom 11) (cell (cell (atom tag) c) z)) = some (.hintD tag c z) :=
      parse_toNoun (.hintD tag c z)
    simp only [exec, hp, Res.bind, h1 d b (by omega) (by omega),
      h2 d (b - n1) (by omega) (by omega)]
    congr 1; omega


/-- The remaining budget never exceeds the budget given. -/
def Res.remLe (b : Nat) : Res → Prop
  | .ok _ r => r ≤ b
  | .crash r => r ≤ b
  | .exhausted => True

theorem Res.remLe.mono {a b : Nat} {x : Res} (h : x.remLe a) (hab : a ≤ b) : x.remLe b := by
  cases x <;> simp_all [Res.remLe] <;> omega

theorem Res.remLe.bind {b : Nat} {x : Res} {k : Noun → Nat → Res} (hx : x.remLe b)
    (hk : ∀ v r, x = .ok v r → (k v r).remLe r) : (x.bind k).remLe b := by
  cases x with
  | ok v r => exact (hk v r rfl).mono hx
  | crash r => exact hx
  | exhausted => trivial

theorem exec_rem_le : ∀ (d b : Nat) (s f : Noun), (exec d b s f).remLe b
  | 0, _, _, _ => trivial
  | _ + 1, 0, _, _ => trivial
  | d + 1, b + 1, s, f => by
    have IH := exec_rem_le d
    have IH' : ∀ s f, (exec d b s f).remLe (b + 1) := fun s f => (IH b s f).mono (by omega)
    simp only [exec]
    cases hp : parse f with
    | none => simp [Res.remLe]
    | some x =>
      cases x <;> dsimp only
      case cons x y z =>
        exact (IH' _ _).bind fun _ r _ => (IH r _ _).bind fun _ r' _ => by simp [Res.remLe]
      case slot a => split <;> simp [Res.remLe]
      case quote x => simp [Res.remLe]
      case eval x y => exact (IH' _ _).bind fun _ r _ => (IH r _ _).bind fun _ r' _ => IH _ _ _
      case wut x => exact (IH' _ _).bind fun _ r _ => by simp [Res.remLe]
      case lus x => exact (IH' _ _).bind fun v r _ => by cases v <;> simp [Res.remLe]
      case tis x y =>
        exact (IH' _ _).bind fun _ r _ => (IH r _ _).bind fun _ r' _ => by simp [Res.remLe]
      case six x y z =>
        exact (IH' _ _).bind fun v r _ => by
          rcases v with (_ | _ | n) | _
          · exact IH _ _ _
          · exact IH _ _ _
          · simp [Res.remLe]
          · simp [Res.remLe]
      case seven x y => exact (IH' _ _).bind fun _ r _ => IH _ _ _
      case eight x y => exact (IH' _ _).bind fun _ r _ => IH _ _ _
      case nine a c => exact (IH' _ _).bind fun core r _ => by split <;> first | exact IH _ _ _ | simp [Res.remLe]
      case ten a c z =>
        exact (IH' _ _).bind fun _ r _ => (IH r _ _).bind fun _ r' _ => by
          split <;> simp [Res.remLe]
      case hintS t z => exact IH' _ _
      case hintD t c z => exact (IH' _ _).bind fun _ r _ => IH _ _ _

/-! ## The interpreter against the spec -/

theorem run_eq_ok {fuel : Nat} {s f v : Noun} :
    run fuel s f = .ok v ↔ ∃ r, exec fuel fuel s f = .ok v r := by
  unfold run; split <;> simp_all

theorem run_eq_crash {fuel : Nat} {s f : Noun} :
    run fuel s f = .error .crash ↔ ∃ r, exec fuel fuel s f = .crash r := by
  unfold run; split <;> simp_all

theorem run_eq_exhausted {fuel : Nat} {s f : Noun} :
    run fuel s f = .error .exhausted ↔ exec fuel fuel s f = .exhausted := by
  unfold run; split <;> simp_all

/-- **Soundness**: an answer of the interpreter is a derivation of the spec. -/
theorem run_sound {fuel : Nat} {s f v : Noun} (h : run fuel s f = .ok v) : Step s f v := by
  obtain ⟨r, hr⟩ := run_eq_ok.mp h
  exact (exec_sound _ _ _ _).1 _ _ hr

/-- **Completeness**: every derivation is reached, in a step count `n` that
depends only on the term, at every fuel `≥ n`. -/
theorem run_complete {s f v : Noun} (h : Step s f v) :
    ∃ n, ∀ fuel, n ≤ fuel → run fuel s f = .ok v ∧ steps fuel s f = n := by
  obtain ⟨n, hn⟩ := step_runs h
  refine ⟨n, fun fuel hf => ?_⟩
  have := hn fuel fuel hf hf
  refine ⟨run_eq_ok.mpr ⟨_, this⟩, ?_⟩
  simp only [steps, this]; omega

/-- A crash of the interpreter is a `Crash` of the spec. -/
theorem run_crash_sound {fuel : Nat} {s f : Noun} (h : run fuel s f = .error .crash) :
    Crash s f := by
  obtain ⟨r, hr⟩ := run_eq_crash.mp h
  exact (exec_sound _ _ _ _).2 _ hr

/-- Every `Crash` is reached, after a term-determined step count. -/
theorem run_crash_complete {s f : Noun} (h : Crash s f) :
    ∃ n, ∀ fuel, n ≤ fuel → run fuel s f = .error .crash ∧ steps fuel s f = n := by
  obtain ⟨n, hn⟩ := crash_runs h
  refine ⟨n, fun fuel hf => ?_⟩
  have := hn fuel fuel hf hf
  refine ⟨run_eq_crash.mpr ⟨_, this⟩, ?_⟩
  simp only [steps, this]; omega

/-- **A crash is a property of the term, not of the fuel.** -/
theorem run_crash_iff {s f : Noun} : (∃ fuel, run fuel s f = .error .crash) ↔ Crash s f := by
  constructor
  · rintro ⟨fuel, h⟩; exact run_crash_sound h
  · intro h
    obtain ⟨n, hn⟩ := run_crash_complete h
    exact ⟨n, (hn n le_rfl).1⟩

/-- A term that crashes has no value. -/
theorem crash_not_step {s f v : Noun} (hc : Crash s f) (hs : Step s f v) : False := by
  obtain ⟨n, hn⟩ := crash_runs hc
  obtain ⟨m, hm⟩ := step_runs hs
  have h1 := hn (n + m) (n + m) (by omega) (by omega)
  rw [hm (n + m) (n + m) (by omega) (by omega)] at h1
  cases h1

/-- `Step` is a function of `(s, f)`. -/
theorem step_deterministic {s f v v' : Noun} (h : Step s f v) (h' : Step s f v') : v = v' := by
  obtain ⟨n, hn⟩ := step_runs h
  obtain ⟨m, hm⟩ := step_runs h'
  have h1 := hn (n + m) (n + m) (by omega) (by omega)
  rw [hm (n + m) (n + m) (by omega) (by omega)] at h1
  exact (Res.ok.inj h1).1.symm

/-- **More fuel never changes an answer.** -/
theorem run_fuel_monotone {fuel fuel' : Nat} {s f v : Noun} (h : run fuel s f = .ok v)
    (hle : fuel ≤ fuel') : run fuel' s f = .ok v := by
  obtain ⟨r, hr⟩ := run_eq_ok.mp h
  have := exec_shift fuel fuel' hle fuel (fuel' - fuel) s f (by rw [hr]; simp)
  rw [Nat.add_sub_cancel' hle, hr] at this
  exact run_eq_ok.mpr ⟨_, this⟩

/-- More fuel never turns a crash into anything else. -/
theorem run_crash_monotone {fuel fuel' : Nat} {s f : Noun} (h : run fuel s f = .error .crash)
    (hle : fuel ≤ fuel') : run fuel' s f = .error .crash := by
  obtain ⟨r, hr⟩ := run_eq_crash.mp h
  have := exec_shift fuel fuel' hle fuel (fuel' - fuel) s f (by rw [hr]; simp)
  rw [Nat.add_sub_cancel' hle, hr] at this
  exact run_eq_crash.mpr ⟨_, this⟩

/-- The metered count of a finished run does not depend on the fuel. -/
theorem steps_stable {fuel fuel' : Nat} {s f : Noun} (h : run fuel s f ≠ .error .exhausted)
    (hle : fuel ≤ fuel') : steps fuel' s f = steps fuel s f := by
  have hne : exec fuel fuel s f ≠ .exhausted := fun he => h (run_eq_exhausted.mpr he)
  have := exec_shift fuel fuel' hle fuel (fuel' - fuel) s f hne
  rw [Nat.add_sub_cancel' hle] at this
  unfold steps
  rw [this]
  cases hx : exec fuel fuel s f with
  | ok v r =>
    simp only [Res.shift]
    have hr : r ≤ fuel := by
      have := exec_rem_le fuel fuel s f; rw [hx] at this; exact this
    omega
  | crash r =>
    simp only [Res.shift]
    have hr : r ≤ fuel := by
      have := exec_rem_le fuel fuel s f; rw [hx] at this; exact this
    omega
  | exhausted => exact absurd hx hne

/-- **Exhaustion says nothing**: a term with a value, run out of fuel. -/
theorem exhausted_says_nothing :
    ∃ s f fuel v, run fuel s f = .error .exhausted ∧ Step s f v :=
  ⟨atom 42, op 4 (op 0 (atom 1)), 1, atom 43, by decide,
    Step.lus (Step.slot (by simp [axis, axisAux]))⟩

/-- `Reduces sf v` ≙ `*sf = v` on the cell `sf = [subject formula]`. -/
def Reduces (sf v : Noun) : Prop := ∃ s f, sf = cell s f ∧ Step s f v

theorem reduces_deterministic {sf v v' : Noun} (h : Reduces sf v) (h' : Reduces sf v') : v = v' := by
  obtain ⟨s, f, rfl, hs⟩ := h
  obtain ⟨s', f', he, hs'⟩ := h'
  cases he
  exact step_deterministic hs hs'

/-! ## The byte-level entry point (what the host and `nock-eval` call) -/

/-- Running a jammed `[subject formula]`. -/
inductive JamRun where
  | ok (steps : Nat) (out : List UInt8)
  | crash (steps : Nat)
  | exhausted (steps : Nat)
  | malformed
  deriving DecidableEq, Repr

def runJammed (fuel : Nat) (input : List UInt8) : JamRun :=
  match cue input with
  | some (cell s f) =>
    match exec fuel fuel s f with
    | .ok v r => .ok (fuel - r) (jam v)
    | .crash r => .crash (fuel - r)
    | .exhausted => .exhausted fuel
  | _ => .malformed

/-- An `ok` from the byte entry point is a derivation, and its output bytes are
the canonical jam of the value. -/
theorem runJammed_sound {fuel : Nat} {input out : List UInt8} {k : Nat}
    (h : runJammed fuel input = .ok k out) :
    ∃ s f v, cue input = some (cell s f) ∧ Step s f v ∧ out = jam v ∧ cue out = some v := by
  unfold runJammed at h
  split at h
  · rename_i s f hc
    split at h
    · rename_i v r he
      cases h
      exact ⟨s, f, v, hc, (exec_sound _ _ _ _).1 _ _ he, rfl, cue_jam v⟩
    · cases h
    · cases h
  · cases h

/-- A `crash` from the byte entry point is a `Crash` of the decoded term. -/
theorem runJammed_crash_sound {fuel : Nat} {input : List UInt8} {k : Nat}
    (h : runJammed fuel input = .crash k) : ∃ s f, cue input = some (cell s f) ∧ Crash s f := by
  unfold runJammed at h
  split at h
  · rename_i s f hc
    split at h
    · cases h
    · rename_i r he; exact ⟨s, f, hc, (exec_sound _ _ _ _).2 _ he⟩
    · cases h
  · cases h

/-! ## Divergence: exhaustion at every fuel -/

/-- `[2 [0 1] 0 1]` on itself: `*[a 2 [0 1] 0 1] = *[a a]`. -/
def loopF : Noun := op 2 (cell (op 0 (atom 1)) (op 0 (atom 1)))

theorem exec_loop : ∀ d b, exec d b loopF loopF = .exhausted
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | 1, _ + 1 => rfl
  | d + 2, 1 => rfl
  | d + 2, 2 => rfl
  | d + 2, b + 3 => by
    have hp : parse loopF = some (.eval (op 0 (atom 1)) (op 0 (atom 1))) :=
      parse_toNoun (.eval _ _)
    have h1 : exec (d + 1) (b + 2) loopF (op 0 (atom 1)) = .ok loopF (b + 1) := rfl
    have h2 : exec (d + 1) (b + 1) loopF (op 0 (atom 1)) = .ok loopF b := rfl
    rw [exec, hp]
    simp only [h1, h2, Res.bind]
    exact exec_loop (d + 1) b

theorem loop_exhausts (fuel : Nat) : run fuel loopF loopF = .error .exhausted :=
  run_eq_exhausted.mpr (exec_loop fuel fuel)

/-- The loop has no value and does not crash: exhaustion is all there is. -/
theorem loop_no_step (v : Noun) : ¬ Step loopF loopF v := fun h => by
  obtain ⟨n, hn⟩ := step_runs h
  have := hn n n le_rfl le_rfl
  rw [exec_loop] at this; cases this

theorem loop_no_crash : ¬ Crash loopF loopF := fun h => by
  obtain ⟨n, hn⟩ := crash_runs h
  have := hn n n le_rfl le_rfl
  rw [exec_loop] at this; cases this

/-! ## Poles: the classic terms, by `decide` -/

/-- `*[42 4 0 1] = 43` in 2 steps. -/
theorem pole_increment : run 10 (atom 42) (op 4 (op 0 (atom 1))) = .ok (atom 43) := by decide
theorem pole_increment_steps : steps 10 (atom 42) (op 4 (op 0 (atom 1))) = 2 := by decide

/-- `%9`: a core `[[4 0 3] 7]` whose arm at axis 2 increments the payload. -/
theorem pole_core_call :
    run 10 (cell (op 4 (op 0 (atom 3))) (atom 7)) (op 9 (cell (atom 2) (op 0 (atom 1)))) =
      .ok (atom 8) := by decide

/-- `%10`: `*[[1 2] 10 [2 1 9] 0 1] = [9 2]`. -/
theorem pole_edit :
    run 10 (cell (atom 1) (atom 2)) (op 10 (cell (cell (atom 2) (op 1 (atom 9))) (op 0 (atom 1)))) =
      .ok (cell (atom 9) (atom 2)) := by decide

/-- The decrement formula from Urbit's Nock documentation,
`[8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] 9 2 [0 2] [4 0 6] 0 7] 9 2 0 1]`. -/
def decF : Noun := (cell (atom 8) (cell (cell (atom 1) (atom 0)) (cell (atom 8) (cell (cell (atom 1) (cell (atom 6) (cell (cell (atom 5) (cell (cell (atom 0) (atom 7)) (cell (atom 4) (cell (atom 0) (atom 6))))) (cell (cell (atom 0) (atom 6)) (cell (atom 9) (cell (atom 2) (cell (cell (atom 0) (atom 2)) (cell (cell (atom 4) (cell (atom 0) (atom 6))) (cell (atom 0) (atom 7)))))))))) (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1))))))))

set_option maxRecDepth 20000 in
/-- Its jam (the constant NOCK-RUNNER compares against `nockvm`'s `jam`). -/
theorem decF_jam : jam decF = [65, 176, 216, 38, 139, 195, 46, 220, 18, 63, 204, 196, 110, 252, 26, 36, 67, 150, 200, 198, 155, 227, 193, 32, 25, 50, 25] := by decide
theorem decF_cue : cue [65, 176, 216, 38, 139, 195, 46, 220, 18, 63, 204, 196, 110, 252, 26, 36, 67, 150, 200, 198, 155, 227, 193, 32, 25, 50, 25] = some decF := by rw [← decF_jam]; exact cue_jam decF

theorem pole_decrement : run 100 (atom 3) decF = .ok (atom 2) := by decide
theorem pole_decrement_steps : steps 100 (atom 3) decF = 36 := by decide
/-- The refutable pole of exhaustion: the same run at fuel 5 is `exhausted`,
at 50 it answers. -/
theorem pole_decrement_exhausted_5 : run 5 (atom 3) decF = .error .exhausted := by decide
theorem pole_decrement_answers_50 : run 50 (atom 3) decF = .ok (atom 2) := by decide

/-- NockApp's slam: subject `[core sample]`, the core's arm 2 produces the gate
`[[4 0 6] 0 0]` (battery: increment the sample); slammed with 41. -/
theorem pole_slam :
    run 30 (cell (cell (op 1 (cell (op 4 (op 0 (atom 6))) (cell (atom 0) (atom 0)))) (atom 0))
      (atom 41)) (slam 2) = .ok (atom 42) := by decide

/-- `%6` picks its branch; `%5` compares; `%3` tests. -/
theorem pole_six_yes :
    run 10 (atom 0) (op 6 (cell (op 5 (cell (op 1 (atom 1)) (op 1 (atom 1))))
      (cell (op 1 (atom 7)) (op 1 (atom 8))))) = .ok (atom 7) := by decide
theorem pole_wut : run 10 (cell (atom 1) (atom 2)) (op 3 (op 0 (atom 1))) = .ok (atom 0) := by decide
theorem pole_hints_dropped :
    run 10 (atom 5) (op 11 (cell (cell (atom 1) (op 1 (atom 99))) (op 0 (atom 1)))) =
      .ok (atom 5) := by decide

/-! ## Poles: crashes (each a `Crash` of the spec and so no value) -/

theorem pole_axis_zero_crash : run 10 (atom 5) (op 0 (atom 0)) = .error .crash := by decide
theorem pole_axis_zero_no_value (v : Noun) : ¬ Step (atom 5) (op 0 (atom 0)) v :=
  fun h => crash_not_step (run_crash_sound pole_axis_zero_crash) h
theorem pole_lus_cell_crash :
    run 10 (cell (atom 1) (atom 2)) (op 4 (op 0 (atom 1))) = .error .crash := by decide
theorem pole_six_nonloobean_crash :
    run 10 (atom 0) (op 6 (cell (op 1 (atom 2)) (cell (op 1 (atom 3)) (op 1 (atom 4))))) =
      .error .crash := by decide
theorem pole_scry_refused : run 10 (atom 0) (op 12 (cell (op 1 (atom 0)) (op 1 (atom 0)))) =
    .error .crash := by decide
theorem pole_bad_opcode_crash : run 10 (atom 0) (op 13 (atom 0)) = .error .crash := by decide
theorem pole_atom_formula_crash : run 10 (atom 0) (atom 7) = .error .crash := by decide
/-- `nockvm` PANICS here (`edit_with_space`: "0 is not allowed as an edit axis"); the spec crashes. -/
theorem pole_edit_axis_zero_crash :
    run 10 (atom 1) (op 10 (cell (cell (atom 0) (op 1 (atom 9))) (op 0 (atom 1)))) =
      .error .crash := by decide
/-- A crashing clue in a dynamic hint crashes: nothing in a hint is skipped. -/
theorem pole_hint_clue_crash :
    run 10 (atom 5) (op 11 (cell (cell (atom 1) (op 0 (atom 0))) (op 0 (atom 1)))) =
      .error .crash := by decide


/-! ## Axiom pins -/

/-- info: 'Minidregg.Theory.Nock.parse_some' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms parse_some
/-- info: 'Minidregg.Theory.Nock.parse_toNoun' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms parse_toNoun
/-- info: 'Minidregg.Theory.Nock.Res.bind_eq_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Res.bind_eq_ok
/-- info: 'Minidregg.Theory.Nock.Res.bind_eq_crash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Res.bind_eq_crash
/-- info: 'Minidregg.Theory.Nock.Res.bind_shift' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Res.bind_shift
/-- info: 'Minidregg.Theory.Nock.Res.bind_ne_exhausted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Res.bind_ne_exhausted
/-- info: 'Minidregg.Theory.Nock.exec_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exec_shift
/-- info: 'Minidregg.Theory.Nock.exec_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exec_sound
/-- info: 'Minidregg.Theory.Nock.Runs.of_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Runs.of_succ
/-- info: 'Minidregg.Theory.Nock.CrashRuns.of_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CrashRuns.of_succ
/-- info: 'Minidregg.Theory.Nock.step_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_runs
/-- info: 'Minidregg.Theory.Nock.crash_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms crash_runs
/-- info: 'Minidregg.Theory.Nock.Res.remLe.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Res.remLe.mono
/-- info: 'Minidregg.Theory.Nock.Res.remLe.bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Res.remLe.bind
/-- info: 'Minidregg.Theory.Nock.exec_rem_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exec_rem_le
/-- info: 'Minidregg.Theory.Nock.run_eq_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_eq_ok
/-- info: 'Minidregg.Theory.Nock.run_eq_crash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_eq_crash
/-- info: 'Minidregg.Theory.Nock.run_eq_exhausted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms run_eq_exhausted
/-- info: 'Minidregg.Theory.Nock.run_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_sound
/-- info: 'Minidregg.Theory.Nock.run_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_complete
/-- info: 'Minidregg.Theory.Nock.run_crash_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_crash_sound
/-- info: 'Minidregg.Theory.Nock.run_crash_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_crash_complete
/-- info: 'Minidregg.Theory.Nock.run_crash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_crash_iff
/-- info: 'Minidregg.Theory.Nock.crash_not_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms crash_not_step
/-- info: 'Minidregg.Theory.Nock.step_deterministic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_deterministic
/-- info: 'Minidregg.Theory.Nock.run_fuel_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_fuel_monotone
/-- info: 'Minidregg.Theory.Nock.run_crash_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_crash_monotone
/-- info: 'Minidregg.Theory.Nock.steps_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms steps_stable
/-- info: 'Minidregg.Theory.Nock.exhausted_says_nothing' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms exhausted_says_nothing
/-- info: 'Minidregg.Theory.Nock.reduces_deterministic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reduces_deterministic
/-- info: 'Minidregg.Theory.Nock.runJammed_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runJammed_sound
/-- info: 'Minidregg.Theory.Nock.runJammed_crash_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runJammed_crash_sound
/-- info: 'Minidregg.Theory.Nock.exec_loop' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms exec_loop
/-- info: 'Minidregg.Theory.Nock.loop_exhausts' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms loop_exhausts
/-- info: 'Minidregg.Theory.Nock.loop_no_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loop_no_step
/-- info: 'Minidregg.Theory.Nock.loop_no_crash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loop_no_crash
/-- info: 'Minidregg.Theory.Nock.pole_increment' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_increment
/-- info: 'Minidregg.Theory.Nock.pole_increment_steps' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_increment_steps
/-- info: 'Minidregg.Theory.Nock.pole_core_call' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_core_call
/-- info: 'Minidregg.Theory.Nock.pole_edit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_edit
/-- info: 'Minidregg.Theory.Nock.decF_jam' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms decF_jam
/-- info: 'Minidregg.Theory.Nock.decF_cue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decF_cue
/-- info: 'Minidregg.Theory.Nock.pole_decrement' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_decrement
/-- info: 'Minidregg.Theory.Nock.pole_decrement_steps' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_decrement_steps
/-- info: 'Minidregg.Theory.Nock.pole_decrement_exhausted_5' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_decrement_exhausted_5
/-- info: 'Minidregg.Theory.Nock.pole_decrement_answers_50' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_decrement_answers_50
/-- info: 'Minidregg.Theory.Nock.pole_slam' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_slam
/-- info: 'Minidregg.Theory.Nock.pole_six_yes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_six_yes
/-- info: 'Minidregg.Theory.Nock.pole_wut' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_wut
/-- info: 'Minidregg.Theory.Nock.pole_hints_dropped' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_hints_dropped
/-- info: 'Minidregg.Theory.Nock.pole_axis_zero_crash' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_axis_zero_crash
/-- info: 'Minidregg.Theory.Nock.pole_axis_zero_no_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pole_axis_zero_no_value
/-- info: 'Minidregg.Theory.Nock.pole_lus_cell_crash' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_lus_cell_crash
/-- info: 'Minidregg.Theory.Nock.pole_six_nonloobean_crash' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_six_nonloobean_crash
/-- info: 'Minidregg.Theory.Nock.pole_scry_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_scry_refused
/-- info: 'Minidregg.Theory.Nock.pole_bad_opcode_crash' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_bad_opcode_crash
/-- info: 'Minidregg.Theory.Nock.pole_atom_formula_crash' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_atom_formula_crash
/-- info: 'Minidregg.Theory.Nock.pole_edit_axis_zero_crash' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_edit_axis_zero_crash
/-- info: 'Minidregg.Theory.Nock.pole_hint_clue_crash' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms pole_hint_clue_crash

end Nock


end Minidregg.Theory
