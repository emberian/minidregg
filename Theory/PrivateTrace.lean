/-
# Theory.PrivateTrace — multi-step, adaptive-adversary indistinguishability of a deterministic machine

**The question this file settles.**  `Kernel/PrivateTurn.lean` (cited by name only — Theory is
candidate-independent and never depends on Kernel) proves the ONE-STEP fact `post_public_agrees`:
under a witness-blind step, two states with equal public projections have equal public projections
after one turn.  A verifier does not
watch one turn — it watches a TRACE, and it CHOOSES each next command from what it has seen so far.
The multi-step lift is: which hypotheses on a relation `R` between initial states make the whole
observed trace equal, for EVERY adaptive policy?  The answer is the pair

* `hout`  — `R` is blind to the observable: `R s t → out s = out t`;
* `hstep` — `R` is preserved by EVERY allowed command: `R s t → R (step s c) (step t c)`;

and NEITHER alone suffices.  That is the external handoff's ("learn/infer-only" private
computation) distinction, made the tree's: **certify the combined learn-and-infer interface, not
the two verbs independently** — "learn" is `step` (the update) and "infer" is `out` (the query), and
the invariant `R` must be simultaneously blind to the query and stable under every update.  Equal
answers to the next inference alone (`hout` without `hstep`) are insufficient; a stable secret that
the query reads (`hstep` without `hout`) is insufficient.  `post_public_agrees` is exactly the
hyperedge-shaped one-step instance: its `hblind` is `hstep` for `R := "equal public halves"` and
its conclusion is `hout` after one step.

**Carrier.**  `Machine S C O` — deterministic `step : S → C → S`, `out : S → O`.  A `Policy C O` is
adaptive: `List O → C`, the next command chosen from the outputs observed so far (oldest first).
`trace M π s n` is the list of the `n` observations made when running `π` from `s`: each round
observes `out` of the current state, appends it to the history, then steps by the policy's choice
on that history — so the first observation is `out s` itself.  Randomized state (a distribution
over `S`) would need a COUPLING version of the theorem; that is NOT done here.

**Statements (statement-first; every hypothesis is a constraint, see the teeth).**

* `trace_eq_of_preserved` — `hout` and `hstep` for `R` ⇒ for every policy `π`, every length `n`,
  `R s t → trace M π s n = trace M π t n`.
* `trace_length` — the trace really has `n` entries (the carrier is not degenerate).

**Witness, falsifiers, premise inhabitation, recovery — all on a byte machine `Fin 256` with the
high bit as the observable (`out s = decide (128 ≤ s.val)`), commands read as additive offsets.**

* *Satisfying witness — the handoff's toy, with the HONEST relation.*  `flipMachine`: the single
  update `s ↦ s + 128`.  The relation that works is `highR s t := s.val / 128 = t.val / 128`
  (EQUAL HIGH BIT, i.e. the states differ only in their low seven bits): `highR_out` (the high
  bit is what `out` reads) and `highR_flip_step` (`+128` flips both high bits together).  So
  `flip_trace_eq_of_highR`: states differing only in lower bits are indistinguishable under every
  policy for every length — while the VISIBLE state changes every round, `flip_trace_alternates`
  (the trace from `s` is `out s, ¬out s, out s, …`).  Non-vacuity: `0` and `5` are distinct and
  related; `trace … 5 3 = [false, true, false]` is computed, not assumed.
* *Falsifier for `hout` — the tempting wrong relation.*  `lowR s t := s.val % 128 = t.val % 128`
  ("agree below the high bit") IS preserved by `+128` (`lowR_flip_step`) but is NOT blind to the
  output (`not_lowR_out`: `0` and `128`), and the conclusion fails: `lowR_traces_differ`.
  Dropping `hout` drops the theorem.
* *Falsifier for `hstep` — the handoff's.*  Allow the update `+1` as well (`twoMachine`, commands
  `flip | inc`).  `highR` still satisfies `hout` (`highR_two_out`: equal answers to the next
  inference) but is NOT preserved by `inc` (`not_highR_two_step`: `127 ↦ 128` and `0 ↦ 1`), and the
  conclusion fails: `highR_two_traces_differ` (`127` and `0`, two observations under "always
  `inc`").  Dropping `hstep` drops the theorem.
* *The stronger fact the handoff measured — adaptive recovery.*  With arbitrary offsets
  (`offsetMachine`, commands `Fin 256`) and the high-bit observable, the binary-search policy
  `searchPolicy` (after each observation, subtract `2^(7−k)` if the last bit seen was `1`, else add
  it) makes the eight observations the binary expansion of the initial byte: `search_recovers`
  (`ofBits (trace … s 8) = s.val`, decided over all 256 bytes), hence `exists_policy_recovers`.
  Sharpness both ways: `search_seven_insufficient` (this policy needs all eight) and the general
  `no_policy_recovers_seven` (NO policy separates 256 states with 7 boolean observations —
  pigeonhole through `List.Vector Bool 7`).
* *Premise inhabitation.*  `machine_inhabited` (the byte machine is a `Machine`); `eq_out`/`eq_step`
  (the identity relation satisfies both premises for EVERY machine — and is the uninteresting
  instance, since it relates no two distinct states, so its conclusion is `trace s = trace s`).
  `highR_zero_five` is the interesting one: distinct related states.

**What was decided by the kernel vs argued.**  `trace_eq_of_preserved`, `trace_length`,
`flip_trace_alternates`, `no_policy_recovers_seven`, `exists_policy_recovers` are general arguments
(induction / pigeonhole).  `highR_out`, `highR_flip_step`, `lowR_flip_step`, `flip_out_step` are
`omega` over the byte bounds.  The concrete witnesses and falsifiers are `decide`;
`search_recovers` is `decide +kernel` over all 256 initial bytes, eight rounds each (the kernel
evaluates the trace; no `native_decide`, no `#guard`, no `ofReduceBool` in any pin).

**Reused from Mathlib:** `Fintype.card_le_of_injective`, `card_vector`, `Fintype.card_bool`,
`List.Vector`.
-/
import Mathlib.Tactic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Vector

namespace Minidregg.Theory.PrivateTrace

set_option autoImplicit false

/-! ## 0. The carrier: a deterministic machine, an adaptive policy, its trace -/

/-- A **deterministic state machine** with observable output.  `step` is the "learn"/update verb,
`out` the "infer"/query verb.  Deterministic on purpose: a randomized state (a distribution over
`S`) needs a coupling version of `trace_eq_of_preserved`, which this file does NOT do. -/
structure Machine (S C O : Type*) where
  /-- the update: apply a command. -/
  step : S → C → S
  /-- the query: what the observer sees of a state. -/
  out : S → O

/-- An **adaptive policy**: the next command is chosen from the outputs observed so far (oldest
first).  Non-adaptive policies are the special case that ignores its argument. -/
abbrev Policy (C O : Type*) := List O → C

/-- One round: observe `out s`, append it to the history, step by the policy's choice on the
history so far.  `acc` is the history accumulated so far; `n` the rounds remaining. -/
def traceAux {S C O : Type*} (M : Machine S C O) (π : Policy C O) :
    S → List O → ℕ → List O
  | _, acc, 0 => acc
  | s, acc, n + 1 =>
    let acc' := acc ++ [M.out s]
    traceAux M π (M.step s (π acc')) acc' n

/-- **The trace**: the `n` observations made running `π` from `s`, oldest first.  The first
observation is `out s`; the `k`-th command is chosen from the first `k` observations. -/
def trace {S C O : Type*} (M : Machine S C O) (π : Policy C O) (s : S) (n : ℕ) : List O :=
  traceAux M π s [] n

theorem traceAux_length {S C O : Type*} (M : Machine S C O) (π : Policy C O) :
    ∀ (n : ℕ) (s : S) (acc : List O), (traceAux M π s acc n).length = acc.length + n := by
  intro n
  induction n with
  | zero => intro s acc; simp [traceAux]
  | succ n ih =>
    intro s acc
    simp only [traceAux]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

/-- The trace really has `n` entries. -/
theorem trace_length {S C O : Type*} (M : Machine S C O) (π : Policy C O) (s : S) (n : ℕ) :
    (trace M π s n).length = n := by
  simp [trace, traceAux_length]

/-! ## 1. The theorem -/

theorem traceAux_eq_of_preserved {S C O : Type*} (M : Machine S C O) (R : S → S → Prop)
    (hout : ∀ s t, R s t → M.out s = M.out t)
    (hstep : ∀ s t c, R s t → R (M.step s c) (M.step t c)) (π : Policy C O) :
    ∀ (n : ℕ) (s t : S) (acc : List O), R s t → traceAux M π s acc n = traceAux M π t acc n := by
  intro n
  induction n with
  | zero => intro s t acc _; rfl
  | succ n ih =>
    intro s t acc hst
    simp only [traceAux]
    rw [hout s t hst]
    exact ih _ _ _ (hstep _ _ _ hst)

/-- **The multi-step, adaptive-policy lift of `post_public_agrees`.**  If `R` is blind to the
observable (`hout`) and preserved by EVERY allowed command (`hstep`), then `R`-related initial
states produce IDENTICAL traces of every length under EVERY adaptive policy.  Both premises are
genuine constraints (`not_lowR_out` / `lowR_traces_differ` and `not_highR_two_step` /
`highR_two_traces_differ` below): the invariant must be certified against the combined
learn-and-infer interface, not against either verb alone. -/
theorem trace_eq_of_preserved {S C O : Type*} (M : Machine S C O) (R : S → S → Prop)
    (hout : ∀ s t, R s t → M.out s = M.out t)
    (hstep : ∀ s t c, R s t → R (M.step s c) (M.step t c)) :
    ∀ (π : Policy C O) (n : ℕ) (s t : S), R s t → trace M π s n = trace M π t n :=
  fun π n s t hst => traceAux_eq_of_preserved M R hout hstep π n s t [] hst

/-! ## 2. The byte machine -/

/-- **The byte machine**: states are bytes, a command `c` is the additive offset `off c`, and the
observable is the HIGH bit. -/
def byteMachine {C : Type} (off : C → Fin 256) : Machine (Fin 256) C Bool where
  step s c := s + off c
  out s := decide (128 ≤ s.val)

/-- The handoff's toy: the single update `+128`. -/
def flipMachine : Machine (Fin 256) Unit Bool := byteMachine fun _ => 128

/-- The toy's commands plus the extra update `+1`. -/
inductive Upd
  | flip
  | inc

/-- The toy with `+1` allowed as well. -/
def twoMachine : Machine (Fin 256) Upd Bool :=
  byteMachine fun
    | .flip => 128
    | .inc => 1

/-- Arbitrary offsets (contains both `+1` and `+128`). -/
def offsetMachine : Machine (Fin 256) (Fin 256) Bool := byteMachine id

/-- Equal HIGH bit — the states differ only in their low seven bits. -/
def highR (s t : Fin 256) : Prop := s.val / 128 = t.val / 128

instance : DecidableRel highR := fun s t => inferInstanceAs (Decidable (s.val / 128 = t.val / 128))

/-- Equal LOW seven bits — the tempting wrong relation for the toy. -/
def lowR (s t : Fin 256) : Prop := s.val % 128 = t.val % 128

instance : DecidableRel lowR := fun s t => inferInstanceAs (Decidable (s.val % 128 = t.val % 128))

/-! ## 3. Satisfying witness — the toy, with the honest relation `highR` -/

/-- `hout` for `highR` on the toy: the high bit is what the observer reads. -/
theorem highR_out : ∀ s t, highR s t → flipMachine.out s = flipMachine.out t := by
  intro s t h
  simp only [flipMachine, byteMachine, highR] at *
  exact decide_eq_decide.mpr (by omega)

/-- `hstep` for `highR` on the toy: `+128` flips BOTH high bits together. -/
theorem highR_flip_step :
    ∀ s t (c : Unit), highR s t → highR (flipMachine.step s c) (flipMachine.step t c) := by
  intro s t _ h
  simp only [flipMachine, byteMachine, highR, Fin.val_add] at *
  have hs := s.isLt
  have ht := t.isLt
  omega

/-- **The witness**: on the toy, states with equal high bit are indistinguishable under every
policy, for every trace length — from the general theorem. -/
theorem flip_trace_eq_of_highR :
    ∀ (π : Policy Unit Bool) (n : ℕ) (s t : Fin 256),
      highR s t → trace flipMachine π s n = trace flipMachine π t n :=
  trace_eq_of_preserved flipMachine highR highR_out highR_flip_step

/-- Two DISTINCT related states (so the witness is not the identity relation in disguise). -/
theorem highR_zero_five : highR 0 5 ∧ (0 : Fin 256) ≠ 5 := by decide

/-- …and their traces agree (the theorem, instantiated). -/
theorem flip_trace_zero_five (π : Policy Unit Bool) (n : ℕ) :
    trace flipMachine π 0 n = trace flipMachine π 5 n :=
  flip_trace_eq_of_highR π n 0 5 highR_zero_five.1

/-- The visible state CHANGES every round: the trace is not constant (computed). -/
theorem flip_trace_five : trace flipMachine (fun _ => ()) 5 3 = [false, true, false] := by
  decide

/-- `b, ¬b, b, …` of length `n`. -/
def alternating : Bool → ℕ → List Bool
  | _, 0 => []
  | b, n + 1 => b :: alternating (!b) n

/-- A single-command machine's trace, unfolded without the policy (which can only say `()`). -/
def simpleTrace {S O : Type*} (M : Machine S Unit O) : S → ℕ → List O
  | _, 0 => []
  | s, n + 1 => M.out s :: simpleTrace M (M.step s ()) n

theorem traceAux_unit {S O : Type*} (M : Machine S Unit O) (π : Policy Unit O) :
    ∀ (n : ℕ) (s : S) (acc : List O), traceAux M π s acc n = acc ++ simpleTrace M s n := by
  intro n
  induction n with
  | zero => intro s acc; simp [traceAux, simpleTrace]
  | succ n ih =>
    intro s acc
    simp only [traceAux, simpleTrace]
    rw [ih]
    simp

/-- `+128` flips the high bit. -/
theorem flip_out_step :
    ∀ s : Fin 256, flipMachine.out (flipMachine.step s ()) = !flipMachine.out s := by
  intro s
  simp only [flipMachine, byteMachine, Fin.val_add]
  have hs := s.isLt
  by_cases h : 128 ≤ s.val
  · have h' : ¬ 128 ≤ (s.val + 128) % 256 := by omega
    simp [h, h']
  · have h' : 128 ≤ (s.val + 128) % 256 := by omega
    simp [h, h']

theorem simpleTrace_flip :
    ∀ (n : ℕ) (s : Fin 256), simpleTrace flipMachine s n = alternating (flipMachine.out s) n := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    simp only [simpleTrace, alternating]
    rw [ih, flip_out_step]

/-- **The toy's trace alternates**: from `s` the observer sees `out s, ¬out s, out s, …` — the
visible state moves every round, and only the initial high bit is ever revealed. -/
theorem flip_trace_alternates (π : Policy Unit Bool) (s : Fin 256) (n : ℕ) :
    trace flipMachine π s n = alternating (flipMachine.out s) n := by
  simp [trace, traceAux_unit, simpleTrace_flip]

/-! ## 4. Falsifier for `hout` — `lowR` is preserved but not blind -/

/-- `lowR` IS preserved by `+128` (`hstep` holds). -/
theorem lowR_flip_step :
    ∀ s t (c : Unit), lowR s t → lowR (flipMachine.step s c) (flipMachine.step t c) := by
  intro s t _ h
  simp only [flipMachine, byteMachine, lowR, Fin.val_add] at *
  have hs := s.isLt
  have ht := t.isLt
  omega

/-- …but `lowR` is NOT blind to the output (`hout` fails): `0` and `128` agree below the high bit
and the observer separates them at once. -/
theorem not_lowR_out : ¬ ∀ s t, lowR s t → flipMachine.out s = flipMachine.out t :=
  fun h => absurd (h 0 128 (by decide)) (by decide)

/-- …and the CONCLUSION fails: `lowR`-related states have different traces.  So `hout` cannot
be dropped from `trace_eq_of_preserved`. -/
theorem lowR_traces_differ :
    lowR 0 128 ∧ trace flipMachine (fun _ => ()) 0 2 ≠ trace flipMachine (fun _ => ()) 128 2 := by
  decide

/-! ## 5. Falsifier for `hstep` — the handoff's: allow `+1` -/

/-- With `+1` allowed, `highR` STILL satisfies `hout` (the observable did not change): equal
answers to the next inference. -/
theorem highR_two_out : ∀ s t, highR s t → twoMachine.out s = twoMachine.out t := highR_out

/-- …but `highR` is NOT preserved by `inc` (`hstep` fails): `127` and `0` share high bit `0`;
`+1` sends `127 ↦ 128` (high bit `1`) and `0 ↦ 1` (high bit `0`). -/
theorem not_highR_two_step :
    ¬ ∀ s t c, highR s t → highR (twoMachine.step s c) (twoMachine.step t c) :=
  fun h => absurd (h 127 0 .inc (by decide)) (by decide)

/-- …and the CONCLUSION fails: under the policy "always `inc`", `127` and `0` — related, and
giving equal answers to the next inference — have different two-observation traces.  So `hstep`
cannot be dropped: `R` must be preserved by EVERY allowed command, not just the ones a
particular run happens to issue. -/
theorem highR_two_traces_differ :
    highR 127 0 ∧
      trace twoMachine (fun _ => .inc) 127 2 ≠ trace twoMachine (fun _ => .inc) 0 2 := by
  decide

/-! ## 6. Adaptive recovery — the stronger fact the handoff measured -/

/-- **The binary-search policy.**  After `k` observations whose last bit is `b`: if `b = 1` the
probe overshot, subtract `2^(7−k)`; else add `2^(7−k)`.  Invariant (the argument behind the
kernel's decision in `search_recovers`): after the `k`-th command the state is
`(s mod 2^(8−k)) + 128 − 2^(7−k)`, whose high bit is bit `7−k` of the initial `s` — so the `k+1`-st
observation is that bit, and the trace is the binary expansion of `s`, most significant bit
first. -/
def searchPolicy (hist : List Bool) : Fin 256 :=
  match hist.getLast? with
  | some true => ⟨(256 - 2 ^ (7 - hist.length)) % 256, Nat.mod_lt _ (by omega)⟩
  | _ => ⟨2 ^ (7 - hist.length) % 256, Nat.mod_lt _ (by omega)⟩

/-- The policy is genuinely adaptive: it answers differently to different histories. -/
theorem searchPolicy_adaptive : searchPolicy [true] ≠ searchPolicy [false] := by decide

/-- The decoder: read a bit list as a binary numeral, most significant bit first. -/
def ofBits (bs : List Bool) : ℕ := bs.foldl (fun acc b => 2 * acc + b.toNat) 0

/-- A sample: `178 = 0b10110010` is read off the trace bit by bit (computed). -/
theorem search_trace_178 :
    trace offsetMachine searchPolicy 178 8 =
      [true, false, true, true, false, false, true, false] := by
  decide

/-- **Recovery**: for EVERY initial byte, the eight observations decode to it — decided over all
256 bytes, eight rounds each. -/
theorem search_recovers : ∀ s : Fin 256, ofBits (trace offsetMachine searchPolicy s 8) = s.val := by
  decide +kernel

/-- **`exists_policy_recovers`**: with arbitrary offsets and the high-bit observable, an adaptive
policy separates every pair of initial states in 8 observations.  Contrast the toy: there, states
differing only in low bits are indistinguishable FOREVER (`flip_trace_eq_of_highR`); one extra
allowed command turns the hidden seven bits into eight observations. -/
theorem exists_policy_recovers :
    ∃ π : Policy (Fin 256) Bool,
      ∀ s t : Fin 256, trace offsetMachine π s 8 = trace offsetMachine π t 8 → s = t :=
  ⟨searchPolicy, fun s t h =>
    Fin.ext ((search_recovers s).symm.trans (by rw [h]; exact search_recovers t))⟩

/-- Sharpness for this policy: seven observations do not suffice (`0` and `1` agree). -/
theorem search_seven_insufficient :
    trace offsetMachine searchPolicy 0 7 = trace offsetMachine searchPolicy 1 7 := by
  decide

/-- Sharpness for EVERY policy: seven boolean observations cannot separate 256 states
(pigeonhole: the trace lands in `List.Vector Bool 7`, which has `2^7 = 128 < 256` elements). -/
theorem no_policy_recovers_seven (π : Policy (Fin 256) Bool) :
    ¬ ∀ s t : Fin 256, trace offsetMachine π s 7 = trace offsetMachine π t 7 → s = t := by
  intro hinj
  let f : Fin 256 → List.Vector Bool 7 := fun s => ⟨trace offsetMachine π s 7, trace_length _ _ _ _⟩
  have hf : Function.Injective f := fun s t h => hinj s t (congrArg Subtype.val h)
  have := Fintype.card_le_of_injective f hf
  rw [card_vector, Fintype.card_bool, Fintype.card_fin] at this
  omega

/-! ## 7. Premise inhabitation -/

/-- The byte machine inhabits the carrier. -/
theorem machine_inhabited : Nonempty (Machine (Fin 256) Unit Bool) := ⟨flipMachine⟩

/-- The identity relation satisfies `hout` for every machine… -/
theorem eq_out {S C O : Type*} (M : Machine S C O) : ∀ s t, s = t → M.out s = M.out t :=
  fun _ _ h => h ▸ rfl

/-- …and `hstep` for every machine.  This is the UNINTERESTING instance: it relates no two
distinct states, so `trace_eq_of_preserved` says only `trace s = trace s`.  The content is in
relations like `highR` that relate DISTINCT states (`highR_zero_five`). -/
theorem eq_step {S C O : Type*} (M : Machine S C O) :
    ∀ s t c, s = t → M.step s c = M.step t c :=
  fun _ _ _ h => h ▸ rfl

/-! ## 8. Axiom pins -/

/-- info: 'Minidregg.Theory.PrivateTrace.trace_eq_of_preserved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms trace_eq_of_preserved
/-- info: 'Minidregg.Theory.PrivateTrace.trace_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms trace_length
/-- info: 'Minidregg.Theory.PrivateTrace.highR_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms highR_out
/-- info: 'Minidregg.Theory.PrivateTrace.highR_flip_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms highR_flip_step
/-- info: 'Minidregg.Theory.PrivateTrace.flip_trace_eq_of_highR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms flip_trace_eq_of_highR
/-- info: 'Minidregg.Theory.PrivateTrace.highR_zero_five' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms highR_zero_five
/-- info: 'Minidregg.Theory.PrivateTrace.flip_trace_five' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms flip_trace_five
/-- info: 'Minidregg.Theory.PrivateTrace.flip_trace_alternates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms flip_trace_alternates
/-- info: 'Minidregg.Theory.PrivateTrace.lowR_flip_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lowR_flip_step
/-- info: 'Minidregg.Theory.PrivateTrace.not_lowR_out' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms not_lowR_out
/-- info: 'Minidregg.Theory.PrivateTrace.lowR_traces_differ' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms lowR_traces_differ
/-- info: 'Minidregg.Theory.PrivateTrace.highR_two_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms highR_two_out
/-- info: 'Minidregg.Theory.PrivateTrace.not_highR_two_step' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms not_highR_two_step
/-- info: 'Minidregg.Theory.PrivateTrace.highR_two_traces_differ' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms highR_two_traces_differ
/-- info: 'Minidregg.Theory.PrivateTrace.search_recovers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms search_recovers
/-- info: 'Minidregg.Theory.PrivateTrace.exists_policy_recovers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exists_policy_recovers
/-- info: 'Minidregg.Theory.PrivateTrace.search_seven_insufficient' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms search_seven_insufficient
/-- info: 'Minidregg.Theory.PrivateTrace.no_policy_recovers_seven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_policy_recovers_seven
/-- info: 'Minidregg.Theory.PrivateTrace.machine_inhabited' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms machine_inhabited
/-- info: 'Minidregg.Theory.PrivateTrace.eq_step' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms eq_step

end Minidregg.Theory.PrivateTrace
