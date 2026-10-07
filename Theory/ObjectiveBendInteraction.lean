/- The reference interaction semantics of an activity: its interaction tree.

An activity is a program that yields Plans and is resumed with responses. Its reference
meaning is the interaction tree of the program's OWN machine, with no checkpointing, no
forcing beyond what it demands, no collection, and resources only as large as needed:

* a visible event `Vis(p, k)`: the program yields Plan `p` (Data) and continues, for every
  response `r`, as `k r`, the program's own yielded state resumed with `r`;
* a return `ret d` (the program finished with result `d`);
* a fault that is a visible ending (`blackhole`: re-entered its own evaluation, `refused`);
* `malformed`: the program halted but its Plan or result is not Data within the deployment's
  output sizes, under any resources;
* `spin`: silent divergence, the machine never halts. It is a node of its own: ignoring
  internal steps never equates spinning forever with eventually yielding.

Since the machine is deterministic, the tree is determined by the node reached after each
finite sequence of responses: `observe budget s rs`. A node is reached "above a threshold"
(`EndsAbove`: under every resource vector at least some vector), which makes it a function of
the state (`endsAbove_unique`) with no resource parameter beyond the output sizes.

The machine/reference theorems (`node_of_chain_vis`, `observe_of_chain`, below, and their
kernel forms in `Kernel.ObjectiveResumeContract`): whatever a normalized state (a kernel
checkpoint) commits, under any resources, is the reference node of the lazy state it is in a
chain with; after a yield, for EVERY response, the resumed checkpoint is in a chain with
`k r`; and if the reference spins, the normalized state commits nothing, ever. -/
import Theory.ObjectiveBendDemandForcingConverse
namespace Minidregg.Theory.ObjectiveBendInteraction
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandCollect
open Minidregg.Theory.ObjectiveBendDemandData
open Minidregg.Theory.ObjectiveBendDemandForcing
set_option autoImplicit false

/-- **An ending above a threshold is unique**: two thresholds meet above both. -/
theorem endsAbove_unique {s : State} {b : Budget} {e1 e2 : Ending} {y1 y2 : State}
    (one : EndsAbove s b e1 y1) (two : EndsAbove s b e2 y2) : e1 = e2 ∧ y1 = y2 := by
  obtain ⟨L1, T1, E1, h1⟩ := one
  obtain ⟨L2, T2, E2, h2⟩ := two
  have a := h1 (limitsMax L1 L2) (T1 + T2) E2 (limitsLe_max_left _ _) (by omega)
  have c := h2 (limitsMax L1 L2) (T1 + T2) E1 (limitsLe_max_right _ _) (by omega)
  rw [Nat.add_comm E2 E1, a] at c
  simp only [Option.some.injEq, Prod.mk.injEq] at c
  exact c

/-- The reference ending of `s` with output sizes `b`: the ending reached above a threshold,
and the state it stops in (for a yield, the program's own yielded state). -/
noncomputable def ending (b : Budget) (s : State) : Option (Ending × State) := by
  classical
  exact if h : ∃ p : Ending × State, EndsAbove s b p.1 p.2 then some (Classical.choose h) else none

theorem ending_of_above {b : Budget} {s : State} {e : Ending} {y : State} (above : EndsAbove s b e y) :
    ending b s = some (e, y) := by
  have h : ∃ p : Ending × State, EndsAbove s b p.1 p.2 := ⟨(e, y), above⟩
  unfold ending
  rw [dif_pos h]
  have spec := Classical.choose_spec h
  obtain ⟨same1, same2⟩ := endsAbove_unique spec above
  exact congrArg some (Prod.ext same1 same2)

/-- One node of an interaction tree. -/
inductive Node where
  /-- A visible event: the program yielded this Plan and awaits a response. -/
  | vis (plan : Data)
  | ret (result : Data)
  | blackhole
  | refused (reason : Refusal)
  /-- The program halted, but no resources make its Plan or result Data within the sizes. -/
  | malformed
  /-- Silent divergence: the program never halts. -/
  | spin

def Node.ofEnding : Ending → Node
  | .yielded d => .vis d
  | .finished d => .ret d
  | .divergent => .blackhole
  | .refused reason => .refused reason

/-- The node at `s`. -/
noncomputable def node (b : Budget) (s : State) : Node := by
  classical
  exact match ending b s with
    | some (e, _) => Node.ofEnding e
    | none => if ∃ n, Halts s n then .malformed else .spin

/-- **The interaction tree** of the program at `s`, as the node reached after each finite
sequence of responses: at a visible event the continuation is the program's own yielded
state resumed with the next response (`k r`); a terminal node absorbs further responses. -/
noncomputable def observe (b : Budget) : State → List Term → Node
  | s, [] => node b s
  | s, response :: rest =>
    match ending b s with
    | some (.yielded _, y) =>
      match resume response y with
      | some next => observe b next rest
      | none => node b s
    | _ => node b s

/-- The continuation `k` of a visible event: the program's own yield, resumed. -/
noncomputable def continuation (b : Budget) (s : State) (response : Term) : Option State :=
  match ending b s with
  | some (.yielded _, y) => resume response y
  | _ => none

theorem node_of_above {b : Budget} {s : State} {e : Ending} {y : State} (above : EndsAbove s b e y) :
    node b s = Node.ofEnding e := by
  unfold node; rw [ending_of_above above]

/-- `spin` is exactly "never halts". -/
theorem node_spin_iff (b : Budget) (s : State) : node b s = .spin ↔ ∀ n, ¬ Halts s n := by
  unfold node
  cases hEnd : ending b s with
  | some p =>
    obtain ⟨en, y⟩ := p
    simp only
    constructor
    · intro h; cases en <;> simp [Node.ofEnding] at h
    · intro never
      exfalso
      unfold ending at hEnd
      split at hEnd
      · rename_i h
        have spec := Classical.choose_spec h
        rw [Option.some.injEq] at hEnd
        rw [hEnd] at spec
        obtain ⟨L0, T0, E0, above⟩ := spec
        obtain ⟨n, halts⟩ := halts_of_endsWith (above L0 T0 0 (limitsLe_refl _) (Nat.le_refl _))
        exact never n halts
      · cases hEnd
  | none =>
    simp only
    constructor
    · intro h n halts; rw [if_pos ⟨n, halts⟩] at h; cases h
    · intro never; rw [if_neg (fun ⟨n, h⟩ => never n h)]

/-! ## The machine against the reference -/

/-- **What a normalized state commits is the reference node** of the lazy state in a chain
with it: under ANY resources, an ending of the normalized state is the lazy state's node. -/
theorem node_of_chain {s t : State} (h : Chain s t) {L' : Limits} {T' : Nat} {b : Budget} {e : Ending}
    {y' : State} (ran : endsWith L' T' b t = some (e, y')) :
    node b s = Node.ofEnding e ∧ ∃ y, ending b s = some (e, y) ∧ Chain y y' := by
  obtain ⟨y, c, above⟩ := h.back ran
  exact ⟨node_of_above above, y, ending_of_above above, c⟩

/-- **The machine/reference yield theorem.** A normalized state yields Plan `d` (under any
resources) and the kernel stores the checkpoint of that yield's extraction. Then the
reference node is `Vis(d, k)`, and for EVERY response `r` the kernel accepts, resuming the
stored checkpoint corresponds to `k r` (they are in a chain: every later ending agrees,
resources only, and spinning is preserved). -/
theorem node_of_chain_vis {s t : State} (h : Chain s t) {L' : Limits} {T' : Nat} {b : Budget} {d : Data}
    {y' : State} (ran : endsWith L' T' b t = some (.yielded d, y')) (valid : AddrValid y') {r' : Result}
    (found : ObjectiveBendDemandData.yieldedPlan L' b y' = .ok r') :
    node b s = .vis d ∧ ∀ (response : Term) (stored : State),
      resume response (checkpoint r'.state) = some stored →
      ∃ next, continuation b s response = some next ∧ Chain next stored := by
  obtain ⟨y, above, chain⟩ := h.next ran valid found
  refine ⟨node_of_above above, fun response stored resumed => ?_⟩
  obtain ⟨next, again, c⟩ := chain.resume_back response resumed
  refine ⟨next, ?_, c⟩
  unfold continuation
  rw [ending_of_above above]
  exact again

/-- **Spinning is never a visible ending**: if the reference spins, the normalized state ends
no segment under any resources. -/
theorem chain_spin {s t : State} (h : Chain s t) {b : Budget} (spin : node b s = .spin) (L : Limits) (T : Nat)
    (b' : Budget) : endsWith L T b' t = none :=
  h.spins ((node_spin_iff b s).mp spin) L T b'

#assert_axioms endsAbove_unique ending_of_above node_of_above node_spin_iff node_of_chain node_of_chain_vis
#assert_axioms chain_spin

end Minidregg.Theory.ObjectiveBendInteraction
