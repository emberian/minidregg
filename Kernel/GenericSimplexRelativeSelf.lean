/- The running replica never changes whose it is: `Replica.step` and `Replica.start` keep
`core.self`. The native journal checks this on every replay (`GenericSimplexIO.replayLog`);
this is the fact that makes the check one that cannot fail. -/
import Kernel.GenericSimplexRelative
import Kernel.GenericSimplexStructure
import Theory.AssertAxioms

namespace Minidregg.Kernel.GenericSimplexRelativeSelf
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexRelative
set_option autoImplicit false

theorem liveStep_self (c : Config) (s : State) (input : Input) : (liveStep c s input).self = s.self :=
  ((Minidregg.Kernel.GenericSimplexStructure.structuralAuditLaws c).stepExtension s input).sameSelf

theorem noteAhead_self (s : State) (sender view : Nat) : (noteAhead s sender view).self = s.self := by
  unfold noteAhead
  split <;> rfl

theorem rebase_self (c : Config) (h : ChainDigest) (r : Replica) :
    (rebase c h r).core.self = r.core.self := by
  unfold rebase
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem finish_self (c : Config) (h : ChainDigest) (r : Replica) (core : State) :
    (finish c h r core).core.self = core.self := by
  unfold finish
  dsimp only
  rw [rebase_self]

theorem foldl_delivery_self (c : Config) (batch : List (WireMessage × Message)) (s : State) :
    (batch.foldl (fun core x => liveStep c core (.delivery x.2)) s).self = s.self := by
  induction batch generalizing s with
  | nil => rfl
  | cons head rest ih =>
    rw [List.foldl_cons, ih]
    exact liveStep_self c s (.delivery head.2)

theorem deliver_self (c : Config) (h : ChainDigest) (r : Replica) (now : Option Nat) (w : WireMessage) :
    (deliver c h r now w).core.self = r.core.self := by
  unfold deliver
  dsimp only
  split
  · rfl
  · split
    · split <;> split <;> simp only [finish_self, noteAhead_self]
    · split <;> split <;> simp only [finish_self, noteAhead_self, liveStep_self]

theorem release_self (c : Config) (h : ChainDigest) (r : Replica) :
    (release c h r).core.self = r.core.self := by
  unfold release
  dsimp only
  split_ifs <;> first | rfl | (rw [finish_self]; exact foldl_delivery_self c _ _)

/-- **One input never changes whose replica it is.** -/
theorem step_self (c : Config) (h : ChainDigest) (r : Replica) (input : WireInput) :
    (r.step c h input).core.self = r.core.self := by
  unfold Replica.step
  rw [release_self]
  cases input with
  | delivery w => exact deliver_self c h r none w
  | deliveryAt now w => exact deliver_self c h r (some now) w
  | tick now => dsimp only; rw [finish_self, liveStep_self]
  | checked height records =>
    dsimp only
    split
    · rw [finish_self, liveStep_self]
    · rfl
  | offer payload => dsimp only; rw [finish_self, liveStep_self]
  | poll => dsimp only; rw [finish_self, liveStep_self]

/-- A replica starts as the member it was started for. -/
theorem start_self (c : Config) (h : ChainDigest) (self now : Nat) :
    (Replica.start c h self now).core.self = self := by
  unfold Replica.start
  dsimp only
  rw [finish_self]
  exact (Minidregg.Kernel.GenericSimplexStructure.structuralAuditLaws c).startSelf self now

#assert_axioms step_self
#assert_axioms start_self

end Minidregg.Kernel.GenericSimplexRelativeSelf
