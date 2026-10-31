import Kernel.DurableEngine

/- Small executable controls for the installed budget, not a performance test.
Every lane is exhausted separately; the next fresh claim must refuse. -/
open Minidregg.Theory
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableCheckpoint
open Minidregg.Kernel.DurableEngine

private def root (_ : List UInt8) : Digest := ⟨0⟩

private def claim (id : Nat) (lane : Lane) (amount : Nat) : DataIntent root where
  transactionId := ⟨id⟩
  writes := []
  readGuards := [⟨⟨0⟩, ⟨0⟩⟩]
  nullifiers := [⟨1, ⟨0⟩, ⟨id⟩, [1]⟩]
  exactCharge := fun selected => if selected = lane then amount else 0
  event := ⟨1, ⟨0⟩, ⟨id⟩, [1]⟩
  subject := none
  postRootsBound := by simp
  guardsReadOnly := by simp

private def initial : Engine root := Engine.ofState root ⟨[], [], fun _ => 2⟩ []

private def accepts (engine : Engine root) (intent : DataIntent root) : Bool :=
  match engine.execute root intent with
  | .accepted _ => true
  | _ => false

private def checks (lane : Lane) : Bool :=
  let first := claim 1 lane 1
  let second := claim 2 lane 1
  let once := initial.install root first
  let twice := once.install root second
  accepts initial first && accepts once second &&
    decide ((initial.install root (claim 4 lane 3)).available lane = 0) &&
    Lane.allCheck (fun other => decide
      (twice.available other = if other = lane then 0 else 2)) &&
    (match twice.execute root (claim 3 lane 1) with
     | .rejected (.durable .insufficientBudget) => true
     | _ => false) &&
    accepts twice (claim 3 lane 0) &&
    (match initial.execute root (claim 4 lane 3) with
     | .rejected (.durable .insufficientBudget) => true
     | _ => false)

#guard Lane.allCheck checks

-- The full protocol simulation remains the obligation, for all engines and
-- intents rather than only the ten executable boundary fixtures above.
#check Engine.view_install
#check Engine.available_install
#assert_axioms Engine.available_install
