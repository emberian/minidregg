import Kernel.GenericSimplexLocal

namespace Minidregg.Kernel.GenericSimplexReceiveProvenance
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
set_option autoImplicit false

/-- External messages are authenticated before ingest. Self-broadcasts have exact
retained send events. This is only message provenance, not count or consensus. -/
def Backed (external : Message → Prop) (state : State) : Prop :=
  ∀ view ∈ state.views, ∀ message ∈ view.received,
    external message ∨ (.send message : AuditEvent) ∈ state.audit

theorem viewAt_backed {external : Message → Prop} {state : State}
    (backed : Backed external state) (number : Nat) :
    ∀ message ∈ (viewAt state number).received,
      external message ∨ (.send message : AuditEvent) ∈ state.audit := by
  unfold viewAt
  cases found : state.views.find? (fun v => v.number == number) with
  | none => simp
  | some view =>
    exact backed view (List.mem_of_find?_eq_some found)

theorem putView_backed {external : Message → Prop} {state : State} (view : View)
    (backed : Backed external state)
    (newBacked : ∀ message ∈ view.received,
      external message ∨ (.send message : AuditEvent) ∈ state.audit) :
    Backed external (putView state view) := by
  intro other member message received
  unfold putView at member
  split at member
  · obtain ⟨old, inside, same⟩ := List.mem_map.mp member
    split at same
    · subst other; exact newBacked message received
    · subst other; exact backed old inside message received
  · rcases List.mem_append.mp member with old | added
    · exact backed other old message received
    · have same : other = view := by simpa using added
      subst other
      exact newBacked message received

theorem addUnique_mem {α : Type} [BEq α] (items : List α) (item value : α)
    (member : value ∈ addUnique items item) : value ∈ items ∨ value = item := by
  unfold addUnique at member
  split at member
  · exact Or.inl member
  · rcases List.mem_append.mp member with old | added
    · exact Or.inl old
    · exact Or.inr (by simpa using added)

theorem register_backed {external : Message → Prop} {state : State} (message : Message)
    (backed : Backed external state)
    (available : external message ∨ (.send message : AuditEvent) ∈ state.audit) :
    Backed external (register state message) := by
  apply putView_backed _ backed
  intro other member
  rcases addUnique_mem _ message other member with old | same
  · exact viewAt_backed backed message.view other old
  · subst other; exact available

theorem backed_weaken {external next : Message → Prop} {state : State}
    (backed : Backed external state) (include : ∀ m, external m → next m) :
    Backed next state := by
  intro view member message received
  exact (backed view member message received).imp (include message) id

theorem broadcast_backed {external : Message → Prop} {state : State}
    (number : Nat) (kind : Kind) (arg : Argument) (backed : Backed external state) :
    Backed external (broadcast state number kind arg) := by
  let message : Message := ⟨state.self, number, kind, arg⟩
  let augmented : Message → Prop := fun m => external m ∨ m = message
  have old : Backed augmented state := backed_weaken backed (fun _ h => Or.inl h)
  have registered := register_backed message old (Or.inl (Or.inr rfl))
  intro view member other received
  have cause := registered view member other received
  rcases cause with externalCause | oldSend
  · rcases externalCause with original | same
    · exact Or.inl original
    · subst other
      exact Or.inr (by simp [broadcast_audit, message])
  · exact Or.inr (by simpa only [broadcast_audit, register_audit, List.mem_append,
      List.mem_singleton] using Or.inl oldSend)

#assert_axioms viewAt_backed
#assert_axioms putView_backed
#assert_axioms register_backed
#assert_axioms broadcast_backed
end Minidregg.Kernel.GenericSimplexReceiveProvenance
EOF'