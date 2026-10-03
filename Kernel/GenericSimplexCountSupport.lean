import Kernel.GenericSimplexVAInvariant
import Mathlib.Data.Finset.Card

namespace Minidregg.Kernel.GenericSimplexCountSupport
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexVAInvariant
set_option autoImplicit false

/-- Proof about the actual Std deduplicator used by executable count. No change
to the runtime algorithm, and no assumption that a raw tally has distinct voters. -/
theorem nat_eraseDups_nodup (xs : List Nat) : xs.eraseDups.Nodup := by
  match xs with
  | [] => simp
  | x :: rest =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    constructor
    · intro member
      have filtered := List.mem_eraseDups.mp member
      simp at filtered
    · exact nat_eraseDups_nodup (rest.filter (fun y => !y == x))
termination_by xs.length
decreasing_by
  have bound := List.length_filter_le (fun y => !y == x) rest
  simp only [List.length_cons]
  omega

def countedSenders (v : View) (kind : Kind) (arg : Argument) : List Nat :=
  ((v.received.filter fun m => m.kind == kind && m.value == arg &&
    (kind != .vote || !voteEquivocator v m.sender)).map Message.sender).eraseDups

theorem countedSenders_nodup (v : View) (kind : Kind) (arg : Argument) :
    (countedSenders v kind arg).Nodup := nat_eraseDups_nodup _

theorem count_is_distinct_card (v : View) (kind : Kind) (arg : Argument) :
    (countedSenders v kind arg).toFinset.card = count v kind arg :=
  List.toFinset_card_of_nodup (countedSenders_nodup v kind arg)

theorem counted_sender_received {v : View} {kind : Kind} {arg : Argument} {party : Nat}
    (member : party ∈ countedSenders v kind arg) :
    ∃ m ∈ v.received, m.sender = party ∧ m.kind = kind ∧ m.value = arg := by
  simp only [countedSenders, List.mem_eraseDups, List.mem_map, List.mem_filter] at member
  obtain ⟨m, ⟨inside, condition⟩, sender⟩ := member
  have pair := (Bool.and_eq_true.mp condition).1
  have k : m.kind = kind := by simpa using (Bool.and_eq_true.mp pair).1
  have a : m.value = arg := by simpa using (Bool.and_eq_true.mp pair).2
  exact ⟨m, inside, sender, k, a⟩

/-- The demanded receive invariant is concrete: every stored message has an
enrolled sender, the current View.number, and a strictly earlier actual send.
Combined with the executable tally this constructs the global Support witness. -/
theorem actual_count_support {tr : Trace} {roster : Finset Nat} {v : View}
    {kind : Kind} {arg : Argument} {time threshold : Nat}
    (received : ∀ m ∈ v.received, m.sender ∈ roster ∧ m.view = v.number ∧
      ∃ sentTime < time, tr sentTime = .send m)
    (enough : threshold ≤ count v kind arg) :
    Support tr roster time v.number kind arg threshold := by
  refine ⟨(countedSenders v kind arg).toFinset, ?_, ?_, ?_⟩
  · intro party member
    obtain ⟨m, inside, sender, _, _⟩ := counted_sender_received (List.mem_toFinset.mp member)
    simpa only [sender] using (received m inside).1
  · simpa only [count_is_distinct_card] using enough
  · intro party member
    obtain ⟨m, inside, sender, kindEq, argEq⟩ := counted_sender_received (List.mem_toFinset.mp member)
    obtain ⟨_, viewEq, sentTime, before, sent⟩ := received m inside
    refine ⟨sentTime, before, ?_⟩
    simpa only [Sent, ← sender, ← viewEq, ← kindEq, ← argEq] using sent

#assert_axioms nat_eraseDups_nodup
#assert_axioms count_is_distinct_card
#assert_axioms actual_count_support
end Minidregg.Kernel.GenericSimplexCountSupport
