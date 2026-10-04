/-
# Theory.ObjectiveBendDigestChecks — axiom pins and deployed-hash instances for `digest`

`Theory.ObjectiveBendDigest` stays Init-only so the C transcription can link it; its pins live
here. The theorems there are kernel-checked over an arbitrary hash; the facts below that need the
deployed cSHAKE256 are closed instances run by the compiled evaluator (`native_decide`), pinned by
`#assert_compiled`, because one Keccak-f[1600] permutation under kernel reduction is outside any
proof budget.

The discriminating pair: `standIn_lowBit_is_vote` proves, for every voter, vote and salt, that the
arithmetic stand-in `world/ballot` used before (`2 * (salt * 1000 + voter) + vote`) carries the vote
in its low bit; `sealed_lowBit_not_vote` exhibits a YES commitment with an even digest and a NO
commitment with an odd one under `digest`, so that leak is gone. Neither is a hiding proof (hiding
is `ObjectiveBendDigest.Hiding`, assumed).
-/
import Theory.ObjectiveBendDigest
import Theory.AssertCompiled

namespace Minidregg.Theory.ObjectiveBendDigestChecks

open Minidregg.Theory.ObjectiveBendDigest

set_option autoImplicit false

#assert_axioms ofBE_natBytesBE natBytesBE_injective natBytesBE_length_le admissible_of_lt
  preimage_injective digest_lt binds_or_collides sealed_binds_or_collides
  lengthHash_binding_fails lengthHash_collides
  constHash_hiding identity_not_hiding hiding_at_equality_is_a_collision digestExport_reads
  deployed_eq customizationPrefix_length padForRate_length permutations_eq preimage_length
  permutations_le permutations_le_three permutations_le_two

/-- The stand-in commitment of `world/ballot` before `digest` existed: binding on its small domain,
and the vote is its low bit, for every voter, vote and salt. -/
theorem standIn_lowBit_is_vote (voter vote salt : Nat) (h : vote < 2) :
    (2 * (salt * 1000 + voter) + vote) % 2 = vote := by
  omega

#assert_axioms standIn_lowBit_is_vote

/-- Under `digest` the low bit is not the vote: voter 1 voting YES under salt 101 commits to an
even digest, and voting NO under salt 100 to an odd one. -/
theorem sealed_lowBit_not_vote :
    digest (digest 1 1) 101 % 2 = 0 ∧ digest (digest 1 0) 100 % 2 = 1 := by
  native_decide

#assert_compiled sealed_lowBit_not_vote

/-- The two openings of voter 1 under one salt commit differently (binding at the deployed hash,
on this instance), and neither commitment is the other's successor (the stand-in's YES commitment
was always its NO commitment plus one). -/
theorem sealed_yes_no_differ :
    digest (digest 1 1) 111 ≠ digest (digest 1 0) 111 ∧
      digest (digest 1 1) 111 ≠ digest (digest 1 0) 111 + 1 := by
  native_decide

#assert_compiled sealed_yes_no_differ

/-- Known answer at the deployed hash, the value the C differential's digest cases reproduce:
`digest 1 1`. -/
theorem digest_one_one :
    digest 1 1 =
      33544760771157370539093351361262075193213937251298462105196476525256921960532 := by
  native_decide

#assert_compiled digest_one_one

/-- Known answer for `world/ballot`'s seal: voter 1, YES, salt 111. The ballot preview row
`BallotSealKnownAnswer` must print this value. -/
theorem sealed_known_answer :
    digest (digest 1 1) 111 =
      83370838008729781310004166183474027631933533742037976749282545846343963921357 := by
  native_decide

#assert_compiled sealed_known_answer

end Minidregg.Theory.ObjectiveBendDigestChecks
