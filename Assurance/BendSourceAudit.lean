/- Audit executable source theorems, not merely names of proposition claims. -/
import Theory.BendTTSource
import Theory.AssertAxioms

open Minidregg.Theory.BendTT

#print axioms Minidregg.Theory.BendTT.book_check
#print axioms Minidregg.Theory.BendTT.confluent
#print axioms Minidregg.Theory.BendTT.sr
#print axioms Minidregg.Theory.BendTT.progress
#print axioms Minidregg.Theory.BendTT.halts
#print axioms Minidregg.Theory.BendTT.empty
#print axioms Minidregg.Theory.BendTT.consistent

#assert_axioms Minidregg.Theory.BendTT.book_check
#assert_axioms Minidregg.Theory.BendTT.confluent
#assert_axioms Minidregg.Theory.BendTT.sr
#assert_axioms Minidregg.Theory.BendTT.progress
#assert_axioms Minidregg.Theory.BendTT.halts
#assert_axioms Minidregg.Theory.BendTT.empty
#assert_axioms Minidregg.Theory.BendTT.consistent
