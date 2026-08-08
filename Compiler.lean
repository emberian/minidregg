/-
# Compiler — the arithmetization spine (ATLAS §7).
-/
import Compiler.Placeholder  -- carve marker: syntactic-leaf IR, fold_unique, seqDescr, descriptor + codec
import Compiler.Signature    -- N3: abstract signatures, Term (= WType), fold_unique, agree_by_initiality, the syntactic-leaves-forced obligation
import Compiler.Air  -- the arithmetization DSL (derived): circuit⟺executor by initiality (N3), the first gadget; [AIR-flatten]/[AIR-poseidon]/[AIR-membership] the rungs toward a note-spend
