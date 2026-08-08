/-
# Compiler — the arithmetization spine (ATLAS §7).
-/
import Compiler.Placeholder  -- carve marker: syntactic-leaf IR, fold_unique, seqDescr, descriptor + codec
import Compiler.Signature    -- N3: abstract signatures, Term (= WType), fold_unique, agree_by_initiality, the syntactic-leaves-forced obligation
import Compiler.Air  -- the arithmetization DSL (derived): circuit⟺executor by initiality (N3), the first gadget; [AIR-poseidon]/[AIR-membership] the rungs toward a note-spend
import Compiler.AirFlatten  -- [AIR-flatten] CLOSED: nested expressions → degree-≤2 gate systems with aux wires, the flatten a fold; wire-forcing refinement (sound+complete+unique) → gate system ⟺ executor
