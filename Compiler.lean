/-
# Compiler — the arithmetization spine (ATLAS §7).
-/
import Compiler.Placeholder  -- carve marker: syntactic-leaf IR, fold_unique, seqDescr, descriptor + codec
import Compiler.Signature    -- N3: abstract signatures, Term (= WType), fold_unique, agree_by_initiality, the syntactic-leaves-forced obligation
import Compiler.Air  -- the arithmetization DSL (derived): circuit⟺executor by initiality (N3), the first gadget; [AIR-poseidon]/[AIR-membership] the rungs toward a note-spend
import Compiler.AirFlatten  -- [AIR-flatten] CLOSED: nested expressions → degree-≤2 gate systems with aux wires, the flatten a fold; wire-forcing refinement (sound+complete+unique) → gate system ⟺ executor
import Compiler.AirRange  -- [AIR-range] the bit-decomposition range gadget: k boolGadgets + recomposition as a ConstraintSystem; correct (iff) + bounds (cast of n < 2^k) + val_lt (ZMod p, 2^k ≤ p — the lift CLOSED) + complete (every n < 2^k accepted)
import Compiler.AirHash  -- [AIR-poseidon] the hash-permutation gadget: parameterized Poseidon2-style rounds (add-rc, S-box x^α full/partial, linear layer) as DSL terms; permGadget_eval (circuit ⟺ executor, all R rounds) + hashConstraint (nullifier ≐ hash(note), iff + teeth + complete); [AIR-poseidon-params] the deployed constants, [COMMIT-CR] the crypto floor
import Compiler.AirMembership  -- [AIR-membership] the Merkle-membership gadget: mux-selected compression (permGadget reused) folded up a path as one DSL term + boolGadget per direction bit; membership_correct (iff, every depth) + membership_meaning (∃ path ⟺ member, sound+complete) + teeth (root & bits); [COMMIT-CR]/[AIR-poseidon-params] inherited — the last note-spend gadget before [PRIVATE-TURN-air] composition
