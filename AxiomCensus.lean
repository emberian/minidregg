/-
# AxiomCensus — the tree-wide axiom check

Imports the DEPLOYED umbrella (`Deployed`: the core, kernel, predicates,
effects and every Host module except the other exe roots, whose `main` collides
with Host.Main; the umbrella builds them as separate targets) and runs `#assert_axioms_tree`: the build fails if
any package constant rests on `sorryAx` or a declared axiom. Built by
`scripts/lane/ub.sh`.
-/
import Deployed
import Theory.AssertAxioms

#assert_axioms_tree
