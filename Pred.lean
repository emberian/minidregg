/-
# Pred — the ONE predicate algebra (ATLAS §7).
-/
import Pred.Core         -- the ONE predicate algebra: syntactic AST, decidable eval, keystone
import Pred.Leaf         -- the clause a refusal names: firstFailingLeaf over eval's own recursion, none exactly when eval accepts
import Pred.HashEqDigest  -- the hashEq commitment: fixed-width canonical opening, cSHAKE256 at DREGG.PRED.HASHEQ/v1, preimage injective, binds_or_collides, the length-hash refutable pole
import Pred.HashEq        -- hashEq_sound, hashEq_admits, hashEq_binds_or_collides, hashEq_reveal_binds, hashEq_context_bound, lengthHash_admits_any_reveal; HashEqHiding H ASSUMED at deployed (not proved), poles lengthHash_hashEqHiding / identity_not_hashEqHiding
import Pred.Placeholder  -- carve marker: relational + quantified views, the two dials (later work)
import Pred.BoundedQuantifiedView  -- finite forall/exists views lower into the same first-order Pred AST with exact denotation
import Pred.CoordinationDial  -- the coordination dial as a COMPUTED PRICE on the ONE Pred AST, with no second evaluator: the function view Slot → WithBot ℤ (Pi sup = slot-wise max), eval_congr_toFun for the new-state fragment, Inv defined THROUGH eval, dial : Pred → Verdict (free / ordering / stepShaped / thirdParty — refusals loud), dial_sound (free ⇒ IConfluent) by structural induction, dialTier + dial_tier1_sound into Theory.Finality; the `any` refusal is necessity (demoAny_not_confluent, the (1,5)/(5,1) join computed). Residuals [DIAL-pn] [DIAL-declared-merge] [DIAL-relational] [DIAL-price]
