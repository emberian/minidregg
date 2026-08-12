/-
# Pred — the ONE predicate algebra (ATLAS §7).
-/
import Pred.Core         -- the ONE predicate algebra: syntactic AST, decidable eval, keystone
import Pred.Placeholder  -- carve marker: relational + quantified views, the two dials (later work)
import Pred.BoundedQuantifiedView  -- finite forall/exists views lower into the same first-order Pred AST with exact denotation
