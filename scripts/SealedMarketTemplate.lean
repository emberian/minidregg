/-
`lake env lean --run scripts/SealedMarketTemplate.lean > deploy/shell/templates/market/sealed/law.market`

The sealed-market template is the Host's own rendering (`LawLeaf.renderClause`, the text a refusal
and `law show` print) of `Kernel.SealedMarket.law` at sentinel parameters, each sentinel replaced by
its placeholder. Lean is the law's one source; the client binds the placeholders and parses the text
(`native/resource-client/src/market.rs`). Check: `diff <(lake env lean --run …) law.market`.
-/
import Kernel.SealedMarket
import Compiler.RefusalReason

open Minidregg.Kernel.SealedMarket

def sentinels : List (Int × String) :=
  [(900000000000000001, "{FOUNDER}"), (900000000000000002, "{LAST_SEALED}"),
   (900000000000000003, "{LAST_REVEAL}"), (900000000000000004, "{CLOSE}"),
   (900000000000000005, "{REVEAL_END}"), (900000000000000006, "{SUPPLY}")]

def sentinel : Params :=
  ⟨900000000000000001, 900000000000000002, 900000000000000003, 900000000000000004,
    900000000000000005, 900000000000000006⟩

def subst (text : String) : String :=
  sentinels.foldl (fun acc (value, name) => acc.replace (toString value) name) text

def main : IO Unit := do
  IO.println "-- market/sealed: one sealed-bid market (SEALED-MARKET; PRIVACY §3.4, MUD §2.7/§2.8)."
  IO.println "-- Written by scripts/SealedMarketTemplate.lean: the Host's rendering of Kernel/SealedMarket.lean `law`."
  IO.println "-- Placeholders: {FOUNDER} the founder's subject; {CLOSE} the first reveal height, {LAST_SEALED} = CLOSE-1;"
  IO.println "-- {REVEAL_END} the first settlement height, {LAST_REVEAL} = REVEAL_END-1; {SUPPLY} the units sold."
  IO.println "-- Fields in fields.json. A bid commits (price, qty) in its slot: commit = cSHAKE256(\"DREGG.PRED.HASHEQ/v2\";"
  IO.println "-- cell ‖ 2 ‖ names of price, qty, blinder, commit ‖ price ‖ qty ‖ blinder), Pred/HashEqDigest.lean."
  for (clause, note) in (clauses sentinel).zip notes do
    IO.println s!"-- {note}"
    IO.println (subst (Minidregg.Compiler.LawLeaf.renderClause clause) ++ ";")
