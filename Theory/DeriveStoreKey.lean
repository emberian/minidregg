/-
# Theory.DeriveStoreKey -- `deriving StoreKey`

A key type of a store layout gets its injective code (`Theory.SparseMap`'s `StoreKey`) by
`deriving StoreKey`, never by hand. For a non-recursive inductive `T` the handler emits

    def T.storeKeyCode : T → List Nat
      | .cᵢ x₁ … xₙ => i :: StoreKey.frames [code x₁, …, code xₙ]

skipping proof fields and fields the result type determines (indices), and the instance
`StoreKey.ofCode T.storeKeyCode (by store_key_inj)`: distinct constructors differ in the head,
equal heads give equal framed field codes (`frames_eq_iff`), hence equal fields (`code_eq_iff`).
-/
module

public import Lean.Elab.Deriving.Basic
public import Lean.Elab.Deriving.Util
public import Lean.Meta.SameCtorUtils
public import Theory.SparseMap

public section

namespace Minidregg.Theory.StoreKey

/-- Injectivity of a derived code `f`: case on both keys; distinct constructors differ in the
head, equal heads give equal framed field codes, hence equal fields. -/
macro "store_key_inj " f:ident : tactic =>
  `(tactic| (intro a b h; cases a <;> cases b <;>
      simp_all [$f:ident, frames_eq_iff, code_eq_iff]))

end Minidregg.Theory.StoreKey

namespace Minidregg.Theory.DeriveStoreKey

open Lean Elab Command Term Meta Deriving Parser.Term
open TSyntax.Compat

def mkCodeFun (ctx : Deriving.Context) (indVal : InductiveVal) : TermElabM Command := do
  let header ← mkHeader ``StoreKey 1 indVal
  let discrs ← mkDiscrs header indVal
  let mut alts : Array (TSyntax ``Parser.Term.matchAlt) := #[]
  let mut ctorIdx := 0
  for ctorName in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let alt ← forallTelescopeReducing ctorInfo.type fun xs type => do
      let type ← Core.betaReduce type
      let mut pats : Array Term := #[]
      for _ in [:indVal.numIndices] do
        pats := pats.push (← `(_))
      let mut args : Array Term := #[]
      for _ in [:indVal.numParams] do
        args := args.push (← `(_))
      let mut codes : Array Term := #[]
      for i in [:ctorInfo.numFields] do
        let x := xs[indVal.numParams + i]!
        if (← isProof x) || occursOrInType (← getLCtx) x type then
          args := args.push (← `(_))
        else
          let a := mkIdent (← mkFreshUserName `a)
          args := args.push a
          codes := codes.push (← `(Minidregg.Theory.StoreKey.code $a))
      let pat ← `(@$(mkIdent ctorName):ident $args:term*)
      let idx := Syntax.mkNumLit (toString ctorIdx)
      let rhs ← `($idx :: Minidregg.Theory.StoreKey.frames [$codes,*])
      let allPats := pats.push pat
      `(matchAltExpr| | $[$allPats],* => $rhs:term)
    alts := alts.push alt
    ctorIdx := ctorIdx + 1
  let body ← `(match $[$discrs],* with $alts:matchAlt*)
  `(def $(mkIdent ctx.auxFunNames[0]!):ident $(header.binders):bracketedBinder* : List Nat := $body:term)

def mkInstanceCmd (ctx : Deriving.Context) (indVal : InductiveVal) : TermElabM Command := do
  let argNames ← mkInductArgNames indVal
  let binders ← mkImplicitBinders argNames
  let binders := binders ++ (← mkInstImplicitBinders ``StoreKey indVal argNames)
  let indType ← mkInductiveApp indVal argNames
  let f := mkIdent ctx.auxFunNames[0]!
  `(instance $(mkIdent ctx.instName):ident $binders:implicitBinder* :
      Minidregg.Theory.StoreKey $indType :=
      Minidregg.Theory.StoreKey.ofCode (fun x => $f x) (by store_key_inj $f))

def mkStoreKeyInstance (declName : Name) : CommandElabM Unit := do
  withoutExposeFromCtors declName do
    let cmds ← liftTermElabM do
      let ctx ← Deriving.mkContext ``StoreKey "storeKeyCode" declName (supportsRec := false)
      let indVal := ctx.typeInfos[0]!
      return #[← mkCodeFun ctx indVal, ← mkInstanceCmd ctx indVal]
    cmds.forM elabCommand

def mkStoreKeyHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size == 1 then
    for declName in declNames do
      mkStoreKeyInstance declName
    return true
  else
    return false

initialize registerDerivingHandler ``StoreKey mkStoreKeyHandler

end Minidregg.Theory.DeriveStoreKey
