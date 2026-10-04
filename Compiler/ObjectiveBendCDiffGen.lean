/- A seeded generator of random WELL-TYPED Core4 programs, and a type-preserving
shrinker, for the C-vs-Lean differential (native/objective-emit/differential.py).

  gen    START COUNT OUT_ROOT [MAX_FUEL]   one program per seed in [START, START+COUNT)
  shrink TYPED_JSON RESPONSES_JSON OUT_DIR  every one-step shrink of a packet that still checks,
                                            smallest first, as a packet root (index.json)

The generator is TYPE-DIRECTED: `genTerm ctx pos ty fuel` builds a term of exactly
`ty` under the binder types `ctx`, recording the lambda / injection / perform
annotations at the positions `Theory/ObjectiveBendTyping.infer` reads them from.
It never decides well-typedness itself: every program is then run through the real
checker (`check`, the function the typing theorems are about) and only an accepted
one is emitted; a refusal is counted and resampled, so the acceptance rate is a
MEASUREMENT of how far the enumerator and the checker agree (printed by `gen`).
Programs are written as the exact `core.v2` / `typed-core.v3` packets the rest of
the pipeline reads, and the packet is decoded back and compared with the generated
term before it is written.

The grammar reached: bound, lam, app, mix, fix, specification, prototype, reflect,
metadata, project, nat, boolean, label, binary (all five primitives), extend,
record, get (including a field shadowed by an extend), ifZero, inject, case,
ifBool, and activities (perform, done, the effect case) with responses.
Binder quantities are `unrestricted` throughout: ownership never changes what the
machine does, and every binder type is shareable. -/
import Lean.Data.Json
import Theory.ObjectiveBendTyping
import Theory.ObjectiveBendDemandData
import Compiler.ObjectiveBendDataWire

open Lean (Json toJson)
open Minidregg.Theory.ObjectiveBendTypes
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandData (Data)

namespace Minidregg.Compiler.ObjectiveBendCDiffGen
set_option autoImplicit false

instance : Inhabited Term := ⟨.nat 0⟩
instance : Inhabited Data := ⟨.natural 0⟩
instance : Inhabited Ty := ⟨.natural⟩
instance : Inhabited Primitive := ⟨.add⟩

structure St where
  seed : UInt64
  annotations : List (List Nat × LambdaAnnotation) := []

instance : Inhabited St := ⟨{ seed := 0 }⟩

abbrev G := StateM St

/-! ## Randomness (splitmix64) -/

def next : G UInt64 := do
  let s ← get
  let z := s.seed + 0x9E3779B97F4A7C15
  set { s with seed := z }
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  pure (z ^^^ (z >>> 31))

def below (n : Nat) : G Nat := do
  if n == 0 then pure 0 else pure ((← next).toNat % n)

def choose {α : Type} [Inhabited α] (alts : List (Nat × G α)) : G α := do
  let total := alts.foldl (fun acc pair => acc + pair.1) 0
  let mut r ← below total
  for (w, act) in alts do
    if r < w then return (← act)
    r := r - w
  match alts with
  | [] => pure default
  | (_, act) :: _ => act

def pickFrom {α : Type} [Inhabited α] (xs : Array α) : G α := do
  let i ← below xs.size
  pure xs[i]!

def annotate (pos : List Nat) (annotation : LambdaAnnotation) : G Unit :=
  modify fun s => { s with annotations := (pos, annotation) :: s.annotations }

/-- `k` distinct elements of `names`, in `names`' own order. -/
def subset (names : Array String) (lo hi : Nat) : G (List String) := do
  let k := lo + (← below (hi - lo + 1))
  let mut remaining := names.toList
  let mut chosen : List String := []
  for _ in [0:k] do
    if remaining.isEmpty then break
    let idx ← below remaining.length
    chosen := chosen ++ [remaining[idx]!]
    remaining := remaining.eraseIdx idx
  pure (names.toList.filter (chosen.contains ·))

def fieldNames : Array String := #["a", "b", "c", "d", "e"]
def tagNames : Array String := #["p", "q", "r"]
def labelValues : Array String := #["x", "y", "ok", "no", "true", "false", "", "λ"]

/-! ## Types -/

def rowOf : List (String × Ty) → Ty
  | [] => .emptyRow
  | (n, t) :: r => .field n t (rowOf r)

def rowFields : Ty → List (String × Ty)
  | .field n t r => (n, t) :: rowFields r
  | _ => []

mutual
partial def genTy (depth : Nat) : G Ty :=
  if depth == 0 then
    choose [(5, pure Ty.natural), (2, pure Ty.boolean), (2, pure Ty.label)]
  else
    choose [
      (10, genTy 0),
      (4, do
        let d ← genTy (depth - 1)
        let c ← genTy (depth - 1)
        pure (Ty.arrow .reusable .unrestricted d c)),
      (4, genRecordTy depth),
      (3, genVariantTy depth),
      (1, do
        let m ← genTy 0
        let e ← genTy (depth - 1)
        pure (Ty.specification m e)),
      (1, do
        let s ← genTy 0
        let t ← genTy (depth - 1)
        pure (Ty.prototype s t))]

partial def genRecordTy (depth : Nat) : G Ty := do
  let names ← subset fieldNames 0 3
  let members ← names.mapM fun n => do pure (n, ← genTy (depth - 1))
  pure (rowOf members)

partial def genVariantTy (depth : Nat) : G Ty := do
  let tags ← subset tagNames 1 3
  let members ← tags.mapM fun n => do pure (n, ← genTy (depth - 1))
  pure (Ty.variant (rowOf members))
end

/-- First-order data types: what a Plan and a response are made of. -/
partial def genDataTy (depth : Nat) : G Ty :=
  if depth == 0 then
    choose [(5, pure Ty.natural), (2, pure Ty.boolean), (2, pure Ty.label)]
  else
    choose [
      (8, genDataTy 0),
      (3, do
        let names ← subset fieldNames 0 2
        let members ← names.mapM fun n => do pure (n, ← genDataTy (depth - 1))
        pure (rowOf members)),
      (2, do
        let tags ← subset tagNames 1 2
        let members ← tags.mapM fun n => do pure (n, ← genDataTy (depth - 1))
        pure (Ty.variant (rowOf members)))]

partial def genData (ty : Ty) : G Data :=
  match ty with
  | .natural => do pure (.natural (← below 7))
  | .boolean => do pure (.boolean ((← below 2) == 1))
  | .label => do pure (.label (← pickFrom labelValues))
  | .variant row => do
      let members := rowFields row
      match members with
      | [] => pure (.natural 0)
      | _ =>
        let (tag, payload) := members[(← below members.length)]!
        pure (.variant tag (← genData payload))
  | row => do
      let members := rowFields row
      pure (.record (← members.mapM fun (n, t) => do pure (n, ← genData t)))

/-! ## Terms -/

def varIdx (ctx : List Ty) (ty : Ty) : List Nat :=
  (List.range ctx.length).filter fun i => ctx[i]? == some ty

/-- Binders whose type is a function into `ty`: (index, domain). -/
def funVars (ctx : List Ty) (ty : Ty) : List (Nat × Ty) :=
  (List.range ctx.length).filterMap fun i =>
    match ctx[i]? with
    | some (Ty.arrow _ _ d c) => if c == ty then some (i, d) else none
    | _ => none

def genNat : G Nat :=
  choose [(8, below 5), (3, below 1000), (1, do pure (4294967295 + (← below 3))),
    (1, do pure (18446744073709551616 + (← below 5)))]

mutual
partial def genTerm (ctx : List Ty) (pos : List Nat) (ty : Ty) (fuel : Nat) : G Term := do
  let vars := varIdx ctx ty
  let mut alts : List (Nat × G Term) := [(if fuel == 0 then 6 else 3, intro ctx pos ty fuel)]
  if !vars.isEmpty then
    alts := alts ++ [(if fuel == 0 then 6 else 4, do pure (Term.bound (← pickFrom vars.toArray)))]
  if fuel > 0 then
    alts := alts ++ compound ctx pos ty fuel
  choose alts

partial def intro (ctx : List Ty) (pos : List Nat) (ty : Ty) (fuel : Nat) : G Term := do
  let f := fuel - 1
  match ty with
  | .natural => do pure (Term.nat (← genNat))
  | .boolean => do pure (Term.boolean ((← below 2) == 1))
  | .label => do pure (Term.label (← pickFrom labelValues))
  | .arrow reuse quantity d c => do
      annotate pos ⟨d, c, quantity, reuse⟩
      pure (Term.lam (← genTerm (d :: ctx) (pos ++ [0]) c f))
  | .variant row => do
      let members := rowFields row
      let (tag, payload) := members[(← below members.length)]!
      annotate pos ⟨payload, ty, .unrestricted, .reusable⟩
      pure (Term.inject tag (← genTerm ctx (pos ++ [0]) payload f))
  | .specification m e => do
      let descriptor ← genTerm ctx (pos ++ [0]) m f
      let ext ← genTerm ctx (pos ++ [1]) e f
      pure (Term.specification descriptor ext)
  | .prototype s t => do
      let spec ← genTerm ctx (pos ++ [0]) s f
      let target ← genTerm ctx (pos ++ [1]) t f
      pure (Term.prototype spec target)
  | row => do
      pure (Term.record (← genFields ctx pos (rowFields row) f))

partial def genFields (ctx : List Ty) (pos : List Nat) (fields : List (String × Ty)) (fuel : Nat) :
    G (List (String × Term)) := do
  let mut out : List (String × Term) := []
  let mut i := 0
  for (name, ty) in fields do
    out := out ++ [(name, ← genTerm ctx (pos ++ [i]) ty fuel)]
    i := i + 1
  pure out

/-- A term whose CALLABLE type is `A → B`: a function, or a specification
wrapping one (`callable` looks through the specification). -/
partial def genFun (ctx : List Ty) (pos : List Nat) (a b : Ty) (fuel : Nat) : G Term :=
  choose [
    (6, genTerm ctx pos (Ty.arrow .reusable .unrestricted a b) fuel),
    (1, do
      let m ← genTy 0
      let descriptor ← genTerm ctx (pos ++ [0]) m fuel
      let ext ← genTerm ctx (pos ++ [1]) (Ty.arrow .reusable .unrestricted a b) fuel
      pure (Term.specification descriptor ext))]

partial def genMix (ctx : List Ty) (pos : List Nat) (self inherited provided : Ty) (fuel : Nat) : G Term := do
  let middle ← genTy 1
  let lower ← genFun ctx (pos ++ [0]) self (Ty.arrow .reusable .unrestricted inherited middle) fuel
  let upper ← genFun ctx (pos ++ [1]) self (Ty.arrow .reusable .unrestricted middle provided) fuel
  pure (Term.mix lower upper)

partial def genFix (ctx : List Ty) (pos : List Nat) (target : Ty) (fuel : Nat) : G Term := do
  let inherited ← genTy 1
  let spec ← choose [
    (6, genFun ctx (pos ++ [0]) target (Ty.arrow .reusable .unrestricted inherited target) fuel),
    (3, genMix ctx (pos ++ [0]) target inherited target fuel)]
  let seed ← genTerm ctx (pos ++ [1]) inherited fuel
  pure (Term.fix spec seed)

partial def genGet (ctx : List Ty) (pos : List Nat) (ty : Ty) (fuel : Nat) : G Term := do
  let name ← pickFrom fieldNames
  let others ← subset (fieldNames.filter (· != name)) 0 2
  let otherFields ← others.mapM fun n => do pure (n, ← genTy 1)
  let fields := (name, ty) :: otherFields
  if (← below 4) == 0 then
    -- the field is added by an extend that shadows a base field of the same name
    let baseNames ← subset fieldNames 0 3
    let baseFields ← baseNames.mapM fun n => do pure (n, ← genTy 1)
    let base ← genTerm ctx (pos ++ [0, 0]) (rowOf baseFields) fuel
    let added ← genFields ctx (pos ++ [0, 1]) fields fuel
    pure (Term.get (Term.extend base added) name)
  else
    pure (Term.get (← genTerm ctx (pos ++ [0]) (rowOf fields) fuel) name)

partial def genCase (ctx : List Ty) (pos : List Nat) (ty : Ty) (fuel : Nat) : G Term := do
  let tags ← subset tagNames 1 3
  let members ← tags.mapM fun n => do pure (n, ← genTy 1)
  let scrutinee ← genTerm ctx (pos ++ [0]) (Ty.variant (rowOf members)) fuel
  let mut arms : List (String × Term) := []
  let mut i := 0
  for (tag, payload) in members do
    arms := arms ++ [(tag, ← genTerm (payload :: ctx) (pos ++ [1, i]) ty fuel)]
    i := i + 1
  pure (Term.case scrutinee arms)

partial def genExtend (ctx : List Ty) (pos : List Nat) (ty : Ty) (fuel : Nat) : G Term := do
  let members := rowFields ty
  let k := 1 + (← below members.length)
  let added := members.take k
  let inherited := members.drop k
  let base ← genTerm ctx (pos ++ [0]) (rowOf inherited) fuel
  let fields ← genFields ctx (pos ++ [1]) added fuel
  pure (Term.extend base fields)

/-- A well-founded loop: `(fix (λself. λseed. λn. ifZero n BASE (… self pred …))) K`, so a
program does real work (the tick count scales with K, naturals grow into many limbs). -/
partial def genRecursion (ctx : List Ty) (pos : List Nat) (result : Ty) (fuel : Nat) : G Term := do
  let seedTy ← genTy 1
  let fnTy := Ty.arrow .reusable .unrestricted .natural result
  let specTy := Ty.arrow .reusable .unrestricted seedTy fnTy
  let spec := pos ++ [0, 0]
  annotate spec ⟨fnTy, specTy, .unrestricted, .reusable⟩
  annotate (spec ++ [0]) ⟨seedTy, fnTy, .unrestricted, .reusable⟩
  annotate (spec ++ [0, 0]) ⟨.natural, result, .unrestricted, .reusable⟩
  let body := spec ++ [0, 0, 0]
  let inner : List Ty := Ty.natural :: seedTy :: fnTy :: ctx
  let zero ← genTerm inner (body ++ [1]) result fuel
  let call : Term := Term.app (Term.bound 3) (Term.bound 0)
  let successor ← match result with
    | .natural => do
        let other ← genTerm (Ty.natural :: inner) (body ++ [2, 1]) .natural fuel
        match (← below 3) with
        | 0 => pure (Term.binary .add call other)
        | 1 => pure (Term.binary .multiply (Term.bound 1) call)
        | _ => pure (Term.binary .add (Term.binary .multiply (Term.bound 1) call) other)
    | .boolean => do
        let other ← genTerm (Ty.natural :: inner) (body ++ [2, 2]) .boolean fuel
        pure (Term.ifBool (Term.binary .equal (Term.bound 1) (Term.bound 0)) call other)
    | _ => genTerm (Ty.natural :: inner) (body ++ [2]) result fuel
  let seed ← genTerm ctx (pos ++ [0, 1]) seedTy fuel
  let count ← choose [(8, below 8), (3, below 20), (1, do pure (30 + (← below 15)))]
  pure (Term.app (Term.fix (Term.lam (Term.lam (Term.lam
    (Term.ifZero (Term.bound 0) zero successor)))) seed) (Term.nat count))

partial def compound (ctx : List Ty) (pos : List Nat) (ty : Ty) (fuel : Nat) : List (Nat × G Term) :=
  let f := fuel - 1
  let common : List (Nat × G Term) := [
    (4, do
      let a ← genTy 1
      let fn ← genFun ctx (pos ++ [0]) a ty f
      let arg ← genTerm ctx (pos ++ [1]) a f
      pure (Term.app fn arg)),
    (3, do
      let v ← genTerm ctx (pos ++ [0]) .natural f
      let z ← genTerm ctx (pos ++ [1]) ty f
      let s ← genTerm (Ty.natural :: ctx) (pos ++ [2]) ty f
      pure (Term.ifZero v z s)),
    (3, do
      let c ← genTerm ctx (pos ++ [0]) .boolean f
      let t ← genTerm ctx (pos ++ [1]) ty f
      let e ← genTerm ctx (pos ++ [2]) ty f
      pure (Term.ifBool c t e)),
    (3, genGet ctx pos ty f),
    (3, genCase ctx pos ty f),
    (2, genFix ctx pos ty f),
    (4, genRecursion ctx pos ty f),
    (1, do
      let e ← genTy 1
      let m ← genTerm ctx (pos ++ [0, 0]) ty f
      let ex ← genTerm ctx (pos ++ [0, 1]) e f
      pure (Term.metadata (Term.specification m ex))),
    (1, do
      let t ← genTy 1
      let s ← genTerm ctx (pos ++ [0, 0]) ty f
      let tg ← genTerm ctx (pos ++ [0, 1]) t f
      pure (Term.reflect (Term.prototype s tg))),
    (1, do
      let s ← genTy 1
      let sp ← genTerm ctx (pos ++ [0, 0]) s f
      let tg ← genTerm ctx (pos ++ [0, 1]) ty f
      pure (Term.project (Term.prototype sp tg)))]
  let calls : List (Nat × G Term) :=
    match funVars ctx ty with
    | [] => []
    | vars => [(5, do
        let (i, d) ← pickFrom vars.toArray
        let arg ← genTerm ctx (pos ++ [1]) d f
        pure (Term.app (Term.bound i) arg))]
  let shaped : List (Nat × G Term) :=
    match ty with
    | .natural => [(6, do
        let op ← pickFrom #[Primitive.add, Primitive.multiply]
        let l ← genTerm ctx (pos ++ [0]) .natural f
        let r ← genTerm ctx (pos ++ [1]) .natural f
        pure (Term.binary op l r))]
    | .boolean => [(6, do
        match (← below 3) with
        | 0 =>
          let l ← genTerm ctx (pos ++ [0]) .natural f
          let r ← genTerm ctx (pos ++ [1]) .natural f
          pure (Term.binary .equal l r)
        | 1 =>
          let l ← genTerm ctx (pos ++ [0]) .boolean f
          let r ← genTerm ctx (pos ++ [1]) .boolean f
          pure (Term.binary .conjunction l r)
        | _ =>
          let l ← genTerm ctx (pos ++ [0]) .label f
          let r ← genTerm ctx (pos ++ [1]) .label f
          pure (Term.binary .labelEqual l r))]
    | .field _ _ _ => [(4, genExtend ctx pos ty f)]
    | .arrow .reusable .unrestricted s (.arrow .reusable .unrestricted i p) => [(3, genMix ctx pos s i p f)]
    | _ => []
  common ++ calls ++ shaped
end

/-! ## Activities -/

mutual
partial def genAct (ctx : List Ty) (pos : List Nat) (plan resp : Ty) (respRow : List (String × Ty))
    (result : Ty) (fuel : Nat) : G Term := do
  let sig : LambdaAnnotation := ⟨plan, resp, .unrestricted, .reusable⟩
  let f := fuel - 1
  let done : G Term := do
    annotate pos sig
    pure (Term.done (← genTerm ctx (pos ++ [0]) result f))
  if fuel == 0 then done
  else choose [
    (3, done),
    (6, do
      annotate (pos ++ [0]) sig
      let planTerm ← genTerm ctx (pos ++ [0, 0]) plan f
      let mut arms : List (String × Term) := []
      let mut i := 0
      for (tag, payload) in respRow do
        arms := arms ++ [(tag, ← genAct (payload :: ctx) (pos ++ [1, i]) plan resp respRow result f)]
        i := i + 1
      pure (Term.case (Term.perform planTerm) arms)),
    (1, do
      let c ← genTerm ctx (pos ++ [0]) .boolean f
      let t ← genAct ctx (pos ++ [1]) plan resp respRow result f
      let e ← genAct ctx (pos ++ [2]) plan resp respRow result f
      pure (Term.ifBool c t e))]
end

/-! ## Packets -/

def primitiveName : Primitive → String
  | .add => "add" | .multiply => "multiply" | .equal => "equal"
  | .conjunction => "conjunction" | .labelEqual => "labelEqual"

partial def termJson : Term → Json
  | .bound i => Json.mkObj [("tag", "bound"), ("index", toJson (toString i))]
  | .lam b => Json.mkObj [("tag", "lam"), ("body", termJson b)]
  | .app f a => Json.mkObj [("tag", "app"), ("fn", termJson f), ("arg", termJson a)]
  | .mix l u => Json.mkObj [("tag", "mix"), ("lower", termJson l), ("upper", termJson u)]
  | .fix s i => Json.mkObj [("tag", "fix"), ("spec", termJson s), ("seed", termJson i)]
  | .specification m e => Json.mkObj [("tag", "specification"), ("metadata", termJson m), ("extension", termJson e)]
  | .prototype s t => Json.mkObj [("tag", "prototype"), ("spec", termJson s), ("target", termJson t)]
  | .reflect v => Json.mkObj [("tag", "reflect"), ("value", termJson v)]
  | .metadata v => Json.mkObj [("tag", "metadata"), ("value", termJson v)]
  | .project v => Json.mkObj [("tag", "project"), ("value", termJson v)]
  | .nat n => Json.mkObj [("tag", "nat"), ("value", toJson (toString n))]
  | .boolean b => Json.mkObj [("tag", "boolean"), ("value", toJson b)]
  | .label s => Json.mkObj [("tag", "label"), ("value", toJson s)]
  | .binary p l r => Json.mkObj [("tag", "binary"), ("primitive", toJson (primitiveName p)),
      ("left", termJson l), ("right", termJson r)]
  | .extend i fs => Json.mkObj [("tag", "extend"), ("inherited", termJson i),
      ("fields", Json.arr (fs.map fun field => Json.mkObj [("name", toJson field.1), ("value", termJson field.2)]).toArray)]
  | .record fs => Json.mkObj [("tag", "record"),
      ("fields", Json.arr (fs.map fun field => Json.mkObj [("name", toJson field.1), ("value", termJson field.2)]).toArray)]
  | .get t n => Json.mkObj [("tag", "get"), ("target", termJson t), ("name", toJson n)]
  | .ifZero v z s => Json.mkObj [("tag", "ifZero"), ("value", termJson v), ("zero", termJson z), ("successor", termJson s)]
  | .inject l p => Json.mkObj [("tag", "inject"), ("label", toJson l), ("payload", termJson p)]
  | .case s arms => Json.mkObj [("tag", "case"), ("scrutinee", termJson s),
      ("arms", Json.arr (arms.map fun arm => Json.mkObj [("label", toJson arm.1), ("body", termJson arm.2)]).toArray)]
  | .ifBool c t e => Json.mkObj [("tag", "ifBool"), ("condition", termJson c), ("whenTrue", termJson t), ("whenFalse", termJson e)]
  | .perform p => Json.mkObj [("tag", "perform"), ("plan", termJson p)]
  | .done v => Json.mkObj [("tag", "done"), ("value", termJson v)]

def annotationJson (entry : List Nat × LambdaAnnotation) : Json :=
  Json.mkObj [("path", Json.arr (entry.1.map fun n => toJson n).toArray),
    ("domain", typeJson entry.2.domain), ("codomain", typeJson entry.2.codomain),
    ("parameter", quantityJson entry.2.parameter), ("reuse", reuseJson entry.2.reuse)]

def typedPacket (term : Term) (annotations : List (List Nat × LambdaAnnotation)) : Json :=
  Json.mkObj [("schema", "dregg.objective-bend.typed-core.v3"), ("types", Json.arr #[]),
    ("term", termJson term), ("annotations", Json.arr (annotations.map annotationJson).toArray),
    ("bounds", Json.arr #[]), ("shareableVariables", Json.arr #[]), ("context", Json.arr #[]),
    ("fuel", toJson 4096)]

def corePacket (term : Term) (note : String) : Json :=
  Json.mkObj [("schema", "dregg.objective-bend.core.v2"), ("edition", "objective-bend-1"),
    ("note", toJson note), ("term", termJson term)]

partial def size : Term → Nat
  | .bound _ | .nat _ | .boolean _ | .label _ => 1
  | .lam b | .reflect b | .metadata b | .project b | .perform b | .done b => size b + 1
  | .app a b | .mix a b | .fix a b | .specification a b | .prototype a b
  | .binary _ a b => size a + size b + 1
  | .extend i fs => size i + (fs.map fun f => size f.2).foldl (· + ·) 0 + 1
  | .record fs => (fs.map fun f => size f.2).foldl (· + ·) 1
  | .get t _ | .inject _ t => size t + 1
  | .ifZero a b c | .ifBool a b c => size a + size b + size c + 1
  | .case s arms => size s + (arms.map fun f => size f.2).foldl (· + ·) 0 + 1

def annotationsFn (list : List (List Nat × LambdaAnnotation)) : Annotations :=
  fun path => (list.find? (·.1 == path)).map (·.2)

def accepted (term : Term) (annotations : List (List Nat × LambdaAnnotation)) : Bool :=
  (check ⟨term, annotationsFn annotations, {}⟩ [] 4096).isSome

/-- One program. `kind`: `pure` or `activity`; the responses an activity is resumed with. -/
structure Program where
  term : Term
  annotations : List (List Nat × LambdaAnnotation)
  responses : List Data
  kind : String

def genProgram (maxFuel : Nat) : G Program := do
  modify fun s => { s with annotations := [] }
  let fuel := 2 + (← below (maxFuel - 1))
  if (← below 5) == 0 then
    let planRow ← do
      let tags ← subset tagNames 1 2
      tags.mapM fun n => do pure (n, ← genDataTy 1)
    let respRow ← do
      let tags ← subset tagNames 1 2
      tags.mapM fun n => do pure (n, ← genDataTy 1)
    let plan := Ty.variant (rowOf planRow)
    let resp := Ty.variant (rowOf respRow)
    let result ← choose [(5, pure Ty.natural), (2, pure Ty.boolean), (2, pure Ty.label)]
    let term ← genAct [] [] plan resp respRow result fuel
    let count ← below 5
    let mut responses : List Data := []
    for _ in [0:count] do
      responses := responses ++ [← genData resp]
    pure { term, annotations := (← get).annotations, responses, kind := "activity" }
  else
    let ty ← choose [(10, pure Ty.natural), (3, pure Ty.boolean), (2, pure Ty.label),
      (2, genRecordTy 2), (2, genVariantTy 2), (2, genTy 2)]
    let term ← genTerm [] [] ty fuel
    pure { term, annotations := (← get).annotations, responses := [], kind := "pure" }

/-- Seed `s` is the same program on every machine. -/
def generate (seed maxFuel : Nat) (attempts : Nat := 64) : Option (Program × Nat) :=
  let init : St := { seed := (UInt64.ofNat seed) * 0xD1B54A32D192ED03 + 0x2545F4914F6CDD1D }
  let rec go (state : St) : Nat → Option (Program × Nat)
    | 0 => none
    | n + 1 =>
      let (program, state) := (genProgram maxFuel).run state
      if accepted program.term program.annotations && size program.term ≤ 3000 then
        some (program, attempts - n - 1)
      else go state n
  go init attempts

def dataArray (responses : List Data) : Json :=
  Json.arr (responses.map Minidregg.Compiler.ObjectiveBendDataWire.dataJson).toArray

def writePacketFiles (dir : String) (term : Term) (annotations : List (List Nat × LambdaAnnotation))
    (responses : List Data) (note : String) : IO Unit := do
  IO.FS.createDirAll dir
  IO.FS.writeFile s!"{dir}/source.core.json" ((corePacket term note).pretty ++ "\n")
  IO.FS.writeFile s!"{dir}/source.typed.json" ((typedPacket term annotations).compress ++ "\n")
  IO.FS.writeFile s!"{dir}/responses.json" ((dataArray responses).compress ++ "\n")

def indexEntry (name root kind : String) (seed attempts nodes : Nat) : Json :=
  Json.mkObj [("name", toJson name), ("status", toJson "ok"),
    ("core", toJson s!"{root}/{name}/source.core.json"),
    ("typed", toJson s!"{root}/{name}/source.typed.json"),
    ("responses", toJson s!"{root}/{name}/responses.json"),
    ("expectTyping", toJson "accepted"), ("kind", toJson kind),
    ("seed", toJson seed), ("attempts", toJson attempts), ("nodes", toJson nodes)]

def runGen (start count : Nat) (root : String) (maxFuel : Nat) : IO UInt32 := do
  IO.FS.createDirAll root
  let mut index : Array Json := #[]
  let mut acceptedCount := 0
  let mut rejected := 0
  let mut failed := 0
  let mut pureCount := 0
  let mut activityCount := 0
  let mut nodes := 0
  let mut maxNodes := 0
  for seed in [start:start + count] do
    match generate seed maxFuel with
    | none => failed := failed + 1
    | some (program, attempts) =>
      -- the packet is what the machine will read: decode it back and compare
      let encoded := (corePacket program.term "").pretty
      let roundTrip : Bool := match Json.parse encoded with
        | .ok json => match json.getObjVal? "term" with
          | .ok tj => match decodeTerm 4096 tj with
            | .ok decoded => reprStr decoded == reprStr program.term
            | .error _ => false
          | .error _ => false
        | .error _ => false
      if !roundTrip then
        IO.eprintln s!"gen: seed {seed}: the packet does not decode to the generated term"
        return 2
      let name := s!"g{seed}"
      writePacketFiles s!"{root}/{name}" program.term program.annotations program.responses
        s!"generated by ObjectiveBendCDiffGen: seed {seed}, maxFuel {maxFuel}, kind {program.kind}"
      let n := size program.term
      index := index.push (indexEntry name root program.kind seed attempts n)
      acceptedCount := acceptedCount + 1
      rejected := rejected + attempts
      nodes := nodes + n
      maxNodes := max maxNodes n
      if program.kind == "activity" then activityCount := activityCount + 1 else pureCount := pureCount + 1
  IO.FS.writeFile s!"{root}/index.json" ((Json.arr index).pretty ++ "\n")
  -- acceptance rate: accepted / (accepted + rejected samples)
  let samples := acceptedCount + rejected
  IO.println (Json.mkObj [("seedStart", toJson start), ("seedCount", toJson count),
    ("emitted", toJson acceptedCount), ("genFailed", toJson failed), ("rejectedSamples", toJson rejected),
    ("acceptancePermille", toJson (if samples == 0 then 0 else acceptedCount * 1000 / samples)),
    ("pure", toJson pureCount), ("activity", toJson activityCount),
    ("meanNodes", toJson (if acceptedCount == 0 then 0 else nodes / acceptedCount)),
    ("maxNodes", toJson maxNodes)]).compress
  pure 0

/-! ## Shrinking: every one-step reduction that still checks -/

/-- The annotation table after the subtree at `path` is replaced by `replacement`, whose
own annotations (relative to its root) are `inner`: entries under `path` are dropped,
`inner` is re-rooted at `path`. -/
def reroot (annotations : List (List Nat × LambdaAnnotation)) (path : List Nat)
    (inner : List (List Nat × LambdaAnnotation)) : List (List Nat × LambdaAnnotation) :=
  annotations.filter (fun entry => !(path.isPrefixOf entry.1)) ++ inner.map fun entry => (path ++ entry.1, entry.2)

/-- Entries at or under `path`, made relative to it. -/
def relative (annotations : List (List Nat × LambdaAnnotation)) (path : List Nat) :
    List (List Nat × LambdaAnnotation) :=
  annotations.filterMap fun entry =>
    if path.isPrefixOf entry.1 then some (entry.1.drop path.length, entry.2) else none

def children : Term → List Term
  | .bound _ | .nat _ | .boolean _ | .label _ => []
  | .lam b | .reflect b | .metadata b | .project b | .perform b | .done b | .get b _ | .inject _ b => [b]
  | .app a b | .mix a b | .fix a b | .specification a b | .prototype a b | .binary _ a b => [a, b]
  | .extend i fs => i :: fs.map (·.2)
  | .record fs => fs.map (·.2)
  | .ifZero a b c | .ifBool a b c => [a, b, c]
  | .case s arms => s :: arms.map (·.2)

/-- The child path steps of `term`, in `children` order, as the positions `infer` uses. -/
def childSteps : Term → List (List Nat)
  | .bound _ | .nat _ | .boolean _ | .label _ => []
  | .lam _ | .reflect _ | .metadata _ | .project _ | .perform _ | .done _ | .get _ _ | .inject _ _ => [[0]]
  | .app _ _ | .mix _ _ | .fix _ _ | .specification _ _ | .prototype _ _ | .binary _ _ _ => [[0], [1]]
  | .extend _ fs => [0] :: (List.range fs.length).map fun i => [1, i]
  | .record fs => (List.range fs.length).map fun i => [i]
  | .ifZero _ _ _ | .ifBool _ _ _ => [[0], [1], [2]]
  | .case _ arms => [0] :: (List.range arms.length).map fun i => [1, i]

def replaceChild (term : Term) (index : Nat) (new : Term) : Term :=
  let at_ := fun (xs : List (String × Term)) (i : Nat) => xs.mapIdx fun j f => if j == i then (f.1, new) else f
  match term, index with
  | .lam _, 0 => .lam new
  | .reflect _, 0 => .reflect new
  | .metadata _, 0 => .metadata new
  | .project _, 0 => .project new
  | .perform _, 0 => .perform new
  | .done _, 0 => .done new
  | .get _ n, 0 => .get new n
  | .inject l _, 0 => .inject l new
  | .app _ b, 0 => .app new b | .app a _, 1 => .app a new
  | .mix _ b, 0 => .mix new b | .mix a _, 1 => .mix a new
  | .fix _ b, 0 => .fix new b | .fix a _, 1 => .fix a new
  | .specification _ b, 0 => .specification new b | .specification a _, 1 => .specification a new
  | .prototype _ b, 0 => .prototype new b | .prototype a _, 1 => .prototype a new
  | .binary p _ b, 0 => .binary p new b | .binary p a _, 1 => .binary p a new
  | .extend _ fs, 0 => .extend new fs
  | .extend i fs, k + 1 => .extend i (at_ fs k)
  | .record fs, k => .record (at_ fs k)
  | .ifZero _ b c, 0 => .ifZero new b c | .ifZero a _ c, 1 => .ifZero a new c | .ifZero a b _, 2 => .ifZero a b new
  | .ifBool _ b c, 0 => .ifBool new b c | .ifBool a _ c, 1 => .ifBool a new c | .ifBool a b _, 2 => .ifBool a b new
  | .case _ arms, 0 => .case new arms
  | .case s arms, k + 1 => .case s (arms.mapIdx fun j f => if j == k then (f.1, new) else f)
  | t, _ => t

/-- Every node of `term`: (child-index path, annotation position, subterm). -/
partial def nodes (term : Term) (idxs : List Nat := []) (path : List Nat := []) :
    List (List Nat × List Nat × Term) :=
  let kids := children term
  let steps := childSteps term
  (idxs, path, term) :: (List.range kids.length).flatMap fun i =>
    nodes kids[i]! (idxs ++ [i]) (path ++ steps[i]!)

partial def replaceIdx (term : Term) : List Nat → Term → Term
  | [], new => new
  | i :: rest, new => replaceChild term i (replaceIdx (children term)[i]! rest new)

def literals : List Term := [.nat 0, .nat 1, .boolean false, .boolean true, .label "x", .record []]

/-- All one-step shrinks that still check, as (term, annotations): replace a node by a
literal, or hoist one of its children into its place (annotations re-rooted). -/
def shrinks (term : Term) (annotations : List (List Nat × LambdaAnnotation)) :
    List (Term × List (List Nat × LambdaAnnotation)) :=
  let candidates := (nodes term).flatMap fun (idxs, path, node) =>
    let lits := if size node > 1 then
      literals.map fun lit => (replaceIdx term idxs lit, reroot annotations path []) else []
    let kids := children node
    let steps := childSteps node
    let hoists := (List.range kids.length).map fun i =>
      (replaceIdx term idxs kids[i]!, reroot annotations path (relative annotations (path ++ steps[i]!)))
    lits ++ hoists
  candidates.filter fun (t, a) => size t < size term && accepted t a

def parseTyped (json : Json) : Except String (Term × List (List Nat × LambdaAnnotation)) := do
  let table ← decodeTypeTable (← json.getObjVal? "types")
  let term ← decodeTerm termNestingCapacity (← json.getObjVal? "term")
  let entries ← (← (← json.getObjVal? "annotations").getArr?).toList.mapM fun entry => do
    let path ← (← (← entry.getObjVal? "path").getArr?).toList.mapM jsonNat
    pure (path, ← decodeLambda table entry)
  pure (term, entries)

def runShrink (typedPath responsesPath outDir : String) : IO UInt32 := do
  let text ← IO.FS.readFile typedPath
  let some (term, annotations) := (Json.parse text >>= parseTyped).toOption
    | IO.eprintln "shrink: typed packet refused"; return 2
  if !accepted term annotations then
    IO.eprintln "shrink: the packet does not check"; return 2
  let responses ← IO.FS.readFile responsesPath
  -- smallest first: the minimizer tests candidates in this order
  let candidates := (shrinks term annotations).toArray.qsort fun x y => size x.1 < size y.1
  let mut seen : List String := []
  let mut index : Array Json := #[]
  for (t, a) in candidates do
    let key := (typedPacket t a).compress
    if seen.contains key then continue
    seen := key :: seen
    let name := s!"s{index.size}"
    let dir := s!"{outDir}/{name}"
    writePacketFiles dir t a [] s!"shrink candidate {index.size} of {typedPath}"
    IO.FS.writeFile s!"{dir}/responses.json" responses
    index := index.push (indexEntry name outDir "shrink" 0 0 (size t))
  IO.FS.writeFile s!"{outDir}/index.json" ((Json.arr index).pretty ++ "\n")
  IO.println (Json.mkObj [("candidates", toJson index.size), ("size", toJson (size term))]).compress
  pure 0

end Minidregg.Compiler.ObjectiveBendCDiffGen

def genMain (start count root : String) (fuel : Option String) : IO UInt32 := do
  match start.toNat?, count.toNat?, (fuel.map String.toNat?).getD (some 7) with
  | some s, some c, some f => Minidregg.Compiler.ObjectiveBendCDiffGen.runGen s c root (max f 2)
  | _, _, _ => IO.eprintln "gen: START COUNT MAX_FUEL are decimal naturals"; pure 2

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["gen", start, count, root] => genMain start count root none
  | ["gen", start, count, root, fuel] => genMain start count root (some fuel)
  | ["shrink", typed, responses, out] => Minidregg.Compiler.ObjectiveBendCDiffGen.runShrink typed responses out
  | _ =>
    IO.eprintln "usage: gen START COUNT OUT_ROOT [MAX_FUEL] | shrink TYPED_JSON RESPONSES_JSON OUT_DIR"
    pure 2
