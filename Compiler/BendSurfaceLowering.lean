/- Structural output bridge for the exact emitted WorldSurface source Data
constructors. No binary Plan or foreign interpreter replaces this result.
The source library ABI is checked against actual parsed Def ASTs in the complete
admitted Book, not by a matching constructor name or caller annotation.
-/
import Compiler.BendWorldSurface
import Compiler.BendSourceByteCodec
import Compiler.BendCoreAdmission
import Theory.BendLiveMachine

namespace Minidregg.Compiler.BendSurfaceLowering
open Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.BendTT
open BendWorldSurface
abbrev BTerm := Minidregg.Theory.BendTT.Term
set_option autoImplicit false

def fieldsTerm : List BTerm → BTerm
  | [] => .Lab "()"
  | value :: rest => .Tup .Q1 value (fieldsTerm rest)
def constructor (name : String) (fields : List BTerm) : BTerm :=
  .Tup .Q1 (.Lab name) (fieldsTerm fields)
def decodeFields : BTerm → Option (List BTerm)
  | .Lab "()" => some []
  | .Tup .Q1 value rest => (decodeFields rest).map (value :: ·)
  | _ => none
def decodeConstructor (name : String) : BTerm → Option (List BTerm)
  | .Tup .Q1 (.Lab found) fields =>
      if found = name then decodeFields fields else none
  | _ => none

def listTerm {α : Type} (encode : α → BTerm) : List α → BTerm
  | [] => constructor "Nil" []
  | value :: rest => constructor "Con" [encode value, listTerm encode rest]
def decodeList {α : Type} (decode : BTerm → Option α) : BTerm → Option (List α)
  | .Tup .Q1 (.Lab "Nil") (.Lab "()") => some []
  | .Tup .Q1 (.Lab "Con") (.Tup .Q1 value (.Tup .Q1 rest (.Lab "()"))) => do
      let value ← decode value
      let rest ← decodeList decode rest
      pure (value :: rest)
  | _ => none

theorem decode_fieldsTerm (fields : List BTerm) : decodeFields (fieldsTerm fields) = some fields := by
  induction fields with
  | nil => rfl
  | cons value rest ih => simp [fieldsTerm, decodeFields, ih]

theorem decode_constructor (name : String) (fields : List BTerm) :
    decodeConstructor name (constructor name fields) = some fields := by
  simp [decodeConstructor, constructor, decode_fieldsTerm]

theorem decode_listTerm {α : Type} (encode : α → BTerm) (decode : BTerm → Option α)
    (inverse : ∀ value, decode (encode value) = some value) (values : List α) :
    decodeList decode (listTerm encode values) = some values := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [listTerm, constructor, fieldsTerm, decodeList, inverse, ih]

def digestTerm (value : Digest) : BTerm :=
  BendSourceRepresentation.bytesTerm (digestStream.encode value)
def stringTerm (value : String) : BTerm :=
  BendSourceRepresentation.bytesTerm value.toUTF8.toList
def decodeDigest (term : BTerm) : Option Digest := do
  let bytes ← BendSourceRepresentation.decodeBytes term
  let (value, rest) ← digestStream.decodePrefix bytes
  if rest.isEmpty && decide (digestStream.encode value = bytes) then some value else none
def decodeString (term : BTerm) : Option String := do
  let bytes ← BendSourceRepresentation.decodeBytes term
  let value ← String.fromUTF8? ⟨bytes.toArray⟩
  if !value.contains (Char.ofNat 0) && decide (value.toUTF8.toList = bytes) then some value else none

theorem decode_digestTerm (value : Digest) : decodeDigest (digestTerm value) = some value := by
  have decoded := digestStream.decodePrefix_encode value []
  simp only [List.append_nil] at decoded
  simp [decodeDigest, digestTerm, BendSourceRepresentation.decode_bytesTerm, decoded]

def intentTerm (value : Intent) : BTerm := constructor "WorldSurface.Intent"
  [digestTerm value.artifact, stringTerm value.exportName, digestTerm value.program,
   BendSourceRepresentation.natTerm value.«instance», digestTerm value.expectedRoot,
   BendSourceRepresentation.bytesTerm value.arguments]
def nodeTerm (value : Node) : BTerm := constructor "WorldSurface.Node"
  [BendSourceRepresentation.natTerm value.tag, BendSourceRepresentation.natTerm value.slot,
   stringTerm value.label, BendSourceRepresentation.natListTerm value.children]
def sourceTerm (value : Surface) : BTerm := constructor "WorldSurface.Surface"
  [digestTerm value.artifact, stringTerm value.exportName, listTerm nodeTerm value.nodes,
   BendSourceRepresentation.natTerm value.root, listTerm intentTerm value.intents]

def decodeIntent (term : BTerm) : Option Intent := do
  let [artifact, exportName, program, instanceTerm, expectedRoot, arguments] ←
    decodeConstructor "WorldSurface.Intent" term | none
  pure ⟨← decodeDigest artifact, ← decodeString exportName, ← decodeDigest program,
    ← BendSourceRepresentation.decodeNat instanceTerm, ← decodeDigest expectedRoot,
    ← BendSourceRepresentation.decodeBytes arguments⟩
def decodeNode (term : BTerm) : Option Node := do
  let [tag, slot, label, children] ← decodeConstructor "WorldSurface.Node" term | none
  pure ⟨← BendSourceRepresentation.decodeNat tag, ← BendSourceRepresentation.decodeNat slot,
    ← decodeString label, ← BendSourceRepresentation.decodeNatList children⟩
def decodeSurface (term : BTerm) : Option Surface := do
  let [artifact, exportName, nodes, root, intents] ←
    decodeConstructor "WorldSurface.Surface" term | none
  pure ⟨← decodeDigest artifact, ← decodeString exportName, ← decodeList decodeNode nodes,
    ← BendSourceRepresentation.decodeNat root, ← decodeList decodeIntent intents⟩

/-- Check canonical structural inverse against the actual returned term. This
does not admit a claimed output: decoding happens first and every source byte,
constructor, field order and quantity must then reconstruct the exact result. -/
def lower (term : BTerm) : Option Surface := do
  let value ← decodeSurface term
  if sourceTerm value = term then some value else none

theorem lower_exact {term : BTerm} {value : Surface} (h : lower term = some value) :
    sourceTerm value = term := by
  unfold lower at h
  cases decoded : decodeSurface term with
  | none => simp [decoded] at h
  | some actual =>
      simp only [decoded, Option.bind_some] at h
      split at h
      · rename_i reconstruction
        cases Option.some.inj h
        exact reconstruction
      · contradiction

def decimalBound (value : Nat) : Bool := decide ((toString value).length ≤ 80)

def bounded (value : Surface) (observationCount : Nat) : Bool :=
  decide (observationCount ≤ 1024 ∧ value.nodes.length ≤ 1024 ∧ value.intents.length ≤ 1024 ∧
    value.root < value.nodes.length) &&
  decimalBound value.artifact.value &&
  !value.exportName.isEmpty && decide (value.exportName.toUTF8.size ≤ 16384) &&
  (List.finRange value.nodes.length).all (fun index =>
    let node := value.nodes[index]
    decide (node.tag ≤ 4 ∧ node.slot < 1024 ∧ node.label.toUTF8.size ≤ 16384 ∧ node.children.length ≤ 1024) &&
    node.children.all (fun child => decide (child < index.val)) &&
    (if node.tag = 1 ∨ node.tag = 2 then decide (node.slot < observationCount)
     else if node.tag = 3 then decide (node.slot < value.intents.length) else true)) &&
  value.intents.all (fun intent => decimalBound intent.artifact.value &&
    decimalBound intent.program.value && decimalBound intent.«instance» &&
    decimalBound intent.expectedRoot.value && !intent.exportName.isEmpty &&
    decide (intent.exportName.toUTF8.size ≤ 16384 ∧ intent.arguments.length ≤ 8192))

/- ABI text is generated below from the actual sealed source emission. -/
def requiredDeclarations : String := "Nat.arms : ∀x0 : <Zero, Succ> -> *2 =\n  λ{.Zero: <()>; λ{.Succ: Σx0 : Nat -> <()>; λ{}}}\n\nNat : *2 =\n  Σx0 : <Zero, Succ> -> (Nat.arms x0)\n\nList.q2.arms : ∀-x0 : *2 -> ∀x1 : <Nil, Con> -> *2 =\n  λ-x0 => λ{.Nil: <()>; λ{.Con: Σx1 : x0 -> Σx2 : (List.q2 -x0) -> <()>; λ{}}}\n\nList.q2 : ∀-x0 : *2 -> *2 =\n  λ-x0 => Σx1 : <Nil, Con> -> (List.q2.arms -x0 x1)\n\nWorldSurface.Intent.arms : ∀x0 : <WorldSurface.Intent> -> *2 =\n  λ{.WorldSurface.Intent: Σx0 : (List.q2 -Nat) -> Σx1 : (List.q2 -Nat) -> Σx2 : (List.q2 -Nat) -> Σx3 : Nat -> Σx4 : (List.q2 -Nat) -> Σx5 : (List.q2 -Nat) -> <()>; λ{}}\n\nWorldSurface.Intent : *2 =\n  Σx0 : <WorldSurface.Intent> -> (WorldSurface.Intent.arms x0)\n\nWorldSurface.Node.arms : ∀x0 : <WorldSurface.Node> -> *2 =\n  λ{.WorldSurface.Node: Σx0 : Nat -> Σx1 : Nat -> Σx2 : (List.q2 -Nat) -> Σx3 : (List.q2 -Nat) -> <()>; λ{}}\n\nWorldSurface.Node : *2 =\n  Σx0 : <WorldSurface.Node> -> (WorldSurface.Node.arms x0)\n\nWorldSurface.Surface.arms : ∀x0 : <WorldSurface.Surface> -> *2 =\n  λ{.WorldSurface.Surface: Σx0 : (List.q2 -Nat) -> Σx1 : (List.q2 -Nat) -> Σx2 : (List.q2 -WorldSurface.Node) -> Σx3 : Nat -> Σx4 : (List.q2 -WorldSurface.Intent) -> <()>; λ{}}\n\nWorldSurface.Surface : *2 =\n  Σx0 : <WorldSurface.Surface> -> (WorldSurface.Surface.arms x0)\n"

def abiMatches (core : BendCoreAdmission.Checked) : Bool :=
  match Book.parse requiredDeclarations with
  | .error _ => false
  | .ok definitions => definitions.all (fun definition =>
      decide (Book.get core.book definition.k = some definition))

theorem abi_definition_exact {core : BendCoreAdmission.Checked} {definitions : Book}
    (parsed : Book.parse requiredDeclarations = .ok definitions)
    (accepted : abiMatches core = true) {definition : Def} (member : definition ∈ definitions) :
    Book.get core.book definition.k = some definition := by
  simp only [abiMatches, parsed] at accepted
  exact of_decide_eq_true ((List.all_eq_true.mp accepted) definition member)

/-- Expected origin is an independent receiving input, never taken from an
output label. This is only an output witness: it creates neither observations
nor prepared action authority. -/
structure Evaluated (core : BendCoreAdmission.Checked) (initial : BTerm)
    (artifact : Digest) (exportName : String) (observationCount : Nat) where
  result : BTerm
  count : Nat
  trace : BendLiveMachine.Trace core.book count initial result
  value : Value core.book result
  surface : Surface
  decoded : lower result = some surface
  abi : abiMatches core = true
  origin : BendWorldSurface.originMatches surface artifact exportName = true
  bounds : bounded surface observationCount = true

def execute (core : BendCoreAdmission.Checked) (classificationTicks steps : Nat)
    (initial : BTerm) (artifact : Digest) (exportName : String)
    (observationCount : Nat) : Option (Evaluated core initial artifact exportName observationCount) :=
  if abi : abiMatches core = true then
    match BendLiveMachine.executeChecked core.book classificationTicks steps initial with
    | .refused _ _ _ _ => none
    | .complete result count trace value =>
        match decoded : lower result with
        | none => none
        | some surface =>
            if origin : BendWorldSurface.originMatches surface artifact exportName = true then
              if bounds : bounded surface observationCount = true then
                some ⟨result, count, trace, value, surface, decoded, abi, origin, bounds⟩
              else none
            else none
  else none

theorem evaluated_source_exact {core : BendCoreAdmission.Checked} {initial : BTerm}
    {artifact : Digest} {exportName : String} {observationCount : Nat}
    (output : Evaluated core initial artifact exportName observationCount) :
    sourceTerm output.surface = output.result := lower_exact output.decoded

theorem evaluated_origin_exact {core : BendCoreAdmission.Checked} {initial : BTerm}
    {artifact : Digest} {exportName : String} {observationCount : Nat}
    (output : Evaluated core initial artifact exportName observationCount) :
    output.surface.artifact = artifact ∧ output.surface.exportName = exportName :=
  BendWorldSurface.origin_exact output.origin

end Minidregg.Compiler.BendSurfaceLowering
