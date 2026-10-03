/- Proof-producing reification of indexed Bend code and closure heaps.
This is a publication/proof/debug path, not the private runtime evaluator.
Successful results contain actual CodeDenotes/Denotes evidence.
-/
import Theory.BendClosureArena
namespace Minidregg.Theory.BendClosureArena
open BendTT
set_option autoImplicit false

structure DecodedCode (program : Program) (pointer : Nat) where
  term : Term
  exact : CodeDenotes program pointer term

def decodeCode (program : Program) : (ticks pointer : Nat) →
    Option (DecodedCode program pointer)
  | 0, _ => none
  | ticks + 1, pointer => do
    match found : program.code[pointer]? with
    | none => none
    | some instruction =>
      match instruction with
      | .var index => pure ⟨.Var index, .var found⟩
      | .ref index =>
        match name : program.names[index]? with
        | none => none
        | some value => pure ⟨.Ref value, .ref found name⟩
      | .ann value type => do
        let v ← decodeCode program ticks value
        let t ← decodeCode program ticks type
        pure ⟨.Ann v.term t.term, .ann found v.exact t.exact⟩
      | .lett q value body => do
        let v ← decodeCode program ticks value
        let f ← decodeCode program ticks body
        pure ⟨.Let q v.term f.term, .lett found v.exact f.exact⟩
      | .typ q => pure ⟨.Typ q, .typ found⟩
      | .all q domain body => do
        let a ← decodeCode program ticks domain
        let b ← decodeCode program ticks body
        pure ⟨.All q a.term b.term, .all found a.exact b.exact⟩
      | .lam q body => do
        let f ← decodeCode program ticks body
        pure ⟨.Lam q f.term, .lam found f.exact⟩
      | .app q function argument => do
        let f ← decodeCode program ticks function
        let x ← decodeCode program ticks argument
        pure ⟨.App q f.term x.term, .app found f.exact x.exact⟩
      | .sig q domain body => do
        let a ← decodeCode program ticks domain
        let b ← decodeCode program ticks body
        pure ⟨.Sig q a.term b.term, .sig found a.exact b.exact⟩
      | .tup q first second => do
        let a ← decodeCode program ticks first
        let b ← decodeCode program ticks second
        pure ⟨.Tup q a.term b.term, .tup found a.exact b.exact⟩
      | .prj handler => do
        let h ← decodeCode program ticks handler
        pure ⟨.Prj h.term, .prj found h.exact⟩
      | .enu index =>
        match names : program.enumerations[index]? with
        | none => none
        | some values => pure ⟨.Enu values, .enu found names⟩
      | .lab index =>
        match name : program.names[index]? with
        | none => none
        | some value => pure ⟨.Lab value, .lab found name⟩
      | .mat index yes no => do
        match name : program.names[index]? with
        | none => none
        | some value => do
          let h ← decodeCode program ticks yes
          let m ← decodeCode program ticks no
          pure ⟨.Mat value h.term m.term, .mat found name h.exact m.exact⟩
      | .efq => pure ⟨.Efq, .efq found⟩
      | .eql left right type => do
        let a ← decodeCode program ticks left
        let b ← decodeCode program ticks right
        let t ← decodeCode program ticks type
        pure ⟨.Eql a.term b.term t.term, .eql found a.exact b.exact t.exact⟩
      | .rfl => pure ⟨.Rfl, .rfl found⟩
      | .rwt evidence motive body => do
        let e ← decodeCode program ticks evidence
        let m ← decodeCode program ticks motive
        let f ← decodeCode program ticks body
        pure ⟨.Rwt e.term m.term f.term, .rwt found e.exact m.exact f.exact⟩

structure Decoded (program : Program) (heap : Heap) (pointer : Nat) where
  term : Term
  exact : Denotes program heap pointer term

structure DecodedEnvironment (program : Program) (heap : Heap) (pointer : Nat) where
  values : List Term
  exact : EnvironmentDenotes program heap pointer values

mutual
def decode (program : Program) (heap : Heap) : (ticks pointer : Nat) →
    Option (Decoded program heap pointer)
  | 0, _ => none
  | ticks + 1, pointer => do
    match found : heap.get? pointer with
    | some (.closure code environment) =>
      let source ← decodeCode program ticks code
      let captured ← decodeEnvironment program heap ticks environment
      pure ⟨Term.sub (Env.sub captured.values) source.term,
        .closure found source.exact captured.exact⟩
    | some (.pair q first second) =>
      let a ← decode program heap ticks first
      let b ← decode program heap ticks second
      pure ⟨.Tup q a.term b.term, .pair found a.exact b.exact⟩
    | some (.application q function argument) =>
      let f ← decode program heap ticks function
      let x ← decode program heap ticks argument
      pure ⟨.App q f.term x.term, .application found f.exact x.exact⟩
    | _ => none

def decodeEnvironment (program : Program) (heap : Heap) : (ticks pointer : Nat) →
    Option (DecodedEnvironment program heap pointer)
  | 0, _ => none
  | ticks + 1, pointer => do
    match found : heap.get? pointer with
    | some .nil => pure ⟨[], .nil found⟩
    | some (.environment value tail) =>
      let head ← decode program heap ticks value
      let tail ← decodeEnvironment program heap ticks tail
      pure ⟨head.term :: tail.values, .cons found head.exact tail.exact⟩
    | _ => none
end

#assert_axioms decodeCode
#assert_axioms decode
#assert_axioms decodeEnvironment
end Minidregg.Theory.BendClosureArena

