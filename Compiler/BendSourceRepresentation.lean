import Compiler.BendLogicSpecialization

namespace Minidregg.Compiler.BendSourceRepresentation
set_option autoImplicit false
open Minidregg.Theory.BendTT
open BendLogicCase
deriving instance DecidableEq for Minidregg.Theory.BendTT.Def
abbrev BTerm := Minidregg.Theory.BendTT.Term
abbrev Normalizes := BendLogicSpecialization.Normalizes

/-- Exact safe.ts constructor lowering of Base.False{} / Base.True{}. -/
def boolTerm (b : Bool) : BTerm := .Tup .Q1 (.Lab (if b then "True" else "False")) (.Lab "()")
def RepBool (t : BTerm) (b : Bool) : Prop := t = boolTerm b

theorem repBool_unique {t : BTerm} {a b : Bool} (ha : RepBool t a) (hb : RepBool t b) : a = b := by
  cases a <;> cases b <;> simp_all [RepBool, boolTerm]
theorem boolTerm_data (b : Bool) : Data (boolTerm b) := .tup (fun _ => .lab) .lab
theorem boolTerm_value (bk : Book) (b : Bool) : Value bk (boolTerm b) := .tup (fun _ => .lab) .lab

def unitArm (t : BTerm) : BTerm := .Mat "()" t .Efq
/-- Captured safe_emit layout, including the live pair split and unit match. -/
def sourceTerm (p : Plan) : BTerm := .Prj (.Mat "False" (unitArm (boolTerm p.onFalse))
  (.Mat "True" (unitArm (boolTerm p.onTrue)) .Efq))

def armsDef : Def := ⟨"Bool.arms", .All .Q1 (.Enu ["False", "True"]) (.Typ .Q2),
  .Mat "False" (.Enu ["()"]) (.Mat "True" (.Enu ["()"]) .Efq), false⟩
def boolDef : Def := ⟨"Bool", .Typ .Q2,
  .Sig .Q1 (.Enu ["False", "True"]) (.App .Q1 (.Ref "Bool.arms") (.Var 0)), false⟩
def methodDef (p : Plan) : Def := ⟨"SourceBool.not", .All .Q1 (.Ref "Bool") (.Ref "Bool"), sourceTerm p, false⟩
/-- Full Book identity is an explicit admission premise, not name-based dispatch.
For the captured source below only negation is an authored method. -/
def emittedNegationBook : Book := [methodDef BendLogicSpecialization.negation, armsDef, boolDef]

theorem source_normalizes (bk : Book) (p : Plan) (b : Bool) :
    Normalizes bk (.App .Q1 (sourceTerm p) (boolTerm b)) (boolTerm (p.output b)) := by
  have splitStep := Eval.split (bk := bk) (h := match sourceTerm p with | .Prj h => h | _ => .Efq)
    (q := .Q1) (r := .Q1) (a := .Lab (if b then "True" else "False")) (b := .Lab "()") rfl (boolTerm_value bk b)
  cases b with
  | false =>
    exact (Relation.ReflTransGen.single splitStep).trans
      ((Relation.ReflTransGen.single (Eval.app_f (Eval.hit rfl))).trans
        (Relation.ReflTransGen.single (Eval.hit rfl)))
  | true =>
    exact (Relation.ReflTransGen.single splitStep).trans
      ((Relation.ReflTransGen.single (Eval.app_f (Eval.miss rfl (by decide)))).trans
        ((Relation.ReflTransGen.single (Eval.app_f (Eval.hit rfl))).trans
          (Relation.ReflTransGen.single (Eval.hit rfl))))

/-- Arbitrary descriptor witnesses force the represented source output. This
retains original wire pinning and does not trust an honest witness generator. -/
theorem descriptor_source_sound {F : Type} [Field F] (bk : Book) (nPublic : Nat)
    (p : Plan) (input output : Bool) (wv : Nat → F)
    (pinned : ∀ i : Fin 2, wv i.val = assignment input output i)
    (holds : descriptorHolds (descriptor nPublic p) wv) :
    Normalizes bk (.App .Q1 (sourceTerm p) (boolTerm input)) (boolTerm output) := by
  have correct := (descriptor_correct nPublic p input output).mp ⟨wv, pinned, holds⟩
  rw [correct]
  exact source_normalizes bk p input

/-- Source Nat tree is a mathematical witness. Consumers carry this relation
in Prop; no native codec is required to materialize a unary tree. -/
def natTerm : Nat → BTerm
  | 0 => .Tup .Q1 (.Lab "Zero") (.Lab "()")
  | n + 1 => .Tup .Q1 (.Lab "Succ") (.Tup .Q1 (natTerm n) (.Lab "()"))
def decodeNat : BTerm → Option Nat
  | .Tup .Q1 (.Lab "Zero") (.Lab "()") => some 0
  | .Tup .Q1 (.Lab "Succ") (.Tup .Q1 pred (.Lab "()")) => (decodeNat pred).map Nat.succ
  | _ => none

theorem decode_natTerm (n : Nat) : decodeNat (natTerm n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [natTerm, decodeNat, ih]

theorem natTerm_injective : Function.Injective natTerm := by
  intro a b h
  have := congrArg decodeNat h
  simpa [decode_natTerm] using this

def RepNat (t : BTerm) (n : Nat) : Prop := t = natTerm n
def RepBoundedNat (cap : Nat) (t : BTerm) (n : Nat) : Prop := RepNat t n ∧ n < cap

theorem natTerm_data (n : Nat) : Data (natTerm n) := by
  induction n with
  | zero => exact .tup (fun _ => .lab) .lab
  | succ n ih => exact .tup (fun _ => .lab) (.tup (fun _ => ih) .lab)

def natListTerm : List Nat → BTerm
  | [] => .Tup .Q1 (.Lab "Nil") (.Lab "()")
  | n :: ns => .Tup .Q1 (.Lab "Con")
      (.Tup .Q1 (natTerm n) (.Tup .Q1 (natListTerm ns) (.Lab "()")))
def decodeNatList : BTerm → Option (List Nat)
  | .Tup .Q1 (.Lab "Nil") (.Lab "()") => some []
  | .Tup .Q1 (.Lab "Con") (.Tup .Q1 head (.Tup .Q1 tail (.Lab "()"))) =>
      do let n ← decodeNat head; let ns ← decodeNatList tail; pure (n :: ns)
  | _ => none

theorem decode_natListTerm (ns : List Nat) : decodeNatList (natListTerm ns) = some ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [natListTerm, decodeNatList, decode_natTerm, ih]

/-- Source byte lists reject a non-byte member; no field cast or truncation. -/
def RepBytes (t : BTerm) (ns : List Nat) : Prop :=
  t = natListTerm ns ∧ ∀ n ∈ ns, n < 256

theorem represented_bytes_decode {t : BTerm} {ns : List Nat} (h : RepBytes t ns) :
    decodeNatList t = some ns ∧ ∀ n ∈ ns, n < 256 := by
  exact ⟨h.1 ▸ decode_natListTerm ns, h.2⟩

def decodeBool : BTerm → Option Bool
  | .Tup .Q1 (.Lab "False") (.Lab "()") => some false
  | .Tup .Q1 (.Lab "True") (.Lab "()") => some true
  | _ => none

theorem decode_boolTerm (b : Bool) : decodeBool (boolTerm b) = some b := by
  cases b <;> rfl

/-- Exact WCon constructor layout; head is the least significant bit in
upstream word_to_term/u32_from_term, not a big-endian reinterpretation. -/
def wordTerm : List Bool → BTerm
  | [] => .Tup .Q1 (.Lab "WNil") (.Lab "()")
  | b :: bs => .Tup .Q1 (.Lab "WCon")
      (.Tup .Q1 (boolTerm b) (.Tup .Q1 (wordTerm bs) (.Lab "()")))
def decodeWord : BTerm → Option (List Bool)
  | .Tup .Q1 (.Lab "WNil") (.Lab "()") => some []
  | .Tup .Q1 (.Lab "WCon") (.Tup .Q1 head (.Tup .Q1 tail (.Lab "()"))) =>
      do let b ← decodeBool head; let bs ← decodeWord tail; pure (b :: bs)
  | _ => none

theorem decode_wordTerm (bs : List Bool) : decodeWord (wordTerm bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [wordTerm, decodeWord, decode_boolTerm, ih]

def wordValue : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * wordValue bs

def RepWord (width : Nat) (t : BTerm) (bits : List Bool) : Prop :=
  t = wordTerm bits ∧ bits.length = width

theorem wordTerm_data (bs : List Bool) : Data (wordTerm bs) := by
  induction bs with
  | nil => exact .tup (fun _ => .lab) .lab
  | cons b bs ih =>
    exact .tup (fun _ => .lab)
      (.tup (fun _ => boolTerm_data b) (.tup (fun _ => ih) .lab))

theorem wordValue_bound (bs : List Bool) : wordValue bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [wordValue]
  | cons b bs ih =>
    cases b <;> simp [wordValue, List.length_cons, pow_succ] <;> omega

#assert_axioms decode_boolTerm
#assert_axioms decode_wordTerm
#assert_axioms wordTerm_data
#assert_axioms wordValue_bound

#assert_axioms decode_natTerm
#assert_axioms natTerm_injective
#assert_axioms natTerm_data
#assert_axioms decode_natListTerm
#assert_axioms represented_bytes_decode

#assert_axioms repBool_unique
#assert_axioms boolTerm_data
#assert_axioms boolTerm_value
#assert_axioms source_normalizes
#assert_axioms descriptor_source_sound
end Minidregg.Compiler.BendSourceRepresentation
