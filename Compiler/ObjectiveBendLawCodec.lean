/- The bytes of a package's laws, as the source artifact commits them.

A law travels as a postfix token stream (the way `PolicyRecordCodec` carries a `Pred`): each
node is one token after its children, and decoding runs the tokens on a stack. The codec is
lawful (`lawStream`, `lawsStream`): a law's bytes are a function of the law, and the artifact
identity that hashes them commits exactly the laws. -/
module

public import Compiler.ObjectiveBendLaw
public import Compiler.PolicyRecordCodec
public import Compiler.IntStream

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Compiler.ObjectiveBendLawCodec
open Minidregg.Compiler.ObjectiveBendLaw
open Minidregg.Compiler.Tower256ConcreteBackend
set_option autoImplicit false

/-- A reference: a field by name, or one of four context words by index. The
index table has a default arm, so only the indices `0`–`3` are accepted
(`retract`); every larger index is refused rather than read as `turn`. -/
def refStream : StreamCodec LawRef :=
  StreamCodec.retract (StreamCodec.sum PolicyRecordCodec.stringStream StreamCodec.nat)
    (fun ref => match ref with
      | .field name => .inl name
      | .subject => .inr 0
      | .caller => .inr 1
      | .height => .inr 2
      | .turn => .inr 3)
    (fun wire => match wire with
      | .inl name => .field name
      | .inr 0 => .subject
      | .inr 1 => .caller
      | .inr 2 => .height
      | .inr _ => .turn)
    (by intro ref; cases ref <;> rfl)

inductive Token where
  | eqC (ref : LawRef) (value : Int)
  | leC (ref : LawRef) (value : Int)
  | inC (ref : LawRef) (values : List Int)
  | eqR (left right : LawRef)
  | leR (left right : LawRef)
  | leROff (left right : LawRef) (offset : Int)
  | monotone (field : String)
  | writeOnce (field : String)
  | sumEq (left right : List String)
  | hashEq (values : List String) (blinder commit : String)
  | not
  | and
  | or
  | implies
  deriving DecidableEq, Repr

def encodeToken : Token → List UInt8
  | .eqC ref value => 0 :: (refStream.encode ref ++ IntStream.intStream.encode value)
  | .leC ref value => 1 :: (refStream.encode ref ++ IntStream.intStream.encode value)
  | .inC ref values => 2 :: (refStream.encode ref ++ (StreamCodec.list IntStream.intStream).encode values)
  | .eqR left right => 3 :: (refStream.encode left ++ refStream.encode right)
  | .leR left right => 4 :: (refStream.encode left ++ refStream.encode right)
  | .leROff left right offset =>
      5 :: (refStream.encode left ++ (refStream.encode right ++ IntStream.intStream.encode offset))
  | .monotone field => 6 :: PolicyRecordCodec.stringStream.encode field
  | .writeOnce field => 7 :: PolicyRecordCodec.stringStream.encode field
  | .not => [8]
  | .and => [9]
  | .or => [10]
  | .implies => [11]
  | .sumEq left right =>
      12 :: ((StreamCodec.list PolicyRecordCodec.stringStream).encode left ++
        (StreamCodec.list PolicyRecordCodec.stringStream).encode right)
  | .hashEq values blinder commit =>
      13 :: ((StreamCodec.list PolicyRecordCodec.stringStream).encode values ++
        (PolicyRecordCodec.stringStream.encode blinder ++ PolicyRecordCodec.stringStream.encode commit))

def decodeToken : List UInt8 → Option (Token × List UInt8)
  | 0 :: bytes => do
      let (ref, rest) ← refStream.decodePrefix bytes
      let (value, rest) ← IntStream.intStream.decodePrefix rest
      some (.eqC ref value, rest)
  | 1 :: bytes => do
      let (ref, rest) ← refStream.decodePrefix bytes
      let (value, rest) ← IntStream.intStream.decodePrefix rest
      some (.leC ref value, rest)
  | 2 :: bytes => do
      let (ref, rest) ← refStream.decodePrefix bytes
      let (values, rest) ← (StreamCodec.list IntStream.intStream).decodePrefix rest
      some (.inC ref values, rest)
  | 3 :: bytes => do
      let (left, rest) ← refStream.decodePrefix bytes
      let (right, rest) ← refStream.decodePrefix rest
      some (.eqR left right, rest)
  | 4 :: bytes => do
      let (left, rest) ← refStream.decodePrefix bytes
      let (right, rest) ← refStream.decodePrefix rest
      some (.leR left right, rest)
  | 5 :: bytes => do
      let (left, rest) ← refStream.decodePrefix bytes
      let (right, rest) ← refStream.decodePrefix rest
      let (offset, rest) ← IntStream.intStream.decodePrefix rest
      some (.leROff left right offset, rest)
  | 6 :: bytes => do
      let (field, rest) ← PolicyRecordCodec.stringStream.decodePrefix bytes
      some (.monotone field, rest)
  | 7 :: bytes => do
      let (field, rest) ← PolicyRecordCodec.stringStream.decodePrefix bytes
      some (.writeOnce field, rest)
  | 8 :: rest => some (.not, rest)
  | 9 :: rest => some (.and, rest)
  | 10 :: rest => some (.or, rest)
  | 11 :: rest => some (.implies, rest)
  | 12 :: bytes => do
      let (left, rest) ← (StreamCodec.list PolicyRecordCodec.stringStream).decodePrefix bytes
      let (right, rest) ← (StreamCodec.list PolicyRecordCodec.stringStream).decodePrefix rest
      some (.sumEq left right, rest)
  | 13 :: bytes => do
      let (values, rest) ← (StreamCodec.list PolicyRecordCodec.stringStream).decodePrefix bytes
      let (blinder, rest) ← PolicyRecordCodec.stringStream.decodePrefix rest
      let (commit, rest) ← PolicyRecordCodec.stringStream.decodePrefix rest
      some (.hashEq values blinder commit, rest)
  | _ => none

theorem decodeToken_encode (token : Token) (suffix : List UInt8) :
    decodeToken (encodeToken token ++ suffix) = some (token, suffix) := by
  cases token <;> simp [encodeToken, decodeToken, StreamCodec.decodePrefix_encode]

set_option hygiene false in
/-- One arm of `decodeToken`: each payload decode read back as the encoding it
consumed. -/
local macro "token_arm" : tactic => `(tactic| (
  simp only [decodeToken, Option.bind_eq_bind] at decoded
  repeat' (
    rw [Option.bind_eq_some_iff] at decoded
    obtain ⟨⟨_, _⟩, ok, decoded⟩ := decoded
    have okBytes := StreamCodec.encode_decodePrefix _ _ _ _ ok
    subst okBytes
    try dsimp only at decoded)
  simp only [Option.some.injEq, Prod.mk.injEq] at decoded
  obtain ⟨rfl, rfl⟩ := decoded
  simp [encodeToken, List.append_assoc]))

theorem encodeToken_decodeToken (bytes : List UInt8) (value : Token) (suffix : List UInt8)
    (decoded : decodeToken bytes = some (value, suffix)) : encodeToken value ++ suffix = bytes := by
  rcases bytes with _ | ⟨tag, bytes⟩
  · cases decoded
  by_cases t0 : tag = 0
  · subst t0; token_arm
  by_cases t1 : tag = 1
  · subst t1; token_arm
  by_cases t2 : tag = 2
  · subst t2; token_arm
  by_cases t3 : tag = 3
  · subst t3; token_arm
  by_cases t4 : tag = 4
  · subst t4; token_arm
  by_cases t5 : tag = 5
  · subst t5; token_arm
  by_cases t6 : tag = 6
  · subst t6; token_arm
  by_cases t7 : tag = 7
  · subst t7; token_arm
  by_cases t8 : tag = 8
  · subst t8; token_arm
  by_cases t9 : tag = 9
  · subst t9; token_arm
  by_cases t10 : tag = 10
  · subst t10; token_arm
  by_cases t11 : tag = 11
  · subst t11; token_arm
  by_cases t12 : tag = 12
  · subst t12; token_arm
  by_cases t13 : tag = 13
  · subst t13; token_arm
  simp [decodeToken, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13] at decoded

def tokenStream : StreamCodec Token where
  encode := encodeToken
  decodePrefix := decodeToken
  decodePrefix_encode := decodeToken_encode
  encode_decodePrefix := encodeToken_decodeToken

def step : Token → List LawExpr → Option (List LawExpr)
  | .eqC ref value, stack => some (.eqC ref value :: stack)
  | .leC ref value, stack => some (.leC ref value :: stack)
  | .inC ref values, stack => some (.inC ref values :: stack)
  | .eqR left right, stack => some (.eqR left right :: stack)
  | .leR left right, stack => some (.leR left right :: stack)
  | .leROff left right offset, stack => some (.leROff left right offset :: stack)
  | .monotone field, stack => some (.monotone field :: stack)
  | .writeOnce field, stack => some (.writeOnce field :: stack)
  | .sumEq left right, stack => some (.sumEq left right :: stack)
  | .hashEq values blinder commit, stack => some (.hashEq values blinder commit :: stack)
  | .not, body :: stack => some (.not body :: stack)
  | .and, right :: left :: stack => some (.and left right :: stack)
  | .or, right :: left :: stack => some (.or left right :: stack)
  | .implies, conclusion :: premise :: stack => some (.implies premise conclusion :: stack)
  | _, _ => none

def runTokens : List Token → List LawExpr → Option (List LawExpr)
  | [], stack => some stack
  | token :: tokens, stack => do
      let next ← step token stack
      runTokens tokens next

/-- Postfix order, as a difference list. -/
def tokensInto : LawExpr → List Token → List Token
  | .eqC ref value, suffix => .eqC ref value :: suffix
  | .leC ref value, suffix => .leC ref value :: suffix
  | .inC ref values, suffix => .inC ref values :: suffix
  | .eqR left right, suffix => .eqR left right :: suffix
  | .leR left right, suffix => .leR left right :: suffix
  | .leROff left right offset, suffix => .leROff left right offset :: suffix
  | .monotone field, suffix => .monotone field :: suffix
  | .writeOnce field, suffix => .writeOnce field :: suffix
  | .sumEq left right, suffix => .sumEq left right :: suffix
  | .hashEq values blinder commit, suffix => .hashEq values blinder commit :: suffix
  | .not body, suffix => tokensInto body (.not :: suffix)
  | .and left right, suffix => tokensInto left (tokensInto right (.and :: suffix))
  | .or left right, suffix => tokensInto left (tokensInto right (.or :: suffix))
  | .implies premise conclusion, suffix => tokensInto premise (tokensInto conclusion (.implies :: suffix))

theorem runTokens_tokensInto (law : LawExpr) :
    ∀ (suffix : List Token) (stack : List LawExpr),
      runTokens (tokensInto law suffix) stack = runTokens suffix (law :: stack) := by
  induction law with
  | eqC => intro suffix stack; rfl
  | leC => intro suffix stack; rfl
  | inC => intro suffix stack; rfl
  | eqR => intro suffix stack; rfl
  | leR => intro suffix stack; rfl
  | leROff => intro suffix stack; rfl
  | monotone => intro suffix stack; rfl
  | writeOnce => intro suffix stack; rfl
  | sumEq => intro suffix stack; rfl
  | hashEq => intro suffix stack; rfl
  | not body ih => intro suffix stack; rw [tokensInto, ih]; rfl
  | and left right ihLeft ihRight => intro suffix stack; rw [tokensInto, ihLeft, ihRight]; rfl
  | or left right ihLeft ihRight => intro suffix stack; rw [tokensInto, ihLeft, ihRight]; rfl
  | implies premise conclusion ihPremise ihConclusion =>
      intro suffix stack; rw [tokensInto, ihPremise, ihConclusion]; rfl

def encodeLaw (law : LawExpr) : List Token := tokensInto law []

def decodeLaw (tokens : List Token) : Option LawExpr := do
  let stack ← runTokens tokens []
  match stack with
  | [law] => some law
  | _ => none

@[simp] theorem decodeLaw_encode (law : LawExpr) : decodeLaw (encodeLaw law) = some law := by
  simp [decodeLaw, encodeLaw, runTokens_tokensInto, runTokens]

/-- A stack as the postfix tokens that build it from empty, deepest law first,
ahead of `rest`. -/
def stackInto : List LawExpr → List Token → List Token
  | [], rest => rest
  | law :: stack, rest => stackInto stack (tokensInto law rest)

/-- Every accepted step appends exactly its token to the stack's spelling. -/
theorem step_stackInto {token : Token} {stack next : List LawExpr}
    (stepped : step token stack = some next) (rest : List Token) :
    stackInto stack (token :: rest) = stackInto next rest := by
  unfold step at stepped
  split at stepped <;> first | (cases stepped; rfl) | cases stepped

theorem runTokens_stackInto (tokens : List Token) {stack next : List LawExpr}
    (ran : runTokens tokens stack = some next) (rest : List Token) :
    stackInto stack (tokens ++ rest) = stackInto next rest := by
  induction tokens generalizing stack with
  | nil =>
      simp only [runTokens, Option.some.injEq] at ran
      subst ran
      rfl
  | cons token tokens ih =>
      cases stepped : step token stack with
      | none => simp [runTokens, stepped] at ran
      | some middle =>
          simp only [runTokens, stepped, bind, Option.bind] at ran
          rw [List.cons_append, step_stackInto stepped, ih ran]

/-- Postfix decoding is canonical: a token list that decodes to a law is that
law's encoding. -/
theorem encodeLaw_decodeLaw {tokens : List Token} {law : LawExpr}
    (decoded : decodeLaw tokens = some law) : encodeLaw law = tokens := by
  unfold decodeLaw at decoded
  cases ran : runTokens tokens [] with
  | none => simp [ran] at decoded
  | some stack =>
      have built := runTokens_stackInto tokens ran []
      simp only [ran, bind, Option.bind] at decoded
      split at decoded
      · cases decoded
        simpa [stackInto, encodeLaw] using built.symm
      · cases decoded

def lawStream : StreamCodec LawExpr where
  encode law := (StreamCodec.list tokenStream).encode (encodeLaw law)
  decodePrefix bytes := do
    let (tokens, suffix) ← (StreamCodec.list tokenStream).decodePrefix bytes
    let law ← decodeLaw tokens
    pure (law, suffix)
  decodePrefix_encode := by
    intro law suffix
    simp [StreamCodec.decodePrefix_encode, decodeLaw_encode]
  encode_decodePrefix := by
    intro bytes law suffix decoded
    cases listed : (StreamCodec.list tokenStream).decodePrefix bytes with
    | none => simp [listed] at decoded
    | some pair =>
      obtain ⟨tokens, rest⟩ := pair
      cases inner : decodeLaw tokens with
      | none => simp [listed, inner] at decoded
      | some decodedLaw =>
        simp only [listed, inner, bind, Option.bind, pure, Option.some.injEq,
          Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        rw [encodeLaw_decodeLaw inner]
        exact StreamCodec.encode_decodePrefix _ _ _ _ listed

/-- A package's laws, in declaration order. -/
def lawsStream : StreamCodec (List (String × LawExpr)) :=
  StreamCodec.list (StreamCodec.product PolicyRecordCodec.stringStream lawStream)

theorem lawsStream_injective {a b : List (String × LawExpr)} (same : lawsStream.encode a = lawsStream.encode b) :
    a = b := by
  have decoded := congrArg (fun bytes => lawsStream.decodePrefix (bytes ++ [])) same
  simp only [lawsStream.decodePrefix_encode, Option.some.injEq, Prod.mk.injEq] at decoded
  exact decoded.1

#assert_axioms decodeToken_encode
#assert_axioms runTokens_tokensInto
#assert_axioms decodeLaw_encode
#assert_axioms encodeToken_decodeToken
#assert_axioms encodeLaw_decodeLaw
#assert_axioms lawsStream_injective
end Minidregg.Compiler.ObjectiveBendLawCodec
