/- The bytes of a package's laws, as the source artifact commits them.

A law travels as a postfix token stream (the way `PolicyRecordCodec` carries a `Pred`): each
node is one token after its children, and decoding runs the tokens on a stack. The codec is
lawful (`lawStream`, `lawsStream`): a law's bytes are a function of the law, and the artifact
identity that hashes them commits exactly the laws. -/
import Compiler.ObjectiveBendLaw
import Compiler.PolicyRecordCodec
import Compiler.IntStream

namespace Minidregg.Compiler.ObjectiveBendLawCodec
open Minidregg.Compiler.ObjectiveBendLaw
open Minidregg.Compiler.Tower256ConcreteBackend
set_option autoImplicit false

def refStream : StreamCodec LawRef :=
  StreamCodec.xmap (StreamCodec.sum PolicyRecordCodec.stringStream StreamCodec.nat)
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
  | _ => none

theorem decodeToken_encode (token : Token) (suffix : List UInt8) :
    decodeToken (encodeToken token ++ suffix) = some (token, suffix) := by
  cases token <;> simp [encodeToken, decodeToken, StreamCodec.decodePrefix_encode]

def tokenStream : StreamCodec Token where
  encode := encodeToken
  decodePrefix := decodeToken
  decodePrefix_encode := decodeToken_encode

def step : Token → List LawExpr → Option (List LawExpr)
  | .eqC ref value, stack => some (.eqC ref value :: stack)
  | .leC ref value, stack => some (.leC ref value :: stack)
  | .inC ref values, stack => some (.inC ref values :: stack)
  | .eqR left right, stack => some (.eqR left right :: stack)
  | .leR left right, stack => some (.leR left right :: stack)
  | .leROff left right offset, stack => some (.leROff left right offset :: stack)
  | .monotone field, stack => some (.monotone field :: stack)
  | .writeOnce field, stack => some (.writeOnce field :: stack)
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

def lawStream : StreamCodec LawExpr where
  encode law := (StreamCodec.list tokenStream).encode (encodeLaw law)
  decodePrefix bytes := do
    let (tokens, suffix) ← (StreamCodec.list tokenStream).decodePrefix bytes
    let law ← decodeLaw tokens
    pure (law, suffix)
  decodePrefix_encode := by
    intro law suffix
    simp [StreamCodec.decodePrefix_encode, decodeLaw_encode]

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
#assert_axioms lawsStream_injective
end Minidregg.Compiler.ObjectiveBendLawCodec
