/-
# Theory.Eval — the run outcomes every evaluator shares

A fueled run of a user program ends with a value, a crash (a property of the
term), or exhaustion (a property of the fuel, which says nothing about the
term). `Outcome` is the two failures; `ByteRun` is the answer of an evaluator's
byte entry point, and `ByteRun.toBytes` its C ABI wire form
(`[status] ++ steps (8 bytes LE) ++ output`, status 0 ok · 1 crash ·
2 exhausted · 3 malformed). Both were `Theory.Nock`'s (`Nock.Outcome`,
`Nock.JamRun`, the body of `runJammedBytes`); nothing in them is Nock, and
`Compiler.Evaluator` states every evaluator against them.
-/

namespace Minidregg.Theory
namespace Eval

/-- How a fueled run fails. -/
inductive Outcome where
  | crash
  | exhausted
  deriving DecidableEq, Repr

/-- The byte entry point's answer on a serialized term. -/
inductive ByteRun where
  | ok (steps : Nat) (out : List UInt8)
  | crash (steps : Nat)
  | exhausted (steps : Nat)
  | malformed
  deriving DecidableEq, Repr

/-- Little-endian 8-byte step count. -/
def le8 (n : Nat) : List UInt8 := (List.range 8).map fun i => (n >>> (8 * i)).toUInt8

/-- The C ABI wire form: `[status] ++ steps (8 bytes LE) ++ output`, status
`0` ok · `1` crash · `2` exhausted · `3` malformed input. -/
def ByteRun.toBytes : ByteRun → List UInt8
  | .ok k bs => 0 :: le8 k ++ bs
  | .crash k => 1 :: le8 k
  | .exhausted k => 2 :: le8 k
  | .malformed => 3 :: le8 0

end Eval
end Minidregg.Theory
