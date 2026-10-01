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

`Ran` is one fueled evaluation in a single pass, the shape the kernel's referee
consumes (`Kernel.Run`): the value and the count, or the failure and the count at
which it stopped. EVAL §1.1's `Except Outcome (Output × Nat)` would drop the count
on a crash and on exhaustion, and the kernel's refusals report it (`crash k`,
`exhausted k`). `FieldWrite` is what a run's product names: the writes a command
must make for its claim to be admitted (K-RAN), whatever evaluator produced them.
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

/-- One fueled evaluation: the value and the steps it took, or the failure and the
steps at which it stopped. -/
inductive Ran (Output : Type) where
  | ok (out : Output) (steps : Nat)
  | crash (steps : Nat)
  | exhausted (steps : Nat)
  deriving DecidableEq, Repr

/-- The byte entry point's answer for this evaluation, the output serialized. -/
def Ran.toByteRun {Output : Type} (encode : Output → List UInt8) : Ran Output → ByteRun
  | .ok out k => .ok k (encode out)
  | .crash k => .crash k
  | .exhausted k => .exhausted k

/-- One object-field write: field `field` of the command's `target`-th target
(0-based, the signed target order) becomes `value`. -/
structure FieldWrite where
  target : Nat
  field : Nat
  value : Int
  deriving DecidableEq, Repr

end Eval
end Minidregg.Theory
