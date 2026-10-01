/-
# How the stdio session answers a request that ended in an exception

`serveSession` answers every frame. A handler that throws instead of returning
its own answer is answered here, and the loop keeps serving:

* a request whose client bytes its operation's grammar refuses is thrown as
  `malformed detail` and answered `refused malformed` (phase `op N`). The detail
  is the decoder's position or field name — a fact about bytes the client sent,
  so it is within the pre-signature disclosure rule (a challenge publishes
  nothing the client does not already hold about its own frame);
* any other exception is answered `refused operationRejected` (phase `op N`)
  with its text, as the fn session dispatcher already answers its own failures.

Two cases are not answered here and still end the process, because the Host's
own state, not the request, decided them (`Main.serveSession`): a poisoned
session (a Store read, chain, tag or replay failure; a new process must reopen
from the MAC'd checkpoint) and a handler that throws after its reply frame has
already been written (a second frame would desynchronise the pipe).
`mini serve` restarts the Host in both cases.
-/
import Compiler.NativeHostCodec
import Theory.AssertAxioms

namespace Minidregg.Host.RequestRefusal

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec

/-- The `IO.Error` filename slot that marks a malformed request. OS errors carry
a real path or `none` there; only `malformed` constructs this one. -/
def tag : String := "minidregg-host request"

/-- Thrown by a decoder when a request's client bytes fail its grammar. -/
def malformed (detail : String) : IO.Error :=
  .invalidArgument (some tag) 0 detail

/-- Lift a decoder's verdict on client bytes into the session monad. -/
def clientBytes {ε α : Type} [ToString ε] (decoded : Except ε α) : IO α :=
  match decoded with
  | .ok value => pure value
  | .error detail => throw (malformed (toString detail))

/-- A refusal detail is at most this many characters, so the answer frame stays
far inside the Host frame bound whatever the exception text quotes. -/
def maxDetailChars : Nat := 1024

def phase (operation : UInt8) : List UInt8 := s!"op {operation}".toUTF8.toList

def clip (text : String) : List UInt8 := (String.ofList (text.toList.take maxDetailChars)).toUTF8.toList

/-- The answer to a request whose handler threw `error`. -/
def answer (operation : UInt8) (error : IO.Error) : Outcome :=
  match error with
  | .invalidArgument (some marker) _ detail =>
      if marker = tag then .refused .malformed (phase operation) (clip detail)
      else .refused .operationRejected (phase operation) (clip (toString error))
  | other => .refused .operationRejected (phase operation) (clip (toString other))

/-- The frame payload `serveSession` writes under response operation 255. -/
def frame (operation : UInt8) (error : IO.Error) : List UInt8 :=
  outcomeCodec.encode (answer operation error)

/-- A malformed request is answered `refused malformed`, phase `op N`, with the
decoder's own detail. -/
theorem answer_malformed (operation : UInt8) (detail : String) :
    answer operation (malformed detail) =
      .refused .malformed (phase operation) (clip detail) := by
  simp [answer, malformed]

/-- Every exception is answered by a refusal for that operation: never a
confirmation, never contention, unavailable or uncertain. -/
theorem answer_refused (operation : UInt8) (error : IO.Error) :
    ∃ reason detail, answer operation error = .refused reason (phase operation) detail := by
  unfold answer
  split
  · split
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-- The written frame decodes, under the current outcome version, to exactly
that refusal: the client reads the reason the Host chose. -/
theorem frame_decodes (operation : UInt8) (error : IO.Error) :
    outcomeCodec.decode (frame operation error) = some (answer operation error) :=
  outcomeCodec.decode_encode _

#assert_axioms answer_malformed
#assert_axioms answer_refused
#assert_axioms frame_decodes

end Minidregg.Host.RequestRefusal
