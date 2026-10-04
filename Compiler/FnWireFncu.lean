/-
# Compiler.FnWireFncu — fn's `fncu` consumer cursor, read by the grammar interpreter

The cursor fn writes (`fn-cp-cursor-encode`, fn `books/consumer-position.lisp`) is the
family `fncu.cursor` of fn's exported grammar file. `cursorGrammar` is that family's grammar;
`Compiler.FnWirePinned.fncuCursor_is_pinned` proves it equal to the one the pinned file
carries, so it cannot drift from fn's export, and `cursorGrammar_wf` is kernel-checked, so
the interpreter's two round trips apply to it with no compiler trust.

`decodeCursor` replaces the `fn --fn consumer-inspect` subprocess and its text-line parser:
Mini reads the cursor octets itself. A cursor is accepted exactly when the octets are one
`fncu.cursor` message, and then it is canonical (`decodeCursor_canonical`).
-/
import Compiler.FnWireRoundTrip
import Kernel.FnConsumerScope

namespace Minidregg.Compiler.FnWire

set_option autoImplicit false

open Minidregg.Kernel

/-- `fncu.cursor`: "fncu" 1, five ids (history, incarnation, consumer, principal, query) of
1..64 octets behind a one-octet length, then query-version, view-version,
registration-epoch (≥ 1) and position as big-endian u32. -/
def cursorGrammar : Grammar :=
  .seqCons (.const [102, 110, 99, 117, 1]) <|
  .seqCons (.bytes 1 1 64 .any) <| .seqCons (.bytes 1 1 64 .any) <|
  .seqCons (.bytes 1 1 64 .any) <| .seqCons (.bytes 1 1 64 .any) <|
  .seqCons (.bytes 1 1 64 .any) <|
  .seqCons (.uint 4 0 4294967295) <| .seqCons (.uint 4 0 4294967295) <|
  .seqCons (.uint 4 1 4294967295) <| .seqCons (.uint 4 0 4294967295) .seqNil

theorem cursorGrammar_wf : cursorGrammar.wf = true := by decide

/-- The longest cursor: 5 + 5 × 65 + 4 × 4 octets (fn `fn-cp-cursor-encode-length-bound`). -/
def maxCursorOctets : Nat := 346

/-- A cursor as its grammar value. -/
def cursorValue (scope : FnConsumerScope.Scope) (position : Nat) : Value :=
  .list [.null, .octets scope.history, .octets scope.incarnation, .octets scope.consumer,
    .octets scope.principal, .octets scope.query, .nat scope.queryVersion,
    .nat scope.viewVersion, .nat scope.registrationEpoch, .nat position]

/-- A cursor value's scope and position. -/
def cursorOfValue : Value → Option (FnConsumerScope.Scope × Nat)
  | .list [.null, .octets h, .octets i, .octets c, .octets p, .octets q,
      .nat qv, .nat vv, .nat e, .nat pos] => some (⟨h, i, c, p, q, qv, vv, e⟩, pos)
  | _ => none

theorem cursorOfValue_eq {v : Value} {s : FnConsumerScope.Scope} {pos : Nat}
    (h : cursorOfValue v = some (s, pos)) : v = cursorValue s pos := by
  unfold cursorOfValue at h
  split at h
  · cases h; rfl
  · cases h

/-- The cursor in `xs`: one `fncu.cursor` message and nothing else, within the cursor
bound. Refusals are the interpreter's (`malformed`, `limit`). -/
def decodeCursor (xs : List UInt8) : Except Refusal (FnConsumerScope.Scope × Nat) :=
  match decodeWithin maxCursorOctets cursorGrammar xs with
  | .ok v => match cursorOfValue v with
    | some c => .ok c
    | none => .error .malformed
  | .error e => .error e

/-- An accepted cursor is the canonical encoding of its scope and position. -/
theorem decodeCursor_canonical {xs : List UInt8} {s : FnConsumerScope.Scope} {pos : Nat}
    (h : decodeCursor xs = .ok (s, pos)) : encode cursorGrammar (cursorValue s pos) = .ok xs := by
  unfold decodeCursor at h
  split at h
  · rename_i v hv
    split at h
    · rename_i c hc
      cases h
      rw [← cursorOfValue_eq hc]
      unfold decodeWithin at hv
      split at hv
      · exact encode_decodeAll cursorGrammar_wf hv
      · cases hv
    · cases h
  · cases h

/-- Every scope and position the grammar admits round-trips. -/
theorem decodeCursor_encode {s : FnConsumerScope.Scope} {pos : Nat} {b : List UInt8}
    (he : encode cursorGrammar (cursorValue s pos) = .ok b) (hb : b.length ≤ maxCursorOctets) :
    decodeCursor b = .ok (s, pos) := by
  unfold decodeCursor
  rw [decodeWithin_of_le hb, decodeAll_encode cursorGrammar_wf he]
  rfl

#assert_axioms cursorGrammar_wf cursorOfValue_eq decodeCursor_canonical decodeCursor_encode

end Minidregg.Compiler.FnWire
