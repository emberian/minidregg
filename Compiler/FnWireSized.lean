/-
# Compiler.FnWireSized — teeth of the `sized` grammar node

`["sized", W, LO, HI, G]` (fn `planning/design/wire-grammar-2026-10-04.md` §2, fn `c50eda3ab`):
a W-octet big-endian length L with LO ≤ L ≤ HI, then exactly L octets that G decodes and
consumes entirely. A length outside LO..HI, fewer octets than L, or leftover octets inside the L
are each `malformed`; an inner refusal is the answer. The interpreter is
`Compiler.FnWireGrammar` (decode, encode, `wf`); the two round trips over it
(`FnWireRoundTrip.decode_encode`, `encode_decode`, and `decodeAll_*`) cover this arm like every
other. Here: one accept and every malformed case, as named theorems (`decide`, kernel-checked).

`pollReplyGrammar` is fn's `fnct.consumer.poll-reply`; the bytes bound 4294966940 is the largest
Store event the poll reply carries (fn `docs/operator-internals.md`: the Store frame's u32 less
the reply's 9 header and 346 cursor octets).
-/
import Compiler.FnWireFncu

namespace Minidregg.Compiler.FnWire

set_option autoImplicit false

/-- A two-octet number behind a one-octet length that must be exactly 2. -/
def sizedU16 : Grammar := .sized 1 2 2 (.uint 2 0 65535)

theorem sizedU16_wf : sizedU16.wf = true := by decide

/-- A 1-octet length of 1..4 around a u16: the length bounds are not the inner width. -/
def sizedU16Loose : Grammar := .sized 1 1 4 (.uint 2 0 65535)

theorem sizedU16Loose_wf : sizedU16Loose.wf = true := by decide

def isMalformed : Except Refusal (Value × List UInt8) → Bool
  | .error .malformed => true
  | _ => false

def natRest : Except Refusal (Value × List UInt8) → Option (Nat × List UInt8)
  | .ok (.nat n, r) => some (n, r)
  | _ => none

/-- Accept: the length 2, then 0x1234; what follows is the rest. -/
theorem sized_accepts :
    natRest (decode sizedU16 [2, 0x12, 0x34, 9]) = some (0x1234, [9]) := by decide

/-- Fewer octets than the length says. -/
theorem sized_refuses_too_short : isMalformed (decode sizedU16 [2, 0x12]) = true := by decide

/-- The inner grammar overruns the L octets (it needs 2, L = 1) although more octets follow. -/
theorem sized_refuses_overrun :
    isMalformed (decode sizedU16Loose [1, 0x12, 0x34]) = true := by decide

/-- The inner grammar leaves an octet of the L over. -/
theorem sized_refuses_leftover :
    isMalformed (decode sizedU16Loose [3, 0x12, 0x34, 0x56]) = true := by decide

/-- A length above HI, and one below LO, even with the octets present. -/
theorem sized_refuses_length_out_of_bounds :
    isMalformed (decode sizedU16 [3, 0x12, 0x34, 0x56]) = true ∧
      isMalformed (decode sizedU16Loose [0]) = true := by decide

/-- No length octet at all. -/
theorem sized_refuses_empty : isMalformed (decode sizedU16 []) = true := by decide

/-- It is the encoder's too: a value whose encoding is outside LO..HI is refused. -/
theorem sized_encode_refuses_out_of_bounds :
    (match encode (.sized 1 3 3 (.uint 2 0 65535)) (.nat 7) with
      | .error .malformed => true
      | _ => false) = true := by decide

/-- fn's `fnct.consumer.poll-reply` (FNCT kind 6): `accepted` carries the cursor behind its
4-octet length (a `sized` region, 31..346 octets) and the record behind its 4-octet length;
`refused`, `uncertain` and `fault` carry eight zero octets. `Compiler.FnWirePinned` proves it
is the pinned file's family of that name. -/
def pollReplyGrammar : Grammar :=
  .frame [0x46, 0x4e, 0x43, 0x54] 1 6 4294967295 <|
    .tagArm 1 0 "accepted"
      (.seqCons (.sized 4 31 346 cursorGrammar) <|
        .seqCons (.bytes 4 0 4294966940 .any) .seqNil) <|
    .tagArm 1 1 "refused" (.const (List.replicate 8 0)) <|
    .tagArm 1 2 "uncertain" (.const (List.replicate 8 0)) <|
    .tagArm 1 3 "fault" (.const (List.replicate 8 0)) (.tagNil 1)

theorem pollReplyGrammar_wf : pollReplyGrammar.wf = true := by decide

#assert_axioms sizedU16_wf sizedU16Loose_wf sized_accepts sized_refuses_too_short
  sized_refuses_overrun sized_refuses_leftover sized_refuses_length_out_of_bounds
  sized_refuses_empty sized_encode_refuses_out_of_bounds pollReplyGrammar_wf

end Minidregg.Compiler.FnWire
