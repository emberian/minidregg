/-
# Compiler.FnWireConsumer — fn's consumer and store-identity reply frames, read by the interpreter

`fn consumer --frame status|position|ack` and `fn identity --frame CONTROL` print the reply
frame their one exchange read as lowercase hex and one newline, in place of the text line
(fn `3f0309256`); the exit class is the same. This module reads those frames with Mini's ONE
grammar interpreter (`Compiler.FnWireGrammar`), over the families of fn's exported file that
describe them:

* `fnct.consumer.reply` (FNCT kind 5): `accepted` (a `maybe` cursor), `refused`, `uncertain`,
  `fault` — the replies to `ack` and `position`;
* `fnct.consumer.status-reply` (kind 9): `accepted` with committed-ack, journal frontier and
  distance (a `where` pins `ack ≤ frontier` and `distance = frontier − ack`), or the three
  refusals — the reply to `status`;
* `fnct.reasoned-reply` (kind 18): a status word and a reason word — what a reasoned request
  (kind 22) may be answered with instead of kind 5/9, never an acceptance;
* `fnct.store-identity.reply` (kind 25): format word, genesis node, schema and profile digests,
  consumer state, creating and running revisions, and the digest of the wire-grammar file the
  running image renders (`grammarDigest`) — or `refused` by name.

The grammars are written here as Lean terms (so the Host can run them without parsing JSON)
and `Compiler.FnWirePinned` proves each is the pinned file's family of that name
(`*_is_pinned`), so none can drift from fn's export; their `wf` is kernel-checked, so the
interpreter's two round trips apply to them. A frame is accepted exactly when the octets are
one frame of the family and nothing else (`decodeAll` after the hex), within the family's bound.
-/
import Compiler.FnWireFncu
import Compiler.FnWireSized

namespace Minidregg.Compiler.FnWire

set_option autoImplicit false

open Minidregg.Kernel

/-! ## Hex lines -/

/-- One lowercase hex digit. -/
def lowerHexDigit? (b : UInt8) : Option Nat :=
  if 48 ≤ b.toNat ∧ b.toNat ≤ 57 then some (b.toNat - 48)
  else if 97 ≤ b.toNat ∧ b.toNat ≤ 102 then some (b.toNat - 87)
  else none

/-- Strict lowercase hex of an even number of digits; nothing else. -/
def lowerHexOctets? : List UInt8 → Option (List UInt8)
  | [] => some []
  | [_] => none
  | a :: b :: rest =>
      match lowerHexDigit? a, lowerHexDigit? b, lowerHexOctets? rest with
      | some x, some y, some tl => some (UInt8.ofNat (16 * x + y) :: tl)
      | _, _, _ => none
termination_by xs => xs.length

/-- The frame a `--frame` command printed: lowercase hex then exactly one newline. -/
def frameOfStdout (stdout : List UInt8) : Option (List UInt8) :=
  match stdout.reverse with
  | 10 :: rev => lowerHexOctets? rev.reverse
  | _ => none

/-! ## The families -/

/-- `FNCT`. -/
def fnctMagic : List UInt8 := [0x46, 0x4e, 0x43, 0x54]

/-- The four outcome arms of a consumer reply: `accepted` with `accepted`'s grammar, then
`refused`, `uncertain`, `fault` with no fields. -/
def outcomeTag (accepted : Grammar) : Grammar :=
  .tagArm 1 0 "accepted" accepted <|
  .tagArm 1 1 "refused" .seqNil <|
  .tagArm 1 2 "uncertain" .seqNil <|
  .tagArm 1 3 "fault" .seqNil (.tagNil 1)

def consumerReplyGrammar : Grammar :=
  .frame fnctMagic 1 5 513 (outcomeTag (.maybe cursorGrammar))

def statusReplyGrammar : Grammar :=
  .frame fnctMagic 1 9 13 <| outcomeTag <|
    .where_ (.seqCons (.uint 4 0 4294967295) <| .seqCons (.uint 4 0 4294967295) <|
      .seqCons (.uint 4 0 4294967295) .seqNil) [.le 0 1, .diff 2 1 0]

/-- The status words of a reasoned reply, from code 1. -/
def reasonedStatusNames : List String :=
  ["accepted", "duplicate", "refused", "clock-unusable", "busy", "uncertain", "fault",
   "article-exceeds-profile-bound", "conflict", "author-not-enrolled", "source-malformed",
   "unknown-group", "carrier-refused", "control-not-filed", "control-malformed",
   "signed-event-not-formed"]

def reasonedReplyGrammar : Grammar :=
  .frame fnctMagic 1 18 517 <|
    .seqCons (.enum 1 1 reasonedStatusNames) <| .seqCons (.bytes 4 1 512 .any) .seqNil

def identityReplyGrammar : Grammar :=
  .frame fnctMagic 1 25 2048 <|
    .tagArm 1 0 "accepted"
      (.seqCons (.bytes 2 1 512 .utf8) <| .seqCons (.bytes 1 32 32 .any) <|
        .seqCons (.bytes 1 32 32 .any) <| .seqCons (.bytes 1 32 32 .any) <|
        .seqCons (.tagArm 1 0 "unbootstrapped" .seqNil <|
          .tagArm 1 1 "bootstrapped"
            (.seqCons (.bytes 1 1 64 .any) <| .seqCons (.bytes 1 1 64 .any) .seqNil)
            (.tagNil 1)) <|
        .seqCons (.bytes 2 1 512 .utf8) <| .seqCons (.bytes 2 1 512 .utf8) <|
        .seqCons (.bytes 1 32 32 .any) .seqNil) <|
    .tagArm 1 1 "refused" (.enum 1 1 ["no-genesis", "consumer-state"]) (.tagNil 1)

theorem consumerReplyGrammar_wf : consumerReplyGrammar.wf = true := by decide
theorem statusReplyGrammar_wf : statusReplyGrammar.wf = true := by decide
theorem reasonedReplyGrammar_wf : reasonedReplyGrammar.wf = true := by decide
theorem identityReplyGrammar_wf : identityReplyGrammar.wf = true := by decide

/-- A frame is its octets of header, payload (at most the family's bound) and 32-octet trailer. -/
def frameBound (payloadMax : Nat) : Nat := 10 + payloadMax + 32

/-! ## Typed answers -/

/-- A reply of the consumer family: the outcome fn's owner gave, with the cursor an
acceptance carried (`position` carries one; `ack` none). -/
inductive ConsumerReply where
  | accepted (cursor : Option (FnConsumerScope.Scope × Nat))
  | refused
  | uncertain
  | fault
  /-- A reasoned reply (kind 18): fn's status word and reason word. -/
  | reasoned (status : String) (reason : List UInt8)

/-- The frame kind octet (header octet 5). -/
def frameKind : List UInt8 → Option UInt8
  | _ :: _ :: _ :: _ :: _ :: k :: _ => some k
  | _ => none

def outcomeOfName : String → Option ConsumerReply
  | "refused" => some .refused
  | "uncertain" => some .uncertain
  | "fault" => some .fault
  | _ => none

def consumerReplyOfValue : Value → Option ConsumerReply
  | .tagged "accepted" (.list []) => some (.accepted none)
  | .tagged "accepted" (.list [c]) =>
      match cursorOfValue c with
      | some sp => some (.accepted (some sp))
      | none => none
  | .tagged n (.list []) => outcomeOfName n
  | _ => none

/-- A reply to `ack` or `position`: a kind-5 frame, or a kind-18 reasoned refusal. -/
def decodeConsumerReply (frame : List UInt8) : Except Refusal ConsumerReply :=
  match frameKind frame with
  | some 5 =>
      match decodeWithin (frameBound 513) consumerReplyGrammar frame with
      | .ok v => match consumerReplyOfValue v with
        | some r => .ok r
        | none => .error .malformed
      | .error e => .error e
  | some 18 =>
      match decodeWithin (frameBound 517) reasonedReplyGrammar frame with
      | .ok (.list [.name s, .octets reason]) =>
          if s = "accepted" then .error .malformed else .ok (.reasoned s reason)
      | .ok _ => .error .malformed
      | .error e => .error e
  | _ => .error .malformed

/-- A `consumer status` reply. -/
inductive StatusReply where
  | accepted (committedAck frontier distance : Nat)
  | refused
  | uncertain
  | fault
  | reasoned (status : String) (reason : List UInt8)

def statusReplyOfValue : Value → Option StatusReply
  | .tagged "accepted" (.list [.nat a, .nat f, .nat d]) => some (.accepted a f d)
  | .tagged "refused" (.list []) => some .refused
  | .tagged "uncertain" (.list []) => some .uncertain
  | .tagged "fault" (.list []) => some .fault
  | _ => none

def decodeStatusReply (frame : List UInt8) : Except Refusal StatusReply :=
  match frameKind frame with
  | some 9 =>
      match decodeWithin (frameBound 13) statusReplyGrammar frame with
      | .ok v => match statusReplyOfValue v with
        | some r => .ok r
        | none => .error .malformed
      | .error e => .error e
  | some 18 =>
      match decodeWithin (frameBound 517) reasonedReplyGrammar frame with
      | .ok (.list [.name s, .octets reason]) =>
          if s = "accepted" then .error .malformed else .ok (.reasoned s reason)
      | .ok _ => .error .malformed
      | .error e => .error e
  | _ => .error .malformed

/-- What `fn identity` reports of a store. `grammarDigest` is the BLAKE3-256 of the
wire-grammar file the running image renders (compare `Compiler.FnWirePinned.pinnedDigest`). -/
structure Identity where
  format : List UInt8
  node : List UInt8
  schema : List UInt8
  profile : List UInt8
  /-- `none`: the consumer state is unbootstrapped; else its history id and incarnation. -/
  consumer : Option (List UInt8 × List UInt8)
  createdRevision : List UInt8
  runningRevision : List UInt8
  grammarDigest : List UInt8
  deriving DecidableEq, Repr

inductive IdentityReply where
  | accepted (identity : Identity)
  | refused (word : String)

def identityReplyOfValue : Value → Option IdentityReply
  | .tagged "accepted" (.list [.octets fmt, .octets node, .octets schema, .octets profile,
      .tagged "unbootstrapped" (.list []), .octets created, .octets running, .octets digest]) =>
      some (.accepted ⟨fmt, node, schema, profile, none, created, running, digest⟩)
  | .tagged "accepted" (.list [.octets fmt, .octets node, .octets schema, .octets profile,
      .tagged "bootstrapped" (.list [.octets h, .octets i]), .octets created, .octets running,
      .octets digest]) =>
      some (.accepted ⟨fmt, node, schema, profile, some (h, i), created, running, digest⟩)
  | .tagged "refused" (.name w) => some (.refused w)
  | _ => none

def decodeIdentityReply (frame : List UInt8) : Except Refusal IdentityReply :=
  match decodeWithin (frameBound 2048) identityReplyGrammar frame with
  | .ok v => match identityReplyOfValue v with
    | some r => .ok r
    | none => .error .malformed
  | .error e => .error e

/-! ### Poll replies (`fnct.consumer.poll-reply`, kind 6)

The family is in the pinned file since fn `1e190ff19`; `pollReplyGrammar` (`FnWireSized`) is
proved equal to it by `FnWirePinned.pollReply_is_pinned`. fn's `--frame` plan covers `status`,
`position` and `ack` only (`fn-ncr-frame-plan`, books/consumer-reason.lisp): `consumer --frame
poll` is a usage refusal today, so the Host's poll still reads fn's text line and the cursor and
report files, and nothing here is called from it yet. -/

/-- A poll reply: an accepted poll carries its cursor (behind a `sized` length) and the record
(the report), the other outcomes carry nothing. -/
inductive PollReply where
  | accepted (cursor : FnConsumerScope.Scope × Nat) (record : List UInt8)
  | refused
  | uncertain
  | fault

def pollReplyOfValue : Value → Option PollReply
  | .tagged "accepted" (.list [c, .octets record]) =>
      match cursorOfValue c with
      | some sp => some (.accepted sp record)
      | none => none
  | .tagged "refused" .null => some .refused
  | .tagged "uncertain" .null => some .uncertain
  | .tagged "fault" .null => some .fault
  | _ => none

/-- A poll-reply frame, within the caller's octet bound (a frame may declare up to 2^32 octets;
`limit` is the caller's, refused `limit` before any decoding work). -/
def decodePollReply (limit : Nat) (frame : List UInt8) : Except Refusal PollReply :=
  match decodeWithin limit pollReplyGrammar frame with
  | .ok v => match pollReplyOfValue v with
    | some r => .ok r
    | none => .error .malformed
  | .error e => .error e

/-- Each reader, from the printed line: hex, one newline, then the frame's reading. -/
def readConsumerReply (stdout : List UInt8) : Except Refusal ConsumerReply :=
  match frameOfStdout stdout with
  | some f => decodeConsumerReply f
  | none => .error .malformed

def readStatusReply (stdout : List UInt8) : Except Refusal StatusReply :=
  match frameOfStdout stdout with
  | some f => decodeStatusReply f
  | none => .error .malformed

def readIdentityReply (stdout : List UInt8) : Except Refusal IdentityReply :=
  match frameOfStdout stdout with
  | some f => decodeIdentityReply f
  | none => .error .malformed

/-- The longest line a `--frame` command prints: two hex digits per octet and the newline. -/
def maxFrameLine (payloadMax : Nat) : Nat := 2 * frameBound payloadMax + 1

#assert_axioms consumerReplyGrammar_wf statusReplyGrammar_wf reasonedReplyGrammar_wf
  identityReplyGrammar_wf

end Minidregg.Compiler.FnWire
