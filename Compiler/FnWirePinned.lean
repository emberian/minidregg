/-
# Compiler.FnWirePinned — fn's exported wire grammar at a pinned revision

`protocol/fn/wire-grammar.json` is fn's `specs/wire-grammar.json` at the commit
`pinnedRevision` (fn dev `1e190ff19`), vendored byte for byte. Its BLAKE3-256 is
`pinnedDigest`: the digest fn's running owner reports as `grammar-digest` in its
`fnct.store-identity.reply`, so the file Mini interprets and the image fn runs can be
compared by one value.

What this module establishes, at build time, against the vendored bytes:

* `pinned_digest` — the file's BLAKE3-256 (computed by `Compiler.Blake3`) is `pinnedDigest`;
* `pinned_vectors` — `checkDoc` passes on the file: every one of its 1140 vectors gets exactly
  the decoder answer the file prints, and the coverage fn §3 promises is present;
* `fncuCursor_is_pinned` — the `fncu.cursor` grammar Mini runs (`cursorGrammar`) is the
  file's family of that name;
* `fn_written_cursor` — a cursor fn wrote (evidence) decodes to its scope and position;
* teeth: a file with one vector's `consumed` changed, or one `rest` changed, or a `trailer`
  or `where` refusal answered `malformed`, or refusal words other than fn's three, is
  refused.

Re-pinning to another fn revision is: vendor the file, set `pinnedRevision` and
`pinnedDigest`, re-run this module and `scripts/check-fn-wire.sh`. The counts in
`pinned_vectors` change with it.

TRUST CLASS: compiled evaluation (`native_decide` + `#assert_compiled`) over a fixed file.
-/
import Compiler.FnWireJson
import Compiler.FnWireFncu
import Compiler.FnWireSized
import Theory.AssertCompiled

namespace Minidregg.Compiler.FnWire

/-- fn's commit the vendored file is taken from. -/
def pinnedRevision : String := "1e190ff19a2bd29cd5560ec8e5e7e22d27831e30"

/-- BLAKE3-256 of the vendored file. -/
def pinnedDigest : String := "db23c0981513032cf49924c34a34b03a9bc6cd1c7d2eb62ceaf8256605a70d6d"

/-- The vendored file. -/
def pinnedText : String := include_str "../protocol/fn/wire-grammar.json"

/-- The file Mini loads is the file fn's owner names by digest. -/
theorem pinned_digest : Blake3.toHex (Blake3.hash pinnedText.toUTF8.toList) = pinnedDigest := by
  native_decide

theorem pinned_length : pinnedText.utf8ByteSize = 234746 := by native_decide

/-- Every vector of the pinned file: 13 families, 1140 vectors, 116 accepted answers and 1024
refusals (counts from `checkDoc`, run on the vendored bytes). -/
theorem pinned_vectors : checkPasses pinnedText ⟨13, 116, 1024⟩ = true := by native_decide

theorem fncuCursor_is_pinned : familyIs pinnedText "fncu.cursor" cursorGrammar = true := by
  native_decide

/-- Tooth: one accepted vector's `consumed` off by one is refused. -/
theorem pinned_refuses_consumed_fault :
    checkRefuses (pinnedText.replace "\"consumed\":32," "\"consumed\":33,") = true := by
  native_decide

/-- Tooth: a `rest` the decoder does not leave is refused. -/
theorem pinned_refuses_rest_fault :
    checkRefuses (pinnedText.replace "\"rest\":\"\"" "\"rest\":\"00\"") = true := by
  native_decide

/-- Tooth: a trailer refusal answered `malformed` is refused (the words are distinct). -/
theorem pinned_refuses_word_fault :
    checkRefuses (pinnedText.replace "\"refused\":\"trailer\"" "\"refused\":\"malformed\"") =
      true := by
  native_decide

/-- Tooth: a failed `where` check answered `malformed` is refused (`where` is its own word). -/
theorem pinned_refuses_where_fault :
    checkRefuses (pinnedText.replace "\"refused\":\"where\"" "\"refused\":\"malformed\"") =
      true := by
  native_decide

/-- Tooth: a file whose refusal words are not exactly fn's three is refused. -/
theorem pinned_refuses_words_fault :
    checkRefuses (pinnedText.replace "\"refusals\":[\"trailer\",\"where\",\"malformed\"]"
      "\"refusals\":[\"trailer\",\"malformed\"]") = true := by
  native_decide

#assert_compiled pinned_refuses_where_fault
#assert_compiled pinned_refuses_words_fault
#assert_compiled pinned_digest
#assert_compiled pinned_length
#assert_compiled pinned_vectors
#assert_compiled fncuCursor_is_pinned
#assert_compiled pinned_refuses_consumed_fault
#assert_compiled pinned_refuses_rest_fault
#assert_compiled pinned_refuses_word_fault

/-! ## A cursor fn wrote

`docs/evidence/2026-09-26-workroom-content-reply/a-retained.fncu`, written by fn's local
consumer (sha256 in that directory's `sha256.txt`); `scripts/check-fn-wire.sh` checks that
the literal below is that file. -/

/-- The octets of the evidence cursor. -/
def fnWrittenCursorHex : String :=
  "666e63750120eb87ce0258e3522fb13f96b9daaaef0767285055daeb6076d789c1f169cefd50204b319ac4f9f145a8e705a02714b7583e3c2bfcdacbdd9d4a0552b576bd8b05c606776f726b6572056c6f63616c07666e2e7465737400000001000000000000000100000006"

def fnWrittenCursor : List UInt8 := (hexBytes? fnWrittenCursorHex.toList).getD []

def cursorIs (xs : List UInt8) (consumer principal query : String) (qv vv epoch pos : Nat) : Bool :=
  match decodeCursor xs with
  | .ok (s, p) =>
      s.consumer == consumer.toUTF8.toList && s.principal == principal.toUTF8.toList &&
        s.query == query.toUTF8.toList && s.history.length == 32 &&
        s.incarnation.length == 32 && s.queryVersion == qv && s.viewVersion == vv &&
        s.registrationEpoch == epoch && p == pos
  | .error _ => false

/-- fn's cursor reads as consumer `worker`, principal `local`, query `fn.test` v1, view 0,
epoch 1, position 6 (and, by `decodeCursor_canonical`, re-encodes to the same octets). -/
theorem fn_written_cursor :
    fnWrittenCursor.length = 108 ∧ cursorIs fnWrittenCursor "worker" "local" "fn.test" 1 0 1 6 = true := by
  native_decide

/-- Teeth: one trailing octet, and registration epoch 0, are each refused `malformed`. -/
theorem fn_written_cursor_mutants :
    decodeCursor (fnWrittenCursor ++ [0]) = .error .malformed ∧
      decodeCursor (fnWrittenCursor.take 100 ++ [0, 0, 0, 0] ++ fnWrittenCursor.drop 104) =
        .error .malformed := by
  native_decide

#assert_compiled fn_written_cursor
#assert_compiled fn_written_cursor_mutants

/-! ## fn's own poll-reply vectors

`Compiler.FnWireSized.pollReplyGrammar` is the pinned family, and the octets below are `accept`
vectors of the pinned file (fn rendered them): the accepted reply whose cursor is 32 octets
and whose record is 64 octets of 07, and the three refusals. They decode through the `sized`
arm to fn's printed values. -/

theorem pollReply_is_pinned :
    familyIs pinnedText "fnct.consumer.poll-reply" pollReplyGrammar = true := by native_decide

def octetsOfHex (h : String) : List UInt8 := (hexBytes? h.toList).getD []

def pollAcceptedHex : String :=
  "464e43540106000000690000000020666e63750102112201330144015501660000000100000001ffffffff00000000000000400707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070707070758d85619e4b0fa8cfd0403f635457326a7eabeafecabdc4351feb7b6b1ab9e47"

def pollRefusedHex : String :=
  "464e4354010600000009010000000000000000ae4a65ebe231f89b95f7eafb78e3379bcd7dd2d4e7c053cfdfcfd6596eb35816"
def pollUncertainHex : String :=
  "464e43540106000000090200000000000000008bdff36a65ceb7e6dffdc3a61cd593726adc997eb7b8161261c2d73bcfdbe089"
def pollFaultHex : String :=
  "464e4354010600000009030000000000000000f0a04c327758509dd826c2230e57ccf9f78193d94cd9c5a0cfc6b96bd78c36b9"

def pollAcceptedIs (xs : List UInt8) (epoch pos : Nat) (record : List UInt8) : Bool :=
  match decodeAll pollReplyGrammar xs with
  | .ok (.tagged "accepted" (.list [c, .octets t])) =>
      (cursorOfValue c).map (fun sp => (sp.1.registrationEpoch, sp.2)) == some (epoch, pos) &&
        t == record
  | _ => false

def pollIs (xs : List UInt8) (name : String) : Bool :=
  match decodeAll pollReplyGrammar xs with
  | .ok (.tagged n .null) => n == name
  | _ => false

def pollRefusal (xs : List UInt8) (e : Refusal) : Bool :=
  match decodeAll pollReplyGrammar xs with
  | .error r => r == e
  | .ok _ => false

/-- fn's accepted poll reply reads as registration epoch 4294967295 and position 0 and the 64-octet record; its three
refusals as `refused`, `uncertain`, `fault`; the accepted octets are canonical (re-encoding the
decoded value gives them back). -/
theorem poll_reply_vectors :
    pollAcceptedIs (octetsOfHex pollAcceptedHex) 4294967295 0 (List.replicate 64 7) = true ∧
    pollIs (octetsOfHex pollRefusedHex) "refused" = true ∧
    pollIs (octetsOfHex pollUncertainHex) "uncertain" = true ∧
    pollIs (octetsOfHex pollFaultHex) "fault" = true ∧
    (match decodeAll pollReplyGrammar (octetsOfHex pollAcceptedHex) with
      | .ok v => encode pollReplyGrammar v == .ok (octetsOfHex pollAcceptedHex)
      | .error _ => false) = true := by
  native_decide

/-- Teeth: the cursor length one short and one long (the `sized` region and what follows
disagree), the accepted frame cut inside the cursor, and one payload octet changed (the trailer
refuses it) are each refused. -/
theorem poll_reply_teeth :
    pollRefusal (octetsOfHex (pollAcceptedHex.replace "69000000002066" "69000000002166")) .trailer = true ∧
    pollRefusal ((octetsOfHex pollAcceptedHex).take 50) .malformed = true ∧
    pollRefusal ((octetsOfHex pollAcceptedHex) ++ [0]) .malformed = true := by
  native_decide

#assert_compiled pollReply_is_pinned
#assert_compiled poll_reply_vectors
#assert_compiled poll_reply_teeth

end Minidregg.Compiler.FnWire
