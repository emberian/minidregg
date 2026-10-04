/-
# Compiler.FnWirePinned — fn's exported wire grammar at a pinned revision

`protocol/fn/wire-grammar.json` is fn's `specs/wire-grammar.json` at the commit
`pinnedRevision` (fn `lane/mini-contract`), vendored byte for byte. Its BLAKE3-256 is
`pinnedDigest`: the digest fn's running owner reports as `grammar-digest` in its
`fnct.store-identity.reply`, so the file Mini interprets and the image fn runs can be
compared by one value.

What this module establishes, at build time, against the vendored bytes:

* `pinned_digest` — the file's BLAKE3-256 (computed by `Compiler.Blake3`) is `pinnedDigest`;
* `pinned_vectors` — `checkDoc` passes on the file: every one of its 249 vectors gets exactly
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
import Theory.AssertCompiled

namespace Minidregg.Compiler.FnWire

/-- fn's commit the vendored file is taken from. -/
def pinnedRevision : String := "930c67414ab9f866fd918465dcedeaeb9640437f"

/-- BLAKE3-256 of the vendored file. -/
def pinnedDigest : String := "d5f516610458cfa0b3d001a5cfba983482ef9520bbcc5445dc0afc849c745454"

/-- The vendored file. -/
def pinnedText : String := include_str "../protocol/fn/wire-grammar.json"

/-- The file Mini loads is the file fn's owner names by digest. -/
theorem pinned_digest : Blake3.toHex (Blake3.hash pinnedText.toUTF8.toList) = pinnedDigest := by
  native_decide

theorem pinned_length : pinnedText.utf8ByteSize = 64056 := by native_decide

/-- Every vector of the pinned file: 6 families (three on a wire, three `conformance.*`),
356 vectors, 60 accepted answers and 296 refusals. -/
theorem pinned_vectors : checkPasses pinnedText ⟨6, 60, 296⟩ = true := by native_decide

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

end Minidregg.Compiler.FnWire
