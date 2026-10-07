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
import Compiler.FnWireConsumer
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

/-! ## The reply families Mini reads

`Compiler.FnWireConsumer`'s grammars are the pinned file's families of those names. -/

theorem consumerReply_is_pinned :
    familyIs pinnedText "fnct.consumer.reply" consumerReplyGrammar = true := by native_decide
theorem statusReply_is_pinned :
    familyIs pinnedText "fnct.consumer.status-reply" statusReplyGrammar = true := by native_decide
theorem reasonedReply_is_pinned :
    familyIs pinnedText "fnct.reasoned-reply" reasonedReplyGrammar = true := by native_decide
theorem identityReply_is_pinned :
    familyIs pinnedText "fnct.store-identity.reply" identityReplyGrammar = true := by native_decide

#assert_compiled consumerReply_is_pinned
#assert_compiled statusReply_is_pinned
#assert_compiled reasonedReply_is_pinned
#assert_compiled identityReply_is_pinned

/-! ## fn-rendered accept vectors, read as a `--frame` line

The octets below are `accept` vectors of the pinned file (fn rendered them: its ACL2 encoder
produced them and fn's own check decodes each to the printed value). Each is read exactly as
`fn ... --frame` prints it: lowercase hex and one newline. -/

def lineOf (hex : String) : List UInt8 := (hex ++ "\n").toUTF8.toList

def consumerReplyCursorHex : String :=
  "464e435401050000006200666e637501010140ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff020203010403050607000000000000000900000001ffffffffef46ed3350e1a44698242a0ef9f346ffe0726a90f96b80af15f0f72f781628d1"
def consumerReplyAcceptedHex : String :=
  "464e435401050000000100b961207007462e3a5ac2cfa2ff965536f0bf7628dbf1426a7dbfca7bf60f26ca"
def consumerReplyRefusedHex : String :=
  "464e435401050000000101b12723a10100f1500fdb79c6dcda3d69fbc33cf8b08f59f149d74e6645021609"
def consumerReplyUncertainHex : String :=
  "464e435401050000000102efea37b0624a376479b724a7c2fc9a63198bc0feb187d1e405e6a53701e6173c"
def consumerReplyFaultHex : String :=
  "464e4354010500000001037f0c7fe0a870661f09d06e6afe1578104a731d0f24c7a242b10ff3131c3518a0"

def consumerReplyIs (hex : String) (p : ConsumerReply → Bool) : Bool :=
  match readConsumerReply (lineOf hex) with
  | .ok r => p r
  | .error _ => false

def consumerReplyMalformed (line : List UInt8) : Bool :=
  match readConsumerReply line with
  | .error .malformed => true
  | _ => false

/-- fn's five `fnct.consumer.reply` accept vectors read as the five outcomes; the first carries a
cursor with registration epoch 1 and position 4294967295. -/
theorem consumer_reply_vectors :
    consumerReplyIs consumerReplyCursorHex
      (fun | .accepted (some (s, pos)) => pos == 4294967295 && s.registrationEpoch == 1
           | _ => false) = true ∧
    consumerReplyIs consumerReplyAcceptedHex (fun | .accepted none => true | _ => false) = true ∧
    consumerReplyIs consumerReplyRefusedHex (fun | .refused => true | _ => false) = true ∧
    consumerReplyIs consumerReplyUncertainHex (fun | .uncertain => true | _ => false) = true ∧
    consumerReplyIs consumerReplyFaultHex (fun | .fault => true | _ => false) = true := by
  native_decide

/-- Teeth: the same frame without its newline, with a second newline, in upper case, one
octet longer, and with one payload octet changed (the trailer refuses it) is `malformed` or
`trailer`; and a kind-5 frame is no status reply. -/
theorem consumer_reply_teeth :
    consumerReplyMalformed (consumerReplyAcceptedHex.toUTF8.toList) = true ∧
    consumerReplyMalformed (lineOf consumerReplyAcceptedHex ++ [10]) = true ∧
    consumerReplyMalformed (lineOf (consumerReplyAcceptedHex.toUpper)) = true ∧
    consumerReplyMalformed (lineOf (consumerReplyAcceptedHex ++ "00")) = true ∧
    (match readConsumerReply
        (lineOf (consumerReplyAcceptedHex.replace "050000000100" "050000000101")) with
      | .error .trailer => true
      | _ => false) = true ∧
    (match decodeStatusReply ((lowerHexOctets? consumerReplyAcceptedHex.toUTF8.toList).getD []) with
      | .error .malformed => true
      | _ => false) = true := by
  native_decide

def statusAcceptedHex : String :=
  "464e435401090000000d00000000030000000a000000077ba07b993314b2ceced2417a867e6c653966df20776bc48df5af1baf8024ff62"
def statusRefusedHex : String :=
  "464e43540109000000010190033e4dc43f9f3eb50df78410fbf64d14c9e66409ccdd27da65fd46e1474252"

def statusReplyIs (hex : String) (p : StatusReply → Bool) : Bool :=
  match readStatusReply (lineOf hex) with
  | .ok r => p r
  | .error _ => false

/-- fn's status accept vector reads as committed ack 3, frontier 10, distance 7; its refusal
vector as `refused`. -/
theorem status_reply_vectors :
    statusReplyIs statusAcceptedHex
      (fun | .accepted a f d => a == 3 && f == 10 && d == 7 | _ => false) = true ∧
    statusReplyIs statusRefusedHex (fun | .refused => true | _ => false) = true := by
  native_decide

/-- Teeth: a status frame whose distance is not frontier − ack is refused by the `where`
(one payload octet changed and the trailer recomputed is fn's `where` vector family; here the
unrecomputed change is refused by the trailer, and a frame of another kind is `malformed`). -/
theorem status_reply_teeth :
    (match readStatusReply (lineOf (statusAcceptedHex.replace "0a0000000" "0b0000000")) with
      | .error .trailer => true
      | _ => false) = true ∧
    (match readStatusReply (lineOf consumerReplyAcceptedHex) with
      | .error .malformed => true
      | _ => false) = true := by
  native_decide

def reasonedRefusedHex : String :=
  "464e435401120000000d03000000086e6f2d6f776e6572a2873d3118da4a59d71e9203ae8573d20f087287cc871b860289f0f68bade94b"
def reasonedAcceptedHex : String :=
  "464e435401120000000901000000044e4f4e457b1d3892b4cea54dd183f4d1ab850d6ccb08cb4821c59eb07b8c82055e450b56"

/-- A reasoned reply reads as fn's status word and reason (`refused`, "no-owner") for both
`ack`/`position` and `status`; one whose status word is `accepted` is refused (an acceptance
never comes as a reasoned reply). -/
theorem reasoned_reply_vectors :
    (match readConsumerReply (lineOf reasonedRefusedHex), readStatusReply (lineOf reasonedRefusedHex) with
      | .ok (.reasoned "refused" r), .ok (.reasoned "refused" r') =>
          r == "no-owner".toUTF8.toList && r' == "no-owner".toUTF8.toList
      | _, _ => false) = true ∧
    consumerReplyMalformed (lineOf reasonedAcceptedHex) = true := by
  native_decide

def identityBootstrappedHex : String :=
  "464e435401190000010800000b666e2d73746f72652d3130200101010101010101010101010101010101010101010101010101010101010101200202020202020202020202020202020202020202020202020202020202020202200303030303030303030303030303030303030303030303030303030303030303012004040404040404040404040404040404040404040404040404040404040404042005050505050505050505050505050505050505050505050505050505050505050028303132333435363738396162636465663031323334353637383961626364656630313233343536370007756e6b6e6f776e200606060606060606060606060606060606060606060606060606060606060606dcac1e12cb3d1f92eaf441989754f053b99ac64de2d68401cd79051a810b72e9"
def identityUnbootstrappedHex : String :=
  "464e43540119000000a500000b666e2d73746f72652d3130200101010101010101010101010101010101010101010101010101010101010101200202020202020202020202020202020202020202020202020202020202020202200303030303030303030303030303030303030303030303030303030303030303000007756e6b6e6f776e0007756e6b6e6f776e2006060606060606060606060606060606060606060606060606060606060606068cee1850c297149da1d53b5a7dc5d573cccba9ccbb730da596b7f310203140dd"
def identityNoGenesisHex : String :=
  "464e43540119000000020101e6a1f30d569d0e1f668a6c749525903fd694b1a97ecb79598536329c8212a916"

def identityIs (hex : String) (p : IdentityReply → Bool) : Bool :=
  match readIdentityReply (lineOf hex) with
  | .ok r => p r
  | .error _ => false

def fill (n b : UInt8) : List UInt8 := List.replicate n.toNat b

/-- fn's identity vectors: the bootstrapped one reads as node 01x32, schema 02x32, profile 03x32,
history 04x32, incarnation 05x32 and grammar digest 06x32; the unbootstrapped one has no
consumer state; the refusal names `no-genesis`. -/
theorem identity_reply_vectors :
    identityIs identityBootstrappedHex
      (fun | .accepted i => i.node == fill 32 1 && i.schema == fill 32 2 &&
                i.profile == fill 32 3 && i.consumer == some (fill 32 4, fill 32 5) &&
                i.grammarDigest == fill 32 6 && i.runningRevision == "unknown".toUTF8.toList
           | _ => false) = true ∧
    identityIs identityUnbootstrappedHex
      (fun | .accepted i => i.consumer == none && i.grammarDigest == fill 32 6 | _ => false) = true ∧
    identityIs identityNoGenesisHex
      (fun | .refused "no-genesis" => true | _ => false) = true := by
  native_decide

/-- The identity the Host accepts of a running owner: the file it renders is the file Mini
interprets (`grammarDigest` is `pinnedDigest`), and node, schema, consumer history and
incarnation are the pinned scope's. Each disagreement is a refusal by name. -/
inductive IdentityRefusal where
  | grammarDigest | node | schema | consumer
  deriving DecidableEq, Repr

def Identity.check (i : Identity) (node schema history incarnation : List UInt8) :
    Except IdentityRefusal Unit :=
  if Blake3.toHex i.grammarDigest ≠ pinnedDigest then .error .grammarDigest
  else if i.node ≠ node then .error .node
  else if i.schema ≠ schema then .error .schema
  else if i.consumer ≠ some (history, incarnation) then .error .consumer
  else .ok ()

def IdentityRefusal.word : IdentityRefusal → String
  | .grammarDigest => "grammar-digest" | .node => "node" | .schema => "schema"
  | .consumer => "consumer"

/-- The fn vector's own identity, with the digest of the file it would render if it ran the pinned
image (`pinnedDigest`): the real fixture the checks are exercised on. -/
def vectorIdentity (digest : List UInt8) : Identity :=
  ⟨(lowerHexOctets? "666e2d73746f72652d3130".toUTF8.toList).getD [], fill 32 1, fill 32 2, fill 32 3,
    some (fill 32 4, fill 32 5), "unknown".toUTF8.toList, "unknown".toUTF8.toList, digest⟩

def refusesWith (r : Except IdentityRefusal Unit) (w : IdentityRefusal) : Bool :=
  match r with
  | .error e => e == w
  | .ok _ => false

theorem identity_binds_pinned_store :
    (match (vectorIdentity ((lowerHexOctets? pinnedDigest.toUTF8.toList).getD [])).check
        (fill 32 1) (fill 32 2) (fill 32 4) (fill 32 5) with
      | .ok _ => true | .error _ => false) = true ∧
    -- the fn vector's own digest (06 x 32) is not the pinned file's
    refusesWith ((vectorIdentity (fill 32 6)).check (fill 32 1) (fill 32 2) (fill 32 4) (fill 32 5))
      .grammarDigest = true ∧
    refusesWith ((vectorIdentity ((lowerHexOctets? pinnedDigest.toUTF8.toList).getD [])).check
        (fill 32 9) (fill 32 2) (fill 32 4) (fill 32 5)) .node = true ∧
    refusesWith ((vectorIdentity ((lowerHexOctets? pinnedDigest.toUTF8.toList).getD [])).check
        (fill 32 1) (fill 32 9) (fill 32 4) (fill 32 5)) .schema = true ∧
    refusesWith ((vectorIdentity ((lowerHexOctets? pinnedDigest.toUTF8.toList).getD [])).check
        (fill 32 1) (fill 32 2) (fill 32 4) (fill 32 9)) .consumer = true := by
  native_decide

#assert_compiled identity_binds_pinned_store
#assert_compiled consumer_reply_vectors
#assert_compiled consumer_reply_teeth
#assert_compiled status_reply_vectors
#assert_compiled status_reply_teeth
#assert_compiled reasoned_reply_vectors
#assert_compiled identity_reply_vectors

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

/-- Typed: fn's poll-reply vectors read as `PollReply` (accepted with epoch 4294967295, position
0 and the 64-octet record; the refusals), and a frame over the caller's bound is refused `limit`. -/
theorem poll_reply_typed :
    (match decodePollReply 4096 (octetsOfHex pollAcceptedHex) with
      | .ok (.accepted (s, pos) r) =>
          s.registrationEpoch == 4294967295 && pos == 0 && r == List.replicate 64 7
      | _ => false) = true ∧
    (match decodePollReply 4096 (octetsOfHex pollRefusedHex) with | .ok .refused => true | _ => false) = true ∧
    (match decodePollReply 4096 (octetsOfHex pollUncertainHex) with | .ok .uncertain => true | _ => false) = true ∧
    (match decodePollReply 4096 (octetsOfHex pollFaultHex) with | .ok .fault => true | _ => false) = true ∧
    (match decodePollReply 100 (octetsOfHex pollAcceptedHex) with | .error .limit => true | _ => false) = true := by
  native_decide

#assert_compiled poll_reply_typed
#assert_compiled pollReply_is_pinned
#assert_compiled poll_reply_vectors
#assert_compiled poll_reply_teeth

end Minidregg.Compiler.FnWire
