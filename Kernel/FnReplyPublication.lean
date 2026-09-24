/-
The bounded B3 reply source is selected from a reopened Mini operation Q and
its retained fn parent, plus independently chosen signer keys. This module
only constructs an unsigned exact source. A separate durable prepared plan
must exist before signing, and the resulting signatures must be durably
staged before any fn post.
-/
import Kernel.FnConsumerOperation

namespace Minidregg.Kernel.FnReplyPublication

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.FnConsumerOperation

set_option autoImplicit false

structure Selection where
  domain : Digest
  semantics : Digest
  miniTransaction : Digest
  miniEvent : Digest
  reply : Reply
  parentSourceIdentity : List UInt8
  parentMessageId : List UInt8
  principal : List UInt8
  edPublicKey : List UInt8
  mlPublicKey : List UInt8
  deriving DecidableEq, Repr

def selectionStream : StreamCodec Selection :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product digestStream (StreamCodec.product digestStream
        (StreamCodec.product replyStream (StreamCodec.product bytesStream
          (StreamCodec.product bytesStream (StreamCodec.product bytesStream
            (StreamCodec.product bytesStream bytesStream)))))))))
    (fun value => (value.domain, value.semantics, value.miniTransaction,
      value.miniEvent, value.reply, value.parentSourceIdentity,
      value.parentMessageId, value.principal, value.edPublicKey,
      value.mlPublicKey))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1,
      value.2.2.2.2.1, value.2.2.2.2.2.1, value.2.2.2.2.2.2.1,
      value.2.2.2.2.2.2.2.1, value.2.2.2.2.2.2.2.2.1,
      value.2.2.2.2.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

private def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then '0'.toNat + n else 'a'.toNat + n - 10)

def hexBytes (bytes : List UInt8) : String :=
  String.ofList <| bytes.flatMap fun byte =>
    [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]

def Selection.valid (value : Selection) : Bool :=
  value.parentSourceIdentity.length == 48 &&
  value.reply.sourceIdentity == value.parentSourceIdentity &&
  value.parentMessageId.length ≥ 3 &&
  value.parentMessageId.length ≤ 256 &&
  value.parentMessageId.head? == some 60 &&
  value.parentMessageId.getLast? == some 62 &&
  value.parentMessageId.all (fun b => 33 ≤ b.toNat && b.toNat ≤ 126) &&
  value.principal.length == 32 && value.edPublicKey.length == 32 &&
  value.mlPublicKey.length == 1952 &&
  (replyCodec.encode value.reply).length ≤ 400

/-- The fully framed preimage includes the Mini accepted event and independent
signer selection. Concatenated unframed fields would admit boundary aliases. -/
def Selection.identityPreimage (value : Selection) : List UInt8 :=
  let codec := StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product bytesStream (StreamCodec.product bytesStream
        (StreamCodec.product bytesStream (StreamCodec.product bytesStream
          (StreamCodec.product bytesStream bytesStream))))))))
  codec.encode (value.domain, value.semantics, value.miniTransaction,
    value.miniEvent, replyCodec.encode value.reply,
    value.parentMessageId, value.parentSourceIdentity,
    value.principal, value.edPublicKey, value.mlPublicKey)

def Selection.messageId (value : Selection) : String :=
  let digest := Sp800185Cshake256.hash
    "DREGG.FN.REPLY-MSGID/v2".toUTF8.toList value.identityPreimage
  "<mini-e2-" ++ hexBytes (digestStream.encode digest.digest) ++ "@example.invalid>"

/-- Fixed local fn.test experiment profile. The application Q is encoded as
ASCII hexadecimal, so its arbitrary binary bytes cannot inject headers or
article terminators. The exact source and ID are stable for a Selection.
The fixed Date below is only this synthetic profile's signed source Date;
a general publication profile must select its creation Date once and retain
that choice in the durable prepared plan. -/
private def experimentDateLine : String :=
  "Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n"

def Selection.source (value : Selection) : Except String (List UInt8) := do
  unless value.valid do throw "reply publication selection is outside bounded profile"
  let article := "From: mini-e2@example.invalid\r\n" ++
    experimentDateLine ++
    "Newsgroups: fn.test\r\n" ++
    "Subject: Mini E2 reply\r\n" ++
    "Message-ID: " ++ value.messageId ++ "\r\n" ++
    "In-Reply-To: " ++
      String.fromUTF8! value.parentMessageId.toByteArray ++ "\r\n" ++
    "Content-Type: application/vnd.dregg.fn-reply; version=1\r\n" ++
    "\r\n" ++ hexBytes (replyCodec.encode value.reply) ++ "\r\n"
  let bytes := article.toUTF8.toList
  unless bytes.length ≤ 32768 do throw "fn reply source exceeds bound"
  pure bytes

/-- The absent-only sidecar's first durable value. The source and Message-ID
are stored explicitly and checked against their Lean derivation on reopen. -/
structure Prepared where
  selection : Selection
  source : List UInt8
  messageId : List UInt8
  deriving DecidableEq, Repr

def preparedStream : StreamCodec Prepared :=
  StreamCodec.xmap
    (StreamCodec.product selectionStream
      (StreamCodec.product bytesStream bytesStream))
    (fun value => (value.selection, value.source, value.messageId))
    (fun value => ⟨value.1, value.2.1, value.2.2⟩)
    (by intro value; cases value; rfl)

def preparedCodec : LawfulCodec Prepared :=
  NativeHostCodec.framed "DREGG/FN/REPLY-PREPARED/v1".toUTF8.toList
    preparedStream

def Selection.prepare (value : Selection) : Except String Prepared := do
  let source ← value.source
  let prepared : Prepared := ⟨value, source, value.messageId.toUTF8.toList⟩
  unless (preparedCodec.encode prepared).length ≤ 8192 do
    throw "fn reply prepared record exceeds bound"
  pure prepared

def Prepared.valid (value : Prepared) : Bool :=
  (preparedCodec.encode value).length ≤ 8192 &&
  value.messageId == value.selection.messageId.toUTF8.toList &&
  match value.selection.source with
  | .ok source => source == value.source
  | .error _ => false

/-- The second absent-only sidecar value. The exact fn native signer output is
retained here before any post attempt. Signature validity is established by
fn's native profile; Lean checks byte widths and the durable prepared plan. -/
structure Signed where
  prepared : Prepared
  sourceIdentity : List UInt8
  edSignature : List UInt8
  mlSignature : List UInt8
  deriving DecidableEq, Repr

def signedStream : StreamCodec Signed :=
  StreamCodec.xmap
    (StreamCodec.product preparedStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream bytesStream)))
    (fun value => (value.prepared, value.sourceIdentity,
      value.edSignature, value.mlSignature))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩)
    (by intro value; cases value; rfl)

def signedCodec : LawfulCodec Signed :=
  NativeHostCodec.framed "DREGG/FN/REPLY-SIGNED/v1".toUTF8.toList
    signedStream

def Signed.valid (value : Signed) : Bool :=
  value.prepared.valid && value.sourceIdentity.length == 48 &&
  value.edSignature.length == 64 &&
  value.mlSignature.length == 3309 &&
  (signedCodec.encode value).length ≤ 12288

end Minidregg.Kernel.FnReplyPublication
