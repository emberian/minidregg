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

/-- Operator-selected creation metadata. These exact bytes are frozen by the
prepared record before fn signs or posts the article. -/
structure CreationContext where
  fromMailbox : String
  newsgroup : String
  messageIdDomain : String
  date : String
  deriving DecidableEq, Repr

def CreationContext.synthetic : CreationContext :=
  ⟨"mini-e2@example.invalid", "fn.test", "example.invalid",
   "Wed, 23 Sep 2026 12:00:00 +0000"⟩

private def asciiLabel (value : String) : Bool :=
  !value.isEmpty && value.length ≤ 63 &&
  value.toList.all (fun c =>
    (97 ≤ c.toNat && c.toNat ≤ 122) ||
    (48 ≤ c.toNat && c.toNat ≤ 57) || c == '-') &&
  value.toList.head? != some '-' && value.toList.getLast? != some '-'

private def dottedName (value : String) : Bool :=
  value.length ≤ 253 &&
  match value.splitOn "." with
  | [] | [_] => false
  | labels => labels.all asciiLabel

private def mailbox (value : String) : Bool :=
  value.length ≤ 254 &&
  match value.splitOn "@" with
  | [localPart, domain] =>
      !localPart.isEmpty && localPart.length ≤ 64 &&
      localPart.toList.all (fun c =>
        (65 ≤ c.toNat && c.toNat ≤ 90) ||
        (97 ≤ c.toNat && c.toNat ≤ 122) ||
        (48 ≤ c.toNat && c.toNat ≤ 57) ||
        ['.', '_', '+', '-'].contains c) &&
      dottedName domain
  | _ => false

private def decimalRange (value : String) (width lo hi : Nat) : Bool :=
  value.length == width && value.toList.all (fun c => 48 ≤ c.toNat && c.toNat ≤ 57) &&
  match value.toNat? with
  | some n => lo ≤ n && n ≤ hi
  | none => false

/-- A bounded canonical RFC-style numeric-zone Date. fn still owns article
admission; this check fixes the source syntax and excludes header injection. -/
private def dateSafe (value : String) : Bool :=
  match value.splitOn " " with
  | [weekday, day, month, year, clock, zone] =>
      ["Mon,", "Tue,", "Wed,", "Thu,", "Fri,", "Sat,", "Sun,"].contains weekday &&
      decimalRange day 2 1 31 &&
      ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug",
       "Sep", "Oct", "Nov", "Dec"].contains month &&
      decimalRange year 4 1 9999 &&
      (match clock.splitOn ":" with
       | [hour, minute, second] =>
           decimalRange hour 2 0 23 && decimalRange minute 2 0 59 &&
           decimalRange second 2 0 60
       | _ => false) &&
      (match zone.toList with
       | sign :: digits =>
           (sign == '+' || sign == '-') &&
           decimalRange (String.ofList (digits.take 2)) 2 0 23 &&
           decimalRange (String.ofList (digits.drop 2)) 2 0 59
       | _ => false)
  | _ => false

def CreationContext.valid (value : CreationContext) : Bool :=
  mailbox value.fromMailbox && dottedName value.newsgroup &&
  dottedName value.messageIdDomain &&
  value.messageIdDomain.length ≤ 179 && dateSafe value.date

def creationContextStream : StreamCodec CreationContext :=
  StreamCodec.xmap
    (StreamCodec.product PolicyRecordCodec.stringStream
      (StreamCodec.product PolicyRecordCodec.stringStream
        (StreamCodec.product PolicyRecordCodec.stringStream
          PolicyRecordCodec.stringStream)))
    (fun value => (value.fromMailbox, value.newsgroup,
      value.messageIdDomain, value.date))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩)
    (by intro value; cases value; rfl)

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
  creation : CreationContext
  deriving DecidableEq, Repr

structure LegacySelection where
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

private def legacySelectionStream : StreamCodec LegacySelection :=
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

def selectionStream : StreamCodec Selection :=
  StreamCodec.xmap
    (StreamCodec.product legacySelectionStream creationContextStream)
    (fun value => (⟨value.domain, value.semantics, value.miniTransaction,
      value.miniEvent, value.reply, value.parentSourceIdentity, value.parentMessageId,
      value.principal, value.edPublicKey, value.mlPublicKey⟩, value.creation))
    (fun value => ⟨value.1.domain, value.1.semantics, value.1.miniTransaction,
      value.1.miniEvent, value.1.reply, value.1.parentSourceIdentity,
      value.1.parentMessageId, value.1.principal, value.1.edPublicKey,
      value.1.mlPublicKey, value.2⟩)
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
  value.creation.valid &&
  (replyCodec.encode value.reply).length ≤ 400

/-- The fully framed preimage includes the Mini accepted event and independent
signer selection. Concatenated unframed fields would admit boundary aliases. -/
def Selection.identityPreimage (value : Selection) : List UInt8 :=
  let codec := StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product bytesStream (StreamCodec.product bytesStream
        (StreamCodec.product bytesStream (StreamCodec.product bytesStream
          (StreamCodec.product bytesStream bytesStream))))))))
  let old := codec.encode (value.domain, value.semantics, value.miniTransaction,
    value.miniEvent, replyCodec.encode value.reply,
    value.parentMessageId, value.parentSourceIdentity,
    value.principal, value.edPublicKey, value.mlPublicKey)
  (StreamCodec.product bytesStream creationContextStream).encode
    (old, value.creation)

def Selection.messageId (value : Selection) : String :=
  let digest := Sp800185Cshake256.hash
    "DREGG.FN.REPLY-MSGID/v3".toUTF8.toList value.identityPreimage
  "<mini-e2-" ++ hexBytes (digestStream.encode digest.digest) ++
    "@" ++ value.creation.messageIdDomain ++ ">"

/-- Build the exact contextual article. Hexadecimal Q bytes cannot inject
headers or article terminators. The prepared record retains this source and
all operator-selected creation fields before any signature or post. -/
def Selection.source (value : Selection) : Except String (List UInt8) := do
  unless value.valid do throw "reply publication selection is outside bounded profile"
  let article := "From: " ++ value.creation.fromMailbox ++ "\r\n" ++
    "Date: " ++ value.creation.date ++ "\r\n" ++
    "Newsgroups: " ++ value.creation.newsgroup ++ "\r\n" ++
    "Subject: Mini E2 reply\r\n" ++
    "Message-ID: " ++ value.messageId ++ "\r\n" ++
    "In-Reply-To: " ++
      String.fromUTF8! value.parentMessageId.toByteArray ++ "\r\n" ++
    "Content-Type: application/vnd.dregg.fn-reply; version=2\r\n" ++
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
  NativeHostCodec.framed "DREGG/FN/REPLY-PREPARED/v2".toUTF8.toList
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
  NativeHostCodec.framed "DREGG/FN/REPLY-SIGNED/v2".toUTF8.toList
    signedStream

def Signed.valid (value : Signed) : Bool :=
  value.prepared.valid && value.sourceIdentity.length == 48 &&
  value.edSignature.length == 64 &&
  value.mlSignature.length == 3309 &&
  (signedCodec.encode value).length ≤ 12288

/-- Historical v1 sidecars decode into their old shape. In particular their
v2 Message-ID preimage and fixed Date are not assigned current v3 meaning. -/
structure HistoricalPrepared where
  selection : LegacySelection
  source : List UInt8
  messageId : List UInt8
  deriving DecidableEq, Repr

private def historicalPreparedStream : StreamCodec HistoricalPrepared :=
  StreamCodec.xmap
    (StreamCodec.product legacySelectionStream
      (StreamCodec.product bytesStream bytesStream))
    (fun value => (value.selection, value.source, value.messageId))
    (fun value => ⟨value.1, value.2.1, value.2.2⟩)
    (by intro value; cases value; rfl)

def historicalPreparedCodec : LawfulCodec HistoricalPrepared :=
  NativeHostCodec.framed "DREGG/FN/REPLY-PREPARED/v1".toUTF8.toList
    historicalPreparedStream

structure HistoricalSigned where
  prepared : HistoricalPrepared
  sourceIdentity : List UInt8
  edSignature : List UInt8
  mlSignature : List UInt8
  deriving DecidableEq, Repr

private def historicalSignedStream : StreamCodec HistoricalSigned :=
  StreamCodec.xmap
    (StreamCodec.product historicalPreparedStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream bytesStream)))
    (fun value => (value.prepared, value.sourceIdentity,
      value.edSignature, value.mlSignature))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩)
    (by intro value; cases value; rfl)

def historicalSignedCodec : LawfulCodec HistoricalSigned :=
  NativeHostCodec.framed "DREGG/FN/REPLY-SIGNED/v1".toUTF8.toList
    historicalSignedStream

end Minidregg.Kernel.FnReplyPublication
