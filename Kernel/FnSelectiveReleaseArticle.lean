/-
Strict public fn application source for one selected owner-signed release.
The caller must first obtain these exact authored source bytes from fn's
bounded native Store projection; this module does not accept an fn assertion
as owner authority. Its body carries only the selected packet, never a Mini
genesis or accepted-history prefix. Native release admission separately
checks the owner signature, current recipient law, capability and nonce.
-/
import Kernel.FnSelectiveReleaseSignature
import Kernel.FnPortableSource

namespace Minidregg.Kernel.FnSelectiveReleaseArticle

open Minidregg.Compiler
open Minidregg.Kernel.FnSelectiveRelease
open Minidregg.Kernel.FnSelectiveReleaseSignature

set_option autoImplicit false

structure Article where
  fromMailbox : String
  date : String
  subject : String
  packet : Packet
  deriving DecidableEq, Repr

private def cleanHeader (value : String) (limit : Nat) : Bool :=
  !value.isEmpty && value.length ≤ limit &&
    value.toUTF8.toList.all (fun byte => 32 ≤ byte.toNat && byte.toNat ≤ 126)

private def cleanGroup (value : String) : Bool :=
  cleanHeader value 256 && value.toList.all (fun c =>
    c.isAlphanum || c == '.' || c == '-' || c == '_')

private def cleanMessageId (value : String) : Bool :=
  -- Match the native Q source profile; the recipient still compares the
  -- complete header byte-for-byte with the owner-signed destination.
  value.length ≥ 3 && value.length ≤ 256 &&
    value.startsWith "<" && value.endsWith ">" &&
    value.toUTF8.toList.all (fun byte => 33 ≤ byte.toNat && byte.toNat ≤ 126)

def Article.render (article : Article) : Except String (List UInt8) := do
  let release := article.packet.release
  unless article.packet.signature.length == 64 do
    throw "selected release has invalid owner signature length"
  unless release.bounded && release.destination.audience.visibility == .publicPeerable do
    throw "selected release is unbounded or not public-peerable"
  unless release.destination.group.all (fun b => b.toNat < 128) &&
      release.destination.messageId.all (fun b => b.toNat < 128) do
    throw "signed routing metadata is non-ASCII"
  let group := String.fromUTF8! release.destination.group.toByteArray
  let messageId := String.fromUTF8! release.destination.messageId.toByteArray
  unless cleanHeader article.fromMailbox 254 && cleanHeader article.date 128 &&
      cleanHeader article.subject 256 && cleanGroup group &&
      cleanMessageId messageId do
    throw "selected release has invalid article headers"
  let packetBytes := packetCodec.encode article.packet
  let source := ("From: " ++ article.fromMailbox ++ "\r\n" ++
    "Date: " ++ article.date ++ "\r\n" ++
    "Newsgroups: " ++ group ++ "\r\n" ++
    "Subject: " ++ article.subject ++ "\r\n" ++
    "Message-ID: " ++ messageId ++ "\r\n" ++
    "Content-Type: application/vnd.dregg.selective-release; version=2\r\n" ++
    "Content-Transfer-Encoding: base64\r\n\r\n" ++
    Base64.encodeLines packetBytes).toUTF8.toList
  unless source.length ≤ FnEvidenceCodec.maxSourceBytes do
    throw "selected release article exceeds source profile"
  pure source

def extract (source : List UInt8) : Except String Article := do
  unless source.length ≤ FnEvidenceCodec.maxSourceBytes &&
      source.all (fun byte => byte.toNat < 128) do
    throw "selected release source is oversized or non-ASCII"
  let text := String.fromUTF8! source.toByteArray
  let (headers, body) ← match text.splitOn "\r\n\r\n" with
    | [headers, body] => pure (headers, body)
    | _ => throw "selected release has no unique header/body boundary"
  let (fromLine, dateLine, groupLine, subjectLine, messageLine) ←
    match headers.splitOn "\r\n" with
    | [fromLine, dateLine, groupLine, subjectLine, messageLine,
       "Content-Type: application/vnd.dregg.selective-release; version=2",
       "Content-Transfer-Encoding: base64"] =>
        pure (fromLine, dateLine, groupLine, subjectLine, messageLine)
    | _ => throw "selected release has unsupported or duplicate headers"
  let some fromMailbox := FnPortableSource.headerValue "From: " fromLine
    | throw "selected release lacks From"
  let some date := FnPortableSource.headerValue "Date: " dateLine
    | throw "selected release lacks Date"
  let some group := FnPortableSource.headerValue "Newsgroups: " groupLine
    | throw "selected release lacks Newsgroups"
  let some subject := FnPortableSource.headerValue "Subject: " subjectLine
    | throw "selected release lacks Subject"
  let some messageId := FnPortableSource.headerValue "Message-ID: " messageLine
    | throw "selected release lacks Message-ID"
  let lines ← match (body.splitOn "\r\n").reverse with
    | "" :: rest => pure rest.reverse
    | _ => throw "selected release base64 body is not CRLF terminated"
  unless !lines.isEmpty && lines.length ≤ FnEvidenceCodec.maxSourceBytes / 76 + 1 &&
      lines.all (fun line => !line.isEmpty && line.length ≤ 76) &&
      (lines.reverse.drop 1).all (fun line => line.length == 76) do
    throw "selected release base64 line width exceeds profile"
  let some bytes := Base64.decode (String.intercalate "" lines).toUTF8.toList
    | throw "selected release base64 body is noncanonical"
  unless bytes.length ≤ FnEvidenceCodec.maxCarrierBytes + 8192 do
    throw "selected release packet exceeds bound"
  let some packet := packetCodec.decode bytes
    | throw "selected release packet is noncanonical"
  let article : Article := ⟨fromMailbox, date, subject, packet⟩
  unless packet.release.destination.group == group.toUTF8.toList &&
      packet.release.destination.messageId == messageId.toUTF8.toList do
    throw "fn routing headers differ from owner-signed release"
  unless (← article.render) == source do
    throw "selected release differs from canonical article rendering"
  pure article

end Minidregg.Kernel.FnSelectiveReleaseArticle
