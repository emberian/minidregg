/-
Strict application parser for the bounded synthetic Q source. Fn native first
verifies the exact authored source and historical Store verdict; this module
only interprets Mini's application body and correlation fields. It does not
parse or decide NNTP/Store authority.
-/
import Kernel.FnReplyPublication
import Kernel.FnPortableSource

namespace Minidregg.Kernel.FnReplySource

open Minidregg.Kernel.FnConsumerOperation

set_option autoImplicit false

structure Extracted where
  messageId : String
  parentMessageId : String
  reply : Reply
  creation : Minidregg.Kernel.FnReplyPublication.CreationContext
  version : Nat
  deriving DecidableEq, Repr

def Extracted.render (value : Extracted) : List UInt8 :=
  let contentType := if value.version == 1 then
    "Content-Type: application/vnd.dregg.fn-reply; version=1"
    else "Content-Type: application/vnd.dregg.fn-reply; version=2"
  ("From: " ++ value.creation.fromMailbox ++ "\r\n" ++
   "Date: " ++ value.creation.date ++ "\r\n" ++
   "Newsgroups: " ++ value.creation.newsgroup ++ "\r\n" ++
   "Subject: Mini E2 reply\r\n" ++
   "Message-ID: " ++ value.messageId ++ "\r\n" ++
   "In-Reply-To: " ++ value.parentMessageId ++ "\r\n" ++
   contentType ++ "\r\n\r\n" ++
   Minidregg.Kernel.FnReplyPublication.hexBytes (replyCodec.encode value.reply) ++
   "\r\n").toUTF8.toList

private def hexDigit (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 97 ≤ n && n ≤ 102 then some (n - 97 + 10)
  else none

private def hexOctets : List Char → Option (List UInt8)
  | [] => some []
  | first :: second :: rest => do
      let hi ← hexDigit first
      let lo ← hexDigit second
      let tail ← hexOctets rest
      some (UInt8.ofNat (hi * 16 + lo) :: tail)
  | _ => none

private def messageIdValid (value : String) : Bool :=
  value.length ≥ 3 && value.length ≤ 256 &&
  value.startsWith "<" && value.endsWith ">" &&
  value.toUTF8.toList.all (fun b => 33 ≤ b.toNat && b.toNat ≤ 126)

/-- Parse the historical synthetic profile and the current contextual profile.
The version is part of the exact signed source, so an old source is never
reinterpreted under the new creation policy. -/
private def parseRaw (source : List UInt8) : Except String Extracted := do
  unless source.length ≤ 32768 && source.all (fun b => b.toNat < 128) do
    throw "Q source is oversized or non-ASCII"
  let text := String.fromUTF8! source.toByteArray
  let (headers, body) ← match text.splitOn "\r\n\r\n" with
    | [headers, body] => pure (headers, body)
    | _ => throw "Q source has no unique header/body boundary"
  let (messageLine, parentLine, creation, version) ← match headers.splitOn "\r\n" with
    | ["From: mini-e2@example.invalid",
       "Date: Wed, 23 Sep 2026 12:00:00 +0000",
       "Newsgroups: fn.test",
       "Subject: Mini E2 reply", messageLine, parentLine,
       "Content-Type: application/vnd.dregg.fn-reply; version=1"] =>
        pure (messageLine, parentLine,
          Minidregg.Kernel.FnReplyPublication.CreationContext.synthetic, 1)
    | [fromLine, dateLine, groupLine,
       "Subject: Mini E2 reply", messageLine, parentLine,
       "Content-Type: application/vnd.dregg.fn-reply; version=2"] => do
        let some fromMailbox := Minidregg.Kernel.FnPortableSource.headerValue
          "From: " fromLine | throw "Q source lacks From"
        let some date := Minidregg.Kernel.FnPortableSource.headerValue
          "Date: " dateLine | throw "Q source lacks Date"
        let some newsgroup := Minidregg.Kernel.FnPortableSource.headerValue
          "Newsgroups: " groupLine | throw "Q source lacks Newsgroups"
        let some messageId := Minidregg.Kernel.FnPortableSource.headerValue
          "Message-ID: " messageLine | throw "Q source lacks Message-ID"
        let domain := match (messageId.dropEnd 1).toString.splitOn "@" with
          | [_, domain] => domain
          | _ => ""
        let creation : Minidregg.Kernel.FnReplyPublication.CreationContext :=
          ⟨fromMailbox, newsgroup, domain, date⟩
        unless creation.valid do throw "Q source has invalid creation metadata"
        pure (messageLine, parentLine, creation, 2)
    | _ => throw "Q source has unsupported experiment headers"
  let some messageId := Minidregg.Kernel.FnPortableSource.headerValue
      "Message-ID: " messageLine
    | throw "Q source lacks Message-ID"
  let some parentMessageId := Minidregg.Kernel.FnPortableSource.headerValue
      "In-Reply-To: " parentLine
    | throw "Q source lacks parent Message-ID"
  let suffix := "@" ++ creation.messageIdDomain ++ ">"
  unless messageIdValid messageId && messageId.startsWith "<mini-e2-" &&
      messageId.endsWith suffix && messageId.length > 9 + suffix.length do
    throw "Q source has invalid Message-ID fields"
  let digestChars := (messageId.toList.drop 9).take
    (messageId.length - 9 - suffix.length)
  let some digestBytes := hexOctets digestChars
    | throw "Q source has invalid Message-ID digest hexadecimal"
  let some digest := Minidregg.Compiler.Tower256ConcreteBackend.digestStream.toLawful.decode digestBytes
    | throw "Q source has invalid Message-ID digest encoding"
  unless !digestBytes.isEmpty &&
      Minidregg.Compiler.Tower256ConcreteBackend.digestStream.encode digest == digestBytes &&
      messageId == "<mini-e2-" ++ String.ofList digestChars ++ suffix &&
      messageIdValid parentMessageId &&
      (version != 1 || parentMessageId.startsWith "<mini-e1-") do
    throw "Q source has invalid Message-ID fields"
  let [hex, ""] := body.splitOn "\r\n"
    | throw "Q body is not one CRLF-terminated hexadecimal line"
  unless !hex.isEmpty && hex.length ≤ 800 do
    throw "Q body exceeds the bounded reply profile"
  let some bytes := hexOctets hex.toList
    | throw "Q body is not canonical lowercase hexadecimal"
  let some reply := replyCodec.decode bytes
    | throw "Q body is not a canonical Mini reply"
  unless replyCodec.encode reply == bytes do
    throw "Q body differs from the canonical reply codec"
  pure ⟨messageId, parentMessageId, reply, creation, version⟩

def extract (source : List UInt8) : Except String Extracted :=
  match parseRaw source with
  | .error err => .error err
  | .ok parsed =>
      if parsed.render == source then .ok parsed
      else .error "Q source differs from canonical application rendering"

/-- Every accepted application parse names the exact source octets supplied
to the fn verifier, including creation metadata and the canonical Q bytes. -/
theorem extract_exact {source : List UInt8} {parsed : Extracted}
    (h : extract source = .ok parsed) : parsed.render = source := by
  unfold extract at h
  cases hraw : parseRaw source with
  | error err => simp [hraw] at h
  | ok value =>
      simp only [hraw] at h
      split at h
      · cases h; simp_all
      · simp at h

end Minidregg.Kernel.FnReplySource
