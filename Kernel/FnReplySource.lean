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
  deriving DecidableEq, Repr

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

/-- The fixed Date is the explicit experiment profile, not a production
creation-time policy. A different source profile needs a new version. -/
def extract (source : List UInt8) : Except String Extracted := do
  unless source.length ≤ 32768 && source.all (fun b => b.toNat < 128) do
    throw "Q source is oversized or non-ASCII"
  let text := String.fromUTF8! source.toByteArray
  let (headers, body) ← match text.splitOn "\r\n\r\n" with
    | [headers, body] => pure (headers, body)
    | _ => throw "Q source has no unique header/body boundary"
  let (messageLine, parentLine) ← match headers.splitOn "\r\n" with
    | ["From: mini-e2@example.invalid",
       "Date: Wed, 23 Sep 2026 12:00:00 +0000",
       "Newsgroups: fn.test",
       "Subject: Mini E2 reply", messageLine, parentLine,
       "Content-Type: application/vnd.dregg.fn-reply; version=1"] =>
        pure (messageLine, parentLine)
    | _ => throw "Q source has unsupported experiment headers"
  let some messageId := Minidregg.Kernel.FnPortableSource.headerValue
      "Message-ID: " messageLine
    | throw "Q source lacks Message-ID"
  let some parentMessageId := Minidregg.Kernel.FnPortableSource.headerValue
      "In-Reply-To: " parentLine
    | throw "Q source lacks parent Message-ID"
  unless messageIdValid messageId && messageId.startsWith "<mini-e2-" &&
      messageId.endsWith "@example.invalid>" &&
      messageId.length == 92 &&
      ((messageId.toList.drop 9).take 66).all
        (fun c => (hexDigit c).isSome) &&
      messageIdValid parentMessageId &&
      parentMessageId.startsWith "<mini-e1-" do
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
  pure ⟨messageId, parentMessageId, reply⟩

end Minidregg.Kernel.FnReplySource
