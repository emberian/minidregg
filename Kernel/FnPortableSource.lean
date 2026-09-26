/-
The first bounded E1 application body carried by an authenticated fn source.
This is Mini's own payload format, not a second implementation of fn's carrier
or authorship semantics. The caller must first obtain exact source octets from
fn's native hybrid verifier under an independently selected key pin.
-/
import Kernel.FnEvidence

namespace Minidregg.Kernel.FnPortableSource

set_option autoImplicit false

structure Extracted where
  messageId : String
  groups : String
  package : List UInt8
  deriving Repr

def digit (c : Char) : Option Nat :=
  let n := c.toNat
  if 65 ≤ n && n ≤ 90 then some (n - 65)
  else if 97 ≤ n && n ≤ 122 then some (n - 97 + 26)
  else if 48 ≤ n && n ≤ 57 then some (n - 48 + 52)
  else if n == 43 then some 62
  else if n == 47 then some 63
  else none

partial def decodeGroups (chars : List Char) (out : Array UInt8) : Option (Array UInt8) :=
  match chars with
  | [] => some out
  | a :: b :: c :: d :: rest => do
      let x ← digit a
      let y ← digit b
      let out := out.push (UInt8.ofNat (x * 4 + y / 16))
      if c == '=' then
        if d == '=' && rest.isEmpty && y % 16 == 0 then some out else none
      else
        let z ← digit c
        let out := out.push (UInt8.ofNat ((y % 16) * 16 + z / 4))
        if d == '=' then
          if rest.isEmpty && z % 4 == 0 then some out else none
        else
          let w ← digit d
          decodeGroups rest (out.push (UInt8.ofNat ((z % 4) * 64 + w)))
  | _ => none

def headerValue (label line : String) : Option String :=
  match line.splitOn label with
  | ["", value] => if value.isEmpty then none else some value
  | _ => none

/-- Strict one-part CRLF/base64 profile. Header order, MIME type, line widths,
alphabet and padding are checked before a package is returned. -/
def extract (source : List UInt8)
    (limits : Minidregg.Compiler.FnEvidenceCodec.Limits :=
      Minidregg.Compiler.FnEvidenceCodec.Limits.portable) : Except String Extracted := do
  unless limits.valid do throw "invalid operator evidence limits"
  unless source.length ≤ limits.sourceBytes && source.all (fun b => b.toNat < 128) do
    throw "fn authored source is oversized or non-ASCII for E1"
  let text := String.fromUTF8! source.toByteArray
  let (headers, body) ← match text.splitOn "\r\n\r\n" with
    | [headers, body] => pure (headers, body)
    | _ => throw "fn authored source has no unique header/body boundary"
  let (fromLine, date, groupsLine, subject, messageLine, contentType, transfer) ←
    match headers.splitOn "\r\n" with
    | [fromLine, date, groups, subject, message, contentType, transfer] =>
        pure (fromLine, date, groups, subject, message, contentType, transfer)
    | _ => throw "fn E1 source has unexpected header layout"
  unless (headerValue "From: " fromLine).isSome &&
      (headerValue "Date: " date).isSome &&
      (headerValue "Subject: " subject).isSome &&
      contentType == "Content-Type: application/vnd.dregg.fn-native-prefix; version=1" &&
      transfer == "Content-Transfer-Encoding: base64" do
    throw "fn E1 source has unsupported headers"
  let some groups := headerValue "Newsgroups: " groupsLine
    | throw "fn E1 source has no groups"
  let some messageId := headerValue "Message-ID: " messageLine
    | throw "fn E1 source has no Message-ID"
  unless groups.length ≤ 256 && messageId.length ≤ 256 do
    throw "fn E1 source metadata exceeds bound"
  let lines ← match (body.splitOn "\r\n").reverse with
    | "" :: rest => pure rest.reverse
    | _ => throw "fn E1 base64 body is not CRLF terminated"
  unless !lines.isEmpty && lines.length ≤ limits.sourceBytes / 76 + 1 &&
      lines.all (fun line => !line.isEmpty && line.length ≤ 76) &&
      (lines.reverse.drop 1).all (fun line => line.length == 76) do
    throw "fn E1 base64 line width exceeds profile"
  let base64 := String.intercalate "" lines
  let some bytes := decodeGroups base64.toList #[]
    | throw "fn E1 base64 body is noncanonical"
  unless bytes.size ≤ limits.packageBytes do
    throw "fn E1 package exceeds native prefix bound"
  pure ⟨messageId, groups, bytes.toList⟩

end Minidregg.Kernel.FnPortableSource
