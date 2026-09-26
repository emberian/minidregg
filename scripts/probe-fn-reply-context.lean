import Kernel.FnReplySource

open Minidregg.Kernel.FnConsumerOperation
open Minidregg.Kernel.FnReplyPublication
open Minidregg.Kernel.FnReplySource
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main : IO Unit := do
  let reply : Reply :=
    ⟨"application".toUTF8.toList, "operation".toUTF8.toList,
      List.replicate 48 7, ⟨⟨101⟩, ⟨102⟩, 1, ⟨103⟩⟩⟩
  let creation : CreationContext :=
    ⟨"agent@demo.example", "fn.demo", "demo.example",
      "Sat, 26 Sep 2026 12:34:56 +0000"⟩
  let selected : Selection :=
    { domain := ⟨8501⟩, semantics := ⟨1⟩,
      miniTransaction := ⟨101⟩, miniEvent := ⟨102⟩,
      reply := reply, parentSourceIdentity := reply.sourceIdentity,
      parentMessageId := "<mini-e1-parent@demo.example>".toUTF8.toList,
      principal := List.replicate 32 0, edPublicKey := List.replicate 32 1,
      mlPublicKey := List.replicate 1952 2, creation := creation }
  let prepared ← IO.ofExcept selected.prepare
  let parsed ← IO.ofExcept (extract prepared.source)
  require (parsed.creation == creation && parsed.reply == reply &&
    parsed.messageId == selected.messageId && parsed.version == 2 &&
    parsed.render == prepared.source) "contextual reply source did not parse exactly"
  require (preparedCodec.decode (preparedCodec.encode prepared) == some prepared)
    "contextual prepared record did not round trip"
  require (prepared.valid &&
    !(Prepared.valid { prepared with source := [0] }))
    "prepared source binding failed"
  let other : Selection := { selected with creation := { creation with newsgroup := "fn.other" } }
  require (other.messageId != selected.messageId)
    "creation context did not change Message-ID"
  let injected : Selection := { selected with
    creation := { creation with fromMailbox := "agent@demo.example\r\nX-Evil: yes" } }
  require (match injected.source with | .error _ => true | .ok _ => false)
    "header injection was accepted"
  let historicalArticle (digestHex : String) :=
    "From: mini-e2@example.invalid\r\n" ++
    "Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n" ++
    "Newsgroups: fn.test\r\nSubject: Mini E2 reply\r\n" ++
    "Message-ID: <mini-e2-" ++ digestHex ++ "@example.invalid>\r\n" ++
    "In-Reply-To: <mini-e1-parent@example.invalid>\r\n" ++
    "Content-Type: application/vnd.dregg.fn-reply; version=1\r\n\r\n" ++
    hexBytes (replyCodec.encode reply) ++ "\r\n"
  let longDigest := hexBytes (digestStream.encode ⟨2 ^ 256 - 1⟩)
  let shortDigest := hexBytes (digestStream.encode ⟨2 ^ 240⟩)
  require (longDigest.length == 68 && shortDigest.length == 64)
    "digest length fixtures no longer cover variable encodings"
  let historical := historicalArticle longDigest
  let historicalId := "<mini-e2-" ++ longDigest ++ "@example.invalid>"
  let oldParsed ← IO.ofExcept (extract historical.toUTF8.toList)
  require (oldParsed.version == 1 && oldParsed.creation == CreationContext.synthetic &&
    oldParsed.render == historical.toUTF8.toList)
    "historical synthetic source did not retain old meaning"
  let shorter := historicalArticle shortDigest
  let shortParsed ← IO.ofExcept (extract shorter.toUTF8.toList)
  require (shortParsed.messageId == "<mini-e2-" ++ shortDigest ++
    "@example.invalid>" && shortParsed.render == shorter.toUTF8.toList)
    "shorter canonical digest Message-ID did not parse"
  let oldSelection : LegacySelection :=
    ⟨selected.domain, selected.semantics, selected.miniTransaction,
      selected.miniEvent, reply, reply.sourceIdentity,
      "<mini-e1-parent@example.invalid>".toUTF8.toList,
      selected.principal, selected.edPublicKey, selected.mlPublicKey⟩
  let oldPrepared : HistoricalPrepared :=
    ⟨oldSelection, historical.toUTF8.toList, historicalId.toUTF8.toList⟩
  require (historicalPreparedCodec.decode (historicalPreparedCodec.encode oldPrepared) ==
    some oldPrepared) "historical prepared codec did not round trip"
  require (preparedCodec.decode (historicalPreparedCodec.encode oldPrepared) == none)
    "historical prepared bytes were reinterpreted as current profile"
  IO.println "PASS contextual and historical fn reply source"
