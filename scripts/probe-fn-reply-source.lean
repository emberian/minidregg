import Kernel.FnReplyPublication

open Minidregg.Kernel.FnConsumerOperation
open Minidregg.Kernel.FnReplyPublication

def require (ok : Bool) (detail : String) : IO Unit :=
  unless ok do throw (IO.userError detail)

def main (args : List String) : IO Unit := do
  let [replyPath] := args
    | throw (IO.userError "usage: lean --run scripts/probe-fn-reply-source.lean REPLY.bin")
  let replyBytes := (← IO.FS.readBinFile replyPath).toList
  let some reply := replyCodec.decode replyBytes
    | throw (IO.userError "Q is not a canonical Mini reply")
  let selected : Selection :=
    { domain := ⟨8501⟩, semantics := ⟨1⟩,
      miniTransaction := ⟨101⟩, miniEvent := ⟨102⟩,
      reply := reply, parentSourceIdentity := reply.sourceIdentity,
      parentMessageId := "<parent@example.invalid>".toUTF8.toList,
      principal := List.replicate 32 0,
      edPublicKey := List.replicate 32 1,
      mlPublicKey := List.replicate 1952 2 }
  let source ← IO.ofExcept selected.source
  let prepared ← IO.ofExcept selected.prepare
  let encoded := preparedCodec.encode prepared
  require (preparedCodec.decode encoded == some prepared)
    "prepared codec did not round trip"
  require prepared.valid "prepared source did not validate"
  require (!(Prepared.valid { prepared with messageId := "<other@example.invalid>".toUTF8.toList }))
    "different staged Message-ID validated"
  require (!(Prepared.valid { prepared with source := [1, 2, 3] }))
    "different staged source validated"
  let signed : Signed := ⟨prepared, reply.sourceIdentity, List.replicate 64 3,
    List.replicate 3309 4⟩
  require signed.valid "bounded signed artifact did not validate"
  require (signedCodec.decode (signedCodec.encode signed) == some signed)
    "signed artifact codec did not round trip"
  require (!(Signed.valid { signed with edSignature := [3] }))
    "short Ed25519 signature validated"
  require (!(Signed.valid { signed with mlSignature := [4] }))
    "short ML-DSA signature validated"
  require (source == (← IO.ofExcept selected.source)) "source changed on repeat"
  let text := String.fromUTF8! source.toByteArray
  require ((text.splitOn "Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n").length == 2)
    "source lacks the fixed signed Date required by fn's portable profile"
  require ((text.splitOn ("Message-ID: " ++ selected.messageId ++ "\r\n")).length == 2)
    "source lacks its selected Message-ID"
  require (text.endsWith (hexBytes replyBytes ++ "\r\n"))
    "source does not carry exact canonical Q bytes"
  let changed : Selection := { selected with miniEvent := ⟨103⟩ }
  require (changed.messageId != selected.messageId)
    "different accepted Mini event reused reply Message-ID"
  let injected : Selection := { selected with
    parentMessageId := "<parent@example.invalid>\r\nX-Evil: yes".toUTF8.toList }
  require (match injected.source with | .error _ => true | .ok _ => false)
    "parent Message-ID injected a header"
  IO.println s!"PASS fn reply source: {source.length} bytes, {selected.messageId}"
