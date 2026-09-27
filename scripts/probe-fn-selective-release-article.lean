import Kernel.FnSelectiveReleaseArticle

open Minidregg.Kernel.FnSelectiveRelease
open Minidregg.Kernel.FnSelectiveReleaseSignature
open Minidregg.Kernel.FnSelectiveReleaseArticle

private def sample : Article :=
  { fromMailbox := "owner@example.invalid"
    date := "Sun, 27 Sep 2026 12:00:00 +0000"
    subject := "Selected public note"
    packet :=
      { release :=
          { source := ⟨⟨1⟩, ⟨2⟩, 8001, ⟨3⟩⟩
            destination :=
              ⟨⟨4⟩, ⟨5⟩, 600, "fn.test".toUTF8.toList,
                "<selected-1@mini.invalid>".toUTF8.toList,
                ⟨.publicPeerable, ⟨6⟩, ⟨7⟩, 1⟩⟩
            owner := ⟨⟨6⟩, 8, 1, ⟨9⟩, 100⟩
            content := "one selected version".toUTF8.toList }
        signature := List.replicate 64 (UInt8.ofNat 17) } }

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def refused {α : Type} (result : Except String α) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

def main : IO Unit := do
  let source ← match sample.render with
    | .ok bytes => pure bytes
    | .error reason => throw (IO.userError s!"render: {reason}")
  let recovered ← match extract source with
    | .ok article => pure article
    | .error reason => throw (IO.userError s!"extract: {reason}")
  require (recovered == sample) "selected article roundtrip changed packet"
  let text := String.fromUTF8! source.toByteArray
  let duplicate := text.replace "Date: Sun, 27 Sep 2026 12:00:00 +0000\r\n"
    "Date: Sun, 27 Sep 2026 12:00:00 +0000\r\nDate: duplicate\r\n"
  require (refused (extract duplicate.toUTF8.toList))
    "duplicate Date was accepted"
  let rerouted := text.replace "Message-ID: <selected-1@mini.invalid>"
    "Message-ID: <selected-2@mini.invalid>"
  require (refused (extract rerouted.toUTF8.toList))
    "header different from owner-signed destination was accepted"
  let badPacket : Packet :=
    { sample.packet with signature := List.replicate 65 (UInt8.ofNat 17) }
  let badSignature : Article := { sample with packet := badPacket }
  require (refused badSignature.render)
    "oversized owner signature reached packet encoding"
  IO.println "selected article roundtrip, duplicate, routing mismatch, signature bound PASS"
