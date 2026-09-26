/-
Pure selected-profile size/capacity probe for one prepared R outbox atom.
The full-size carrier is synthetic; this checks Mini's actual content page
materializer and codecs, not native fn authorship or receiving admission.
-/
import Kernel.FnOriginOutbox

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.FnOriginOutbox

set_option autoImplicit false

private def require (condition : Bool) (detail : String) : IO Unit := do
  unless condition do throw (IO.userError detail)

def originOutboxMaxProbe : IO Unit := do
  let domain : Digest := ⟨8501⟩
  let semantics : Digest := ⟨6⟩
  let receipt : NativeHostCodec.Receipt := ⟨⟨101⟩, ⟨102⟩, 2, ⟨103⟩⟩
  let package : FnEvidenceCodec.Package :=
    ⟨domain, semantics, ⟨104⟩, [1], receipt, [2]⟩
  let packageBytes ← IO.ofExcept (FnEvidenceCodec.encodeChecked package)
  let prepared : Prepared :=
    ⟨[17], FnConsumerOperation.originOperation package,
      "<r@x>".toUTF8.toList, List.replicate 48 3,
      List.replicate FnEvidenceCodec.maxCarrierBytes (4 : UInt8),
      packageIdentity packageBytes, callIdentity package.signedCall,
      receipt, List.replicate 32 5, List.replicate 32 6,
      List.replicate 1952 7⟩
  let report : Report :=
    ⟨prepared, packageBytes, ⟨7⟩, 600, ⟨61⟩, ⟨11⟩, ⟨12⟩, true, true⟩
  let pin : FnGatewayPolicy.Pin := ⟨[17], ⟨7⟩, 600, ⟨61⟩, ⟨99⟩⟩
  let policy : FnConsumerOperation.Policy := ⟨[17], ⟨7⟩, 600, ⟨61⟩⟩
  let .ok () := checkReport pin policy report
    | throw (IO.userError "maximal prepared R exceeded selected outbox profile")
  let command := outboxCommand domain semantics report
  let commandBytes := DeclaredResourceController.commandCodec.encode command
  let some decoded := DeclaredResourceController.commandCodec.decode commandBytes
    | throw (IO.userError "maximal outbox command did not strictly decode")
  require (FnConsumerOperation.exactSignedCommand commandBytes decoded)
    "maximal outbox command changed on strict decode"
  let some intent := (Decision.fresh command).intent report
    | throw (IO.userError "maximal outbox had no observation intent")
  let intentBytes := NativeObservationCodec.intentCodec.encode intent
  require (intentBytes.length ≤ FnEvidenceCodec.maxHostFrameBytes)
    "maximal outbox intent exceeded native host frame"
  let author : PrincipalRef := ⟨⟨7⟩, .object, ⟨61⟩⟩
  let operation : OperationId := ⟨⟨23⟩⟩
  let content : ContentResource.Command :=
    ⟨[.createAtom (outboxAtom domain semantics prepared) (.inlineObject ⟨10⟩)
      (preparedCodec.encode prepared)]⟩
  let .ok page := ContentResource.preparePage author operation
      (ContentResource.initialPage domain 600) content
    | throw (IO.userError "content page refused maximal prepared R atom")
  IO.println s!"PASS maximal prepared R outbox: atom={((preparedCodec.encode prepared).length)} command={commandBytes.length} intent={intentBytes.length} page={ContentResource.contentBytes page.post} frame={FnEvidenceCodec.maxHostFrameBytes}"

#eval originOutboxMaxProbe
