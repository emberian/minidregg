/-
Source-owned fn R article for an already verified Mini AgentGrain publication.

The receiving host must first call `FnEvidence.verify` against its independently
pinned origin configuration and pass the returned receipt here. This module is
pure: it rechecks the bounded package and exact receipt, classifies the signed
grain/parent/publication command, and renders only Mini's strict application
source. fn retains hybrid signing, article admission, peering and identity.
Other Mini origin shapes have no constructor in this renderer.
-/
import Kernel.FnPortableSource
import Kernel.AgentGrain
import Compiler.ResourceBirthCodec

namespace Minidregg.Host.GrainOriginSource

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel
open Minidregg.Theory.DeclaredActionLowering

set_option autoImplicit false

structure ArticleContext where
  fromMailbox : String
  group : String
  date : String
  subject : String
  messageIdDomain : String
  deriving DecidableEq, Repr

/-- Existing real-R script bytes for the same group, date and package. -/
def ArticleContext.application (group date : String) : ArticleContext :=
  ⟨"mini-grain@example.invalid", group, date,
    "Mini AgentGrain publication", "mini.invalid"⟩

private def cleanHeader (value : String) (max : Nat) : Bool :=
  !value.isEmpty && value.length ≤ max && value.toUTF8.data.toList.all
    (fun b => 32 ≤ b.toNat && b.toNat ≤ 126)

private def cleanGroup (value : String) : Bool :=
  cleanHeader value 128 && value.toList.all (fun c =>
    c.isAlphanum || c == '.' || c == '-' || c == '_')

private def cleanDomain (value : String) : Bool :=
  cleanHeader value 253 && value.toList.contains '.' &&
    value.toList.all (fun c => c.isAlphanum || c == '.' || c == '-')

def ArticleContext.valid (context : ArticleContext) : Bool :=
  cleanHeader context.fromMailbox 254 && cleanGroup context.group &&
    cleanHeader context.date 128 && cleanHeader context.subject 256 &&
    cleanDomain context.messageIdDomain

private def alphabet : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

private def base64Line (bytes : ByteArray) (start stop : Nat) : String := Id.run do
  let mut chars : Array Char := #[]
  let mut i := start
  while i < stop do
    let a := bytes[i]!.toNat
    let b := if i + 1 < stop then bytes[i + 1]!.toNat else 0
    let c := if i + 2 < stop then bytes[i + 2]!.toNat else 0
    chars := chars.push alphabet[a / 4]!
    chars := chars.push alphabet[(a % 4) * 16 + b / 16]!
    chars := chars.push (if i + 1 < stop then alphabet[(b % 16) * 4 + c / 64]! else '=')
    chars := chars.push (if i + 2 < stop then alphabet[c % 64]! else '=')
    i := i + 3
  return String.ofList chars.toList

private def base64Lines (bytes : ByteArray) : String := Id.run do
  let mut lines : Array String := #[]
  let mut i := 0
  while i < bytes.size do
    let stop := min bytes.size (i + 57)
    lines := lines.push (base64Line bytes i stop)
    i := stop
  return String.intercalate "\r\n" lines.toList ++ "\r\n"

private def writePair (task field : Nat) : Action → Option (Int × Int)
  | .write (.objectField resource fieldId) (some before) after =>
      if resource.value == task && fieldId.value == field then some (before, after) else none
  | _ => none

private def grainStates (task : Nat) (actions : List Action) :
    Option (AgentGrain.State × AgentGrain.State) := do
  let [a, b, c, d] := actions | none
  let p0 ← writePair task 0 a
  let p1 ← writePair task 1 b
  let p2 ← writePair task 2 c
  let p3 ← writePair task 3 d
  return (⟨p0.1, p1.1, p2.1, p3.1⟩, ⟨p0.2, p1.2, p2.2, p3.2⟩)

structure Selection where
  grainTask : Nat
  parentTask : Nat
  publicationTarget : Nat
  deriving DecidableEq, Repr

def Selection.valid (selection : Selection) : Bool :=
  selection.grainTask != selection.parentTask &&
    selection.grainTask != selection.publicationTarget &&
    selection.parentTask != selection.publicationTarget

structure Rendered where
  private mk ::
  context : ArticleContext
  selection : Selection
  packageBytes : List UInt8
  receipt : Receipt
  signedTargets : List Nat
  messageId : String
  source : List UInt8
  extracted : FnPortableSource.Extracted
  sourceExact : FnPortableSource.extract source = .ok extracted
  packageExact : extracted.package = packageBytes
  messageIdExact : extracted.messageId = messageId
  groupExact : extracted.groups = context.group

/-- The returned bytes are accepted by the same strict Mini application
parser and contain the complete original package, with no normalization. -/
theorem Rendered.strict_source (rendered : Rendered) :
    FnPortableSource.extract rendered.source = .ok rendered.extracted ∧
      rendered.extracted.package = rendered.packageBytes ∧
      rendered.extracted.messageId = rendered.messageId ∧
      rendered.extracted.groups = rendered.context.group :=
  ⟨rendered.sourceExact, rendered.packageExact,
    rendered.messageIdExact, rendered.groupExact⟩

/-- The receipt argument must be the result of the independent native
`FnEvidence.verify` call, not a value read from the package alone. That IO
provenance is the caller's boundary; this pure function checks its exact
agreement with the decoded package and source classification. -/
def render (packageBytes : List UInt8) (verifiedReceipt : Receipt)
    (context : ArticleContext) (selection : Selection) : Except String Rendered := do
  unless selection.valid do
    throw "grain, parent, and publication targets must be distinct"
  unless context.valid do
    throw "origin article context is outside the single-group source profile"
  let package ← FnEvidenceCodec.decodeChecked packageBytes
  unless verifiedReceipt == package.originalReceipt do
    throw "independent Mini receipt differs from original package receipt"
  let some (.invoke signed) := callCodec.decode package.signedCall
    | throw "origin evidence is not an ordinary signed resource invocation"
  let some command := DeclaredResourceController.commandCodec.decode signed.commandBytes
    | throw "origin signed command is noncanonical"
  let grainTarget :: witness :: publications := command.targets
    | throw "origin command has no grain, parent witness, and publication legs"
  unless grainTarget.kind == .object && grainTarget.target == selection.grainTask do
    throw "original call does not lead with the named grain task"
  let .scalar grainActions := grainTarget.payload
    | throw "origin grain leg is not scalar"
  let some (grainBefore, grainAfter) := grainStates selection.grainTask grainActions
    | throw "origin grain leg is not the four-coordinate AgentGrain shape"
  let charge := grainBefore.remaining + grainBefore.reserved - grainAfter.remaining
  unless (grainBefore.status == 3 || grainBefore.status == 4) &&
      decide (0 ≤ charge) && decide (charge ≤ grainBefore.reserved) &&
      decide (grainAfter = AgentGrain.settle grainBefore charge) &&
      AgentGrain.accepts grainBefore grainAfter do
    throw "origin grain leg is not an admitted reserved-to-settled transition"
  unless witness.kind == .object && witness.target == selection.parentTask do
    throw "origin call has no named parent witness in its second leg"
  let .scalar witnessActions := witness.payload
    | throw "origin parent witness is not scalar"
  let some (parentBefore, parentAfter) := grainStates selection.parentTask witnessActions
    | throw "origin parent witness is not the four-coordinate shape"
  unless decide (parentBefore = parentAfter) &&
      (parentBefore.status == 3 || parentBefore.status == 4) do
    throw "origin parent witness did not preserve a reserved prompt"
  unless publications.any (fun target => target.kind == .object &&
      target.target == selection.publicationTarget &&
      match target.payload with
      | .scalar actions => !actions.isEmpty
      | .content content => !content.actions.isEmpty) do
    throw "original call has no authored publication to the named resource"
  let messageId :=
    s!"<mini-grain-{verifiedReceipt.transactionId.value}-{verifiedReceipt.eventId.value}@{context.messageIdDomain}>"
  unless messageId.length ≤ 256 do
    throw "derived Message-ID exceeds Mini source profile"
  let source := ("From: " ++ context.fromMailbox ++ "\r\n" ++
    "Date: " ++ context.date ++ "\r\n" ++
    "Newsgroups: " ++ context.group ++ "\r\n" ++
    "Subject: " ++ context.subject ++ "\r\n" ++
    "Message-ID: " ++ messageId ++ "\r\n" ++
    "Content-Type: application/vnd.dregg.fn-native-prefix; version=1\r\n" ++
    "Content-Transfer-Encoding: base64\r\n\r\n" ++
    base64Lines packageBytes.toByteArray).toUTF8.toList
  match parsed : FnPortableSource.extract source with
  | .error detail => throw s!"authored fn source fails Mini's strict source parser: {detail}"
  | .ok extracted =>
      if packageExact : ResourceBirthCodec.bytesEqual extracted.package packageBytes then
        if messageExact : extracted.messageId = messageId then
          if groupExact : extracted.groups = context.group then
            have exactBytes : extracted.package = packageBytes :=
              (ResourceBirthCodec.bytesEqual_eq_true_iff extracted.package packageBytes).mp packageExact
            return ⟨context, selection, packageBytes, verifiedReceipt,
              command.targets.map (·.target), messageId, source, extracted,
              parsed, exactBytes, messageExact, groupExact⟩
          else throw "authored source group differs from operator context"
        else throw "authored source Message-ID differs from accepted receipt"
      else throw "authored source package differs from exact Mini evidence"

end Minidregg.Host.GrainOriginSource
