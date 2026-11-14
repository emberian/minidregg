/-
# `Assurance/MemberPatchPoles.lean` — the member patch rule, executed

`Effect.memberPatch` (`Kernel/ResourceEffect.lean`) is the one rule of what thin consent shows
for a registered operation: its declaration states a member patch and the operation pins its
root. The poles, on the deployed declarations:

* *shown*: the two root-pinning reads (codes 3 and 7) state the empty patch and are shown it;
* *by name*: the content write (code 1) and the cited read (code 9) state none and are refused
  `unstated` (the cited read commutes and is displayed without a view; it never asks);
* *the root*: a ghost of the content read that commutes, stating the same member patch, is
  refused `commutes`: a member patch alone does not make an operation displayable;
* *a registered write*: the kind definition revision (code 5) on a kind with a field, revised to
  add one. The receiver computes it, the member patch answers one write, and that patch run on
  the loaded store is the receiver's post, which holds the signed definition. A revision that
  skips a number is refused by both: the receiver by the declaration's name (`notNextRevision`),
  the member patch as not applying (`patchRefused`). Under an account role the receiver refuses
  `wrongRole` while the member patch still answers: shown, then refused, nothing commits.
* *a registered write whose fields are inside its cell*: world actions (code 4) on a poll
  instance. A vote is computed and shown; the shown patch run is the receiver's post; a write
  whose guard does not hold is refused by both sides by name; the footprint is the inner field
  (the declaration's `footprint`), and an empty action list authors nothing.
* *the wire and the faces*: the payload's bytes are the tag octet 5 and the definition's
  canonical bytes, as the hand arm wrote them; the inbox JSON is `kind`, `revision`,
  `exactDefinitionHex`; the refusal prints under the declaration's name.
-/
import Kernel.MemberPatchPoles
import Kernel.ResourcePayloadJson

namespace Minidregg.Assurance.MemberPatchPoles
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Effects
open Minidregg.Theory.TypedAuthorization

def signer : MemberCtx := ⟨⟨7⟩, 3, .object, 41, ⟨5⟩⟩

/-- How a member patch answered: the length of the shown patch, or the refusal. -/
def answer {e : Effect} (shown : Except Effect.MemberRefusal (Minidregg.Theory.Store.Patch e.L)) :
    Except Effect.MemberRefusal Nat := shown.map List.length

instance : BEq (Except Effect.MemberRefusal Nat) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => decide (a = b)
    | _, _ => false

#guard answer ((effectAt 3).memberPatch signer () 0) == .ok 0
#guard answer ((effectAt 7).memberPatch signer () 0) == .ok 0
#guard answer ((effectAt 9).memberPatch signer [] 0) == .error .unstated
#guard answer ((effectAt 1).memberPatch signer ⟨[]⟩ 0) == .error .unstated
#guard (effectAt 9).spec.commutes [] == true

/-- The content read, declared commuting, with the member patch it states today. -/
def commutingReadGhost : Effect :=
  { readEffect with spec := { readSpec with commutes := fun _ => true } }

#guard commutingReadGhost.member.isSome
#guard answer (commutingReadGhost.memberPatch signer () 0) == .error .commutes
#guard answer (readEffect.memberPatch signer () 0) == .ok 0

/-! ## A registered write: the kind definition revision -/

section KindDefinition
open Minidregg.Kernel.NativeThinConsent
open Minidregg.Compiler
open Minidregg.Compiler.WorldKindDescriptor
open Minidregg.Theory.Store
open Minidregg.Theory.CellState

def openField : Field := ⟨1, "open", "whether the poll accepts votes", .natural, .ram⟩
def votesField : Field := ⟨2, "votes", "one vote per member", .natural, .appendOnly⟩

def definitionAt (revision : Nat) (fields : List Field) : WorldKindCell.Definition :=
  ⟨⟨9, revision, fields⟩, StoreCodec.encode (wire ⟨9, revision, fields⟩) 0⟩

def richOld : WorldKindCell.Definition := definitionAt 1 [openField]
def richNext : WorldKindCell.Definition := definitionAt 2 [openField, votesField]
def richSkipped : WorldKindCell.Definition := definitionAt 3 [openField, votesField]

def richPre : Materialized WorldKindCell.definitionMaterializer :=
  materialize WorldKindCell.definitionMaterializer
    ((0 : Store WorldKindCell.definitionLayout).set WorldKindCell.definitionAddress (some richOld))

def richTarget (kind : ResourceKind) (definition : WorldKindCell.Definition) : Target :=
  ⟨kind, 9, ⟨0⟩, 1, richPre.root, .kindDefinition definition, none, none, none⟩

def bytesOf (store : Store WorldKindCell.definitionLayout) : List UInt8 :=
  WorldKindCell.definitionMaterializer.codec.encode store

/-- The receiver's computation and the member patch of one revision of the sample kind. -/
def revise (kind : ResourceKind) (definition : WorldKindCell.Definition) :
    Except Reject (Store WorldKindCell.definitionLayout) ×
      Except Minidregg.Kernel.NativeThinConsent.Refusal (Patch WorldKindCell.definitionLayout) :=
  (computeTarget sampleSnapshot ⟨0⟩ sampleAmbient sampleCommand (richTarget kind definition) richPre,
   memberPatch sampleCommand (richTarget kind definition) richPre.logical)

-- Satisfiable, executed: computed, shown, one write, and the shown patch run is the post.
#guard (match revise .object richNext with
  | (.ok post, .ok patch) =>
      patch.length == 1 && bytesOf (Patch.run richPre.logical patch) == bytesOf post &&
        post WorldKindCell.definitionAddress == some richNext &&
        bytesOf post != bytesOf richPre.logical
  | _ => false)
-- A skipped revision: refused by both, each by its own name.
#guard (match revise .object richSkipped with
  | (.error (.effect refusal), .error (Minidregg.Kernel.NativeThinConsent.Refusal.patchRefused 9)) =>
      reprStr refusal == "Effect.KindDefinition.notNextRevision"
  | _ => false)
-- Shown, then refused: under an account role the member patch answers and the receiver refuses.
#guard (match revise .account richNext with
  | (.error .wrongRole, .ok patch) => patch.length == 1
  | _ => false)

#guard payloadStream.encode (.kindDefinition richNext) ==
  5 :: WorldKindCell.definitionStream.encode richNext
#guard (payloadStream.decodePrefix (5 :: WorldKindCell.definitionStream.encode richNext ++ [99])).map
    (fun d => (decide (d.1 = .kindDefinition richNext), d.2)) == some (true, [99])
#guard effectNamed "kindDefinition" == some 5
#guard ((effectAt 5).toJson richNext).map (·.1) == ["kind", "revision", "exactDefinitionHex"]
#guard ((effectAt 5).toJson richNext).head? == some ("kind", Lean.Json.str "9")
#guard (effectAt 5).display richNext == ["kind 9: layout revision 2, 2 semantic fields"]
#guard (match (effectAt 5).ofJson "p" (Lean.Json.mkObj [("type", "kindDefinition")]) with
  | .ok _ => false | .error text => text == "p: missing field definition")

end KindDefinition

/-! ## A registered write whose fields are inside its cell: world actions -/

section World
open Minidregg.Kernel.NativeThinConsent
open Minidregg.Compiler
open Minidregg.Compiler.WorldKindDescriptor
open Minidregg.Theory.Store
open Minidregg.Theory.CellState
open Minidregg.Kernel (WorldKindInstance.Action)

def pollDescriptor : Descriptor := ⟨9, 1, [votesField]⟩

/-- A poll instance without votes. -/
def pollPre : Materialized WorldKindCell.instanceMaterializer :=
  materialize WorldKindCell.instanceMaterializer
    (WorldKindCell.instanceOf ⟨0⟩ ⟨pollDescriptor, by decide, 0⟩)

/-- One vote: field 2 at key 7 becomes 1. -/
def vote : List WorldKindInstance.Action := [.create 2 7 (ScalarCodec.natural.stream.encode 1)]
/-- A write of a vote that was never cast. -/
def revote : List WorldKindInstance.Action :=
  [.write 2 7 (ScalarCodec.natural.stream.encode 1) (ScalarCodec.natural.stream.encode 2)]

def worldTarget (actions : List WorldKindInstance.Action) : Target :=
  ⟨.object, 9, ⟨0⟩, 1, pollPre.root, .world actions, none, none, none⟩

def act (actions : List WorldKindInstance.Action) :
    Except Reject (Store WorldKindCell.instanceLayout) ×
      Except Minidregg.Kernel.NativeThinConsent.Refusal (Patch WorldKindCell.instanceLayout) :=
  (computeTarget sampleSnapshot ⟨0⟩ sampleAmbient sampleCommand (worldTarget actions) pollPre,
   memberPatch sampleCommand (worldTarget actions) pollPre.logical)

def instanceBytes (store : Store WorldKindCell.instanceLayout) : List UInt8 :=
  WorldKindCell.instanceMaterializer.codec.encode store

-- Satisfiable, executed: the vote is computed and shown; the shown patch is one write, and run
-- on the loaded store it is the receiver's post, which differs from the pre-state.
#guard (match act vote with
  | (.ok post, .ok patch) =>
      patch.length == 1 && instanceBytes (Patch.run pollPre.logical patch) == instanceBytes post &&
        instanceBytes post != instanceBytes pollPre.logical
  | _ => false)
-- A guard that does not hold: refused by both, each by its own name.
#guard (match act revote with
  | (.error (.effect refusal), .error (Minidregg.Kernel.NativeThinConsent.Refusal.patchRefused 9)) =>
      reprStr refusal == "Effect.World.worldKind"
  | _ => false)
-- The footprint is the declaration's: the inner field, not the cell's body.
#guard (match act vote with
  | (.ok post, _) =>
      decide ((targetFullFootprint (worldTarget vote) pollPre.logical post).touched ≠ {CellField.body})
  | _ => false)
#guard (effectAt 4).authors [] == false && (effectAt 4).authors vote == true
#guard payloadStream.encode (.world vote) ==
  4 :: (Tower256ConcreteBackend.StreamCodec.list Minidregg.Kernel.WorldKindInstance.actionStream).encode vote
#guard effectNamed "world" == some 4
#guard ((effectAt 4).toJson vote).map (·.1) == ["actionCount", "exactActionsHex"]
#guard (effectAt 4).display vote == ["world instance: 1 guarded field actions"]

end World

end Minidregg.Assurance.MemberPatchPoles
