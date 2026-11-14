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
* *scalar actions* (code 0), on a declared object cell that declares one field. A write is
  computed and shown; the shown patch run on the loaded store is the receiver's post. A guard
  that does not hold is refused by the receiver under the
  declaration's name while the member patch still answers (it is the actions' own patch and
  reads no store): shown, then refused, nothing commits. A capability the authority cell does not
  hold and a guard over a field its scope does not name are refused by the header before the
  schema version and the root. The order of the header against the semantics: an account with a
  wrong version, an account with a stale root and no action with a stale root are refused by the
  header (`unsupportedVersion`, `staleTarget`); the scalar receiver `prepareCell`, which the
  deleted arm called, names the role and the empty list first at the same inputs. No action with
  a wrong version (the control) is `unsupportedVersion` on both.
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

/-! ## Scalar actions -/

section Scalar
open Minidregg.Kernel.NativeThinConsent
open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.Store
open Minidregg.Theory.CellState
open Minidregg.Theory.DeclaredActionLowering (Action)

/-- A write capability on object 41 whose scope names field 2 alone. -/
def scalarCapability : CredentialAuthorityState.StoredCapability .object :=
  ⟨{ id := ⟨5⟩, root := ⟨5⟩, parent := none, issuer := ⟨0⟩, holder := .bearer,
     scope := { targets := .explicit {⟨41⟩}, verbs := {.mutateObject}, perRequestBytes := 0,
                fields := some {.slot 2} },
     notBefore := 0, notAfter := 0, issuerEpoch := 0, policyId := ⟨0⟩, policyEpoch := 0,
     ancestors := ∅, channels := ∅ }, []⟩

/-- A whole-cell capability on account 41. -/
def accountCapability : CredentialAuthorityState.StoredCapability .account :=
  ⟨{ id := ⟨6⟩, root := ⟨6⟩, parent := none, issuer := ⟨0⟩, holder := .bearer,
     scope := { targets := .explicit {⟨41⟩}, verbs := {.transfer}, perRequestBytes := 0,
                fields := none },
     notBefore := 0, notAfter := 0, issuerEpoch := 0, policyId := ⟨0⟩, policyEpoch := 0,
     ancestors := ∅, channels := ∅ }, []⟩

def scalarSnapshot : AuthoritySnapshot :=
  CredentialAuthorityDomain.Snapshot.ofCell ⟨0⟩ 0 (fun _ => false)
    (materialize CredentialAuthorityCell.materializer
      (Store.set (Store.set 0 ⟨.capability .object, ⟨5⟩⟩ (some scalarCapability))
        ⟨.capability .account, ⟨6⟩⟩ (some accountCapability)))

def scalarPre : Materialized DeclaredEffectCell.materializer :=
  materialize DeclaredEffectCell.materializer scalarStore

def staleRoot : Digest := ⟨scalarPre.root.value + 1⟩

/-- A write of field 2 that expects a value the cell does not hold. -/
def scalarMisguarded : List Action := [.write (.objectField ⟨41⟩ ⟨2⟩) (some 9) 7]
/-- A write of field 3, which the capability's scope does not name. -/
def scalarUndeclared : List Action := [.create (.objectField ⟨41⟩ ⟨3⟩) 1]

def scalarTarget (kind : ResourceKind) (capability : Nat) (version : Nat) (root : Digest)
    (actions : List Action) : Target :=
  ⟨kind, 41, ⟨capability⟩, version, root, .scalar actions, none, none, none⟩

def write (kind : ResourceKind) (capability version : Nat) (root : Digest) (actions : List Action) :
    Except Reject (Store EffectDeclaration.effectLayout) ×
      Except Minidregg.Kernel.NativeThinConsent.Refusal (Patch EffectDeclaration.effectLayout) :=
  (computeTarget scalarSnapshot ⟨0⟩ sampleAmbient sampleCommand
      (scalarTarget kind capability version root actions) scalarPre,
   memberPatch sampleCommand (scalarTarget kind capability version root actions) scalarPre.logical)

def declaredBytes (store : Store EffectDeclaration.effectLayout) : List UInt8 :=
  DeclaredEffectCell.materializer.codec.encode store

/-- A refusal as the Host commits it. -/
def named (result : Except Reject (Store EffectDeclaration.effectLayout)) : String :=
  match result with
  | .ok _ => "admitted"
  | .error reason => ((reprStr reason).splitOn "DeclaredResourceController.").getLastD ""

-- Satisfiable, executed: the write is computed and shown; the shown patch is one write, and run
-- on the loaded store it is the receiver's post (the cell has no blinding, so no ratchet).
#guard (match write .object 5 1 scalarPre.root scalarWrite with
  | (.ok post, .ok patch) =>
      patch.length == 1 && declaredBytes (Patch.run scalarPre.logical patch) == declaredBytes post &&
        declaredBytes post != declaredBytes scalarPre.logical
  | _ => false)
-- Teeth at the declaration: the semantics emits one operation at the sample write, so the member
-- patch `fun _ _ _ => some []` (a declaration showing "no change") is not `MemberExact`.
#guard (match scalarSpec.sem (targetCtx scalarSnapshot ⟨0⟩ sampleAmbient sampleCommand .object 41 ⟨5⟩
    none none none) scalarWrite scalarStore with
  | .ok patch => patch.length == 1
  | .error _ => false)
-- Shown, then refused: a guard that does not hold.
#guard (match write .object 5 1 scalarPre.root scalarMisguarded with
  | (refused, .ok patch) => named refused == "Reject.effect (Effect.Scalar.guardRejected 0)" && patch.length == 1
  | _ => false)
-- The header's scope gate, before the version and the root: a capability the authority cell
-- does not hold, and a guard over a field the scope does not name.
#guard named (write .object 9 7 staleRoot scalarWrite).1 == "Reject.capabilityRejected"
#guard named (write .object 5 7 staleRoot scalarUndeclared).1 == "Reject.fieldNotNamed"
-- The three orders that moved: the header's refusal is named, where the scalar receiver the
-- deleted arm called names the role or the empty list at the same inputs.
#guard named (write .account 6 7 scalarPre.root scalarWrite).1 == "Reject.unsupportedVersion"
#guard named (write .account 6 1 staleRoot scalarWrite).1 == "Reject.staleTarget"
#guard named (write .object 5 1 staleRoot []).1 == "Reject.staleTarget"
-- What each names once the header passes: the declaration's own refusal.
#guard named (write .account 6 1 scalarPre.root scalarWrite).1 == "Reject.effect (Effect.Scalar.accountRequiresBook)"
#guard named (write .object 5 1 scalarPre.root []).1 == "Reject.effect (Effect.Scalar.emptyActions)"
-- The control, which did not move: no action with a wrong version, and an account with no action.
#guard named (write .object 5 7 scalarPre.root []).1 == "Reject.unsupportedVersion"
#guard named (write .account 6 1 scalarPre.root []).1 == "Reject.effect (Effect.Scalar.accountRequiresBook)"

/-- The scalar receiver the deleted arm called (`prepareCell`, still the purse's and the job's),
at the same role, version, root and actions: the order before the binding. -/
def before (kind : ResourceKind) (version : Nat) (root : Digest) (actions : List Action) : String :=
  match Minidregg.Kernel.DeclaredResourceScalar.prepareCell scalarSnapshot ⟨0⟩ sampleAmbient scalarPre
      ⟨kind, 41, ⟨0⟩, ⟨5⟩, version, root, 0, actions⟩ with
  | .ok _ => "admitted"
  | .error reason => ((reprStr reason).splitOn ".").getLastD ""

#guard before .account 7 scalarPre.root scalarWrite == "accountRequiresBook"
#guard before .account 1 staleRoot scalarWrite == "accountRequiresBook"
#guard before .object 1 staleRoot [] == "emptyActions"
#guard before .object 7 scalarPre.root [] == "unsupportedVersion"
#guard before .account 1 scalarPre.root [] == "accountRequiresBook"
#guard before .object 1 scalarPre.root scalarWrite == "admitted"

-- The wire and the faces: the tag octet 0 and the actions' canonical bytes, as the hand arm
-- wrote them; the request's and the inbox's JSON; the display; the run's claimed writes.
#guard payloadStream.encode (.scalar scalarWrite) ==
  0 :: (Tower256ConcreteBackend.StreamCodec.list
    Minidregg.Kernel.DeclaredResourceScalar.actionStream).encode scalarWrite
#guard (payloadStream.decodePrefix (payloadStream.encode (.scalar scalarWrite) ++ [99])).map
    (fun d => (decide (d.1 = .scalar scalarWrite), d.2)) == some (true, [99])
#guard effectNamed "scalar" == some 0
#guard ((effectAt 0).toJson scalarWrite).map (·.1) == ["actions"]
#guard (Lean.Json.mkObj ((effectAt 0).toJson scalarWrite)).compress ==
  "{\"actions\":[{\"key\":{\"field\":\"2\",\"resource\":\"41\",\"type\":\"object\"},\"type\":\"create\",\"value\":\"7\"}]}"
#guard (effectAt 0).display scalarWrite == ["create field 2 = 7"]
#guard (effectAt 0).display scalarMisguarded == ["write field 2 := 7 (expected 9)"]
#guard (effectAt 0).authors [] == false && (effectAt 0).authors scalarWrite == true
#guard (match (effectAt 0).ofJson "p" (Lean.Json.mkObj [("type", "scalar"), ("actions", .arr #[
    Lean.Json.mkObj [("type", "create"), ("value", "7"), ("key", Lean.Json.mkObj
      [("type", "object"), ("resource", "41"), ("field", "2")])]])]) with
  | .ok actions => decide (Payload.registered 0 actions = .scalar scalarWrite) | .error _ => false)
#guard (match Minidregg.Kernel.ResourcePayloadJson.payloadOfJson [] "p"
    (Lean.Json.mkObj [("type", "scalar"), ("actions", .arr #[])]) with
  | .ok payload => decide (payload = .scalar []) | .error _ => false)
#guard (targetWrites 0 (scalarTarget .object 5 1 scalarPre.root scalarWrite) scalarPre.logical ⟨0⟩).map
    (fun writes => writes.map fun w => (w.field, w.value)) == some [(2, 7)]

end Scalar

end Minidregg.Assurance.MemberPatchPoles
