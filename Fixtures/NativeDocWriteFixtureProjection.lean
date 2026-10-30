/-
# The semantic projection of the native document-write fixture

`Fixtures.NativeDocWriteFixture` re-runs a member's ordinary document write (`doc append`) as
the native Host admitted it, and checks that its record is byte for byte the Host's.  Both
sides are this tree's code and the pinned bytes are regenerated from a run of it, so a change
to WHAT such a write records is absorbed by regeneration.  This module is the other half: a
pure projection of the accepted write onto what the member ASKED FOR
(`native/resource-client/doc-write-native-acceptance.py`), as `key = value` lines, compared to
the hand-written `Fixtures/NativeDocWriteFixtureAuthority.lean`.

Every line is a function of the record and the command alone, never of a byte the run chose.
-/
import Fixtures.NativeAcceptedFixtureProjection
import Kernel.ContentResource

namespace Minidregg.Fixtures.NativeDocWriteFixtureProjection

open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Fixtures.NativeAcceptedFixtureProjection (Line kindOf chargeLines)

set_option autoImplicit false

/-- The retained payload bytes of the document cell the call targets, after the write
(`ContentResource.contentPayloadBytes`: the text the member appended, nothing else). -/
def targetPayloadBytes (command : DeclaredResourceController.Command) (record : IntentRecord) : String :=
  match command.targets.head? with
  | none => "no target"
  | some target =>
      match record.writes.find? fun write => write.cellId.value == target.target with
      | none => "no target write"
      | some write =>
          match (ResourceBirthCodec.LifecycleImage.codec CanonicalCellRegistry.registry).decode
              write.canonicalPostBytes with
          | some (.live ⟨.content, payload⟩) => toString (ContentResource.contentPayloadBytes payload.logical)
          | _ => "not a content cell"

/-- The lane of a document write that measures the call besides storage: its signed bytes
(`turnBytes`). -/
def docWriteRelative : List Theory.ResourceCost.Lane := [.turnBytes]

/-- **The projection of an accepted document write**: who signed and how many signature
checks, which cells it writes (by kind) and guards, what the document holds afterwards,
and what it is charged. -/
def projectDocWrite (deployment : CanonicalCellRegistry.Deployment)
    (command : DeclaredResourceController.Command) (record : IntentRecord) (receipts : List Nat)
    (ingress : List UInt8) (legs : List (World.Leg Minidregg.Kernel.DeployedBridge.deployedR)) :
    List Line :=
  let targetCells := command.targets.map fun target => target.target
  [("write.verdict", "accepted"),
   ("write.subject", toString (record.subject.map (·.value))),
   ("write.targets", toString command.targets.length),
   ("write.receipts", toString receipts.length),
   ("write.receipts.signedBySubject", toString (receipts.all (· == command.subject.value))),
   ("write.writes", ", ".intercalate (record.writes.map fun write => kindOf write.canonicalPostBytes)),
   ("write.writes.targets", toString (targetCells.all fun cell =>
      record.writes.any fun write => write.cellId.value == cell)),
   ("write.guards.authorityCell", toString (record.readGuards.any fun guard =>
      guard.cellId.value == deployment.authorityCellId)),
   ("write.guards.writtenCells", toString (record.readGuards.any fun guard =>
      record.writes.any fun write => write.cellId == guard.cellId)),
   ("write.nullifiers", toString record.nullifiers.length),
   ("write.document.payloadBytes", targetPayloadBytes command record)] ++
  chargeLines "write" docWriteRelative ingress legs record

end Minidregg.Fixtures.NativeDocWriteFixtureProjection
