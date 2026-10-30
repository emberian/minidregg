/-
# The semantic projection of the native accepted fixture

`Fixtures.NativeAcceptedFixture` re-runs the first native Objective acceptance and
checks that its record is byte for byte the Host's.  Both sides are this tree's
code, and the bytes it pins are regenerated from a run of the same tree, so a
change to WHAT an accepted invocation records (a dropped write, a changed charge,
a lost signature check) is absorbed by regeneration.

This module is the other half: a small, pure projection of an accepted
invocation's record onto what the acceptance DRIVER asked for
(`native/resource-client/objective-native-acceptance.py`, `objective-first`), as
`key = value` lines.  The expected lines are the hand-written authority file
`Fixtures/NativeAcceptedFixtureAuthority.lean`, which no generator writes.  The
fixture module checks the projection of its re-run against that file
(`first_projection`), and `scripts/native-accepted-fixture/generate.sh` refuses to
write data whose projection differs from it (`replay.lean` prints the same
projection, this definition).  An authority change is its own reviewed commit
(`scripts/pipeline/check-fixture-authority.sh`).

Every line is a function of the record, the command, the call's signed ingress and
the write's legs, never of a byte the run chose (an id, a root, a digest).  A byte
lane measures bytes whose length the run chooses: digests, ids and nonces are encoded
at their natural width, so the call and the written values move by a few bytes from
run to run (and the ingress framing with the width of the semantics digest).  Such a
lane is stated as its relation to the run, never as a number:
* the retained event, `ingress` when its canonical bytes ARE the call's signed ingress
  (`DeclaredResourceController.signedBytes` of the deployment's domain, the semantics
  and the signed command), and a lane that measures the ingress, `ingress` when it is
  its length (`relativeTo`);
* the storage lane, `event + legs` (`storageRelation`): the retained event plus the
  written values of the World's legs (`DeployedHistory.legBytes`) and nothing else (no
  born image, no post image, no per-kind framing);
* the legs' shape (`legShape`: each leg's operations by kind), which the run does not
  choose.
-/
import Kernel.DeclaredResourceController
import Kernel.DeployedCharge
import Kernel.DurableReceiver
import Kernel.PayCellDomain
import Kernel.ObjectiveBendNativeInput
import Kernel.ContentResource
import Compiler.ObjectiveBendPlanAdapter

namespace Minidregg.Fixtures.NativeAcceptedFixtureProjection

open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- One authority line. -/
abbrev Line := String × String

/-- Parse `key = value` lines; blank lines and `#` comments are skipped. -/
def parseAuthority (text : String) : List Line :=
  (text.splitOn "\n").filterMap fun raw =>
    let line := raw.trim
    if line.isEmpty || line.startsWith "#" then none
    else match line.splitOn " = " with
      | [key, value] => some (key.trim, value.trim)
      | _ => some ("malformed", line)

/-- The registry kind of a write's live post cell, by its stable tag. -/
def kindOf (bytes : List UInt8) : String :=
  match (ResourceBirthCodec.LifecycleImage.codec CanonicalCellRegistry.registry).decode bytes with
  | some (.live cell) => s!"tag{CanonicalCellRegistry.Kind.tag cell.kind}"
  | some .retired => "retired"
  | some .fresh => "fresh"
  | none => "undecodable"

/-- A run-dependent byte count stated against a run quantity named `name` of `base` bytes:
`name` when equal, else the offset (`name + k`, `name - k`). -/
def relativeTo (name : String) (base value : Nat) : String :=
  if value = base then name
  else if base ≤ value then s!"{name} + {value - base}" else s!"{name} - {base - value}"

/-- The retained event against the signed ingress: `ingress` when its canonical bytes are
exactly the ingress, else what differs. -/
def eventRelation (ingress : List UInt8) (record : IntentRecord) : String :=
  if record.event.canonicalBytes = ingress then "ingress"
  else s!"not the ingress ({relativeTo "ingress" ingress.length record.event.canonicalBytes.length})"

open Minidregg.Kernel.DeployedBridge (deployedR bridge) in
/-- The World's legs of a record's writes against the cells of the snapshot it was admitted
at (`DeployedCharge.storageAt`'s legs). -/
def recordLegs {rootBytes : List UInt8 → Digest} (snap : DataSnapshot rootBytes)
    (record : IntentRecord) : List (World.Leg deployedR) :=
  (TurnOfIntent.deltas bridge.codec (HostRefinesWorld.cellsOf bridge snap) record.writes).filterMap
    fun d => d.2.leg? bridge.codec d.1

/-- A leg's operations by kind, in order (`write`, `allocate`, `free`, `read`). -/
def legShape (legs : List (World.Leg Minidregg.Kernel.DeployedBridge.deployedR)) : String :=
  "; ".intercalate (legs.map fun leg => ", ".intercalate (leg.patch.map fun
    | .write .. => "write" | .allocate .. => "allocate" | .free .. => "free" | .read .. => "read"))

/-- The storage lane stated as its relation to the run: `event + legs` when it is exactly
the retained event's canonical bytes plus the legs' written values, else the offset. -/
def storageRelation (record : IntentRecord)
    (legs : List (World.Leg Minidregg.Kernel.DeployedBridge.deployedR)) : String :=
  let base := record.event.canonicalBytes.length + (legs.map DeployedHistory.legBytes).sum
  let value := record.exactCharge .storageBytes
  if value = base then "event + legs"
  else if base ≤ value then s!"event + legs + {value - base}" else s!"event + legs - {base - value}"

/-- The charge lanes, in a fixed order. -/
def lanes : List (String × Theory.ResourceCost.Lane) :=
  [("incidences", .incidences), ("turnBytes", .turnBytes), ("memoryTouches", .memoryTouches),
   ("storageBytes", .storageBytes), ("witnessBytes", .witnessBytes), ("proofWork", .proofWork),
   ("feeDebit", .feeDebit), ("networkBytes", .networkBytes), ("sideEffectCount", .sideEffectCount),
   ("leaseByteBlocks", .leaseByteBlocks)]

section Receipts

open Minidregg.Kernel.DeclaredResourceController

variable {F : Type} [Field F] [DecidableEq F] {deployment : CanonicalCellRegistry.Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {ground : Ground deployment}
  {command : Command}

/-- The subject each of an accepted invocation's signature checks was for: the
authority leg, then each target leg (its ordinary leg's receipt, or an observe-only
read target's `ReadLeg`'s: `AcceptedInvocation.receipt`). -/
def receiptSubjects {prepared : PreparedInvocation deployment profile ambient ground command}
    {signed : SignedCommand} (accepted : AcceptedInvocation prepared signed) : List Nat :=
  (accepted.receipt none :: (List.finRange command.targets.length).map fun i =>
    accepted.receipt (some i)).map fun receipt => receipt.request.2.subject.value

end Receipts

/-! ## What the written cells hold

Values the driver's inputs determine: the compute the pay cell records for the
signing subject (the request's capacity `proofWork`, priced by the tariff), and
the atom the call created in its target (the requested atom id, schema and byte).
Nothing here reads a run-chosen byte (a root, a day, a nonce). -/

/-- The admitted compute steps the record's pay-cell write holds for `subject`. -/
def payComputeSteps (deployment : CanonicalCellRegistry.Deployment) (record : IntentRecord)
    (subject : Nat) : String :=
  match record.writes.find? fun write => write.cellId == PayCellDomain.cellIdOf deployment with
  | none => "no pay write"
  | some write =>
      match PayCellDomain.decodeCell write.canonicalPostBytes with
      | none => "undecodable"
      | some cell =>
          match PayCell.computeUsageAt cell.logical subject with
          | none => "no usage row"
          | some usage => toString usage.admittedSteps

/-- A digest spelled as the driver's argument labels spell it (`digest_hex`). -/
def labelDigest (text : String) : Option Digest := do
  let bytes ← ObjectiveBendPlanAdapter.unhex text.toList
  ObjectiveNativeScalarBinding.rootCodec.decode bytes

/-- The requested atom of an Objective call: (atom id, schema, byte), read from the
call's signed arguments (`{atom, schema, byte}`, the driver's `build_request`). -/
def requestedAtom (command : DeclaredResourceController.Command) : Option (Digest × Digest × Nat) := do
  let some claim := command.objectiveClaim.toOption.join | none
  let terms ← (ObjectiveBendNativeInput.parseArguments claim.arguments.length 512 claim.arguments).toOption
  match terms with
  | [.record [("atom", .label atom), ("schema", .label schema), ("byte", .nat byte)]] =>
      pure (← labelDigest atom, ← labelDigest schema, byte)
  | _ => none

/-- The created atom in the target's post: its schema and bytes, found by the id the
call requested. -/
def createdAtom (command : DeclaredResourceController.Command) (record : IntentRecord) :
    List Line :=
  match requestedAtom command, command.targets.head? with
  | some (atom, schema, byte), some target =>
      let found := record.writes.find? fun write => write.cellId.value == target.target
      let atomLine := match found with
        | none => "no target write"
        | some write =>
            match (ResourceBirthCodec.LifecycleImage.codec CanonicalCellRegistry.registry).decode
                write.canonicalPostBytes with
            | some (.live ⟨.content, payload⟩) =>
                match payload.logical ⟨.atoms, ⟨atom⟩⟩ with
                | none => "absent"
                | some created =>
                    let kindOk := decide (created.kind = .inlineObject schema)
                    s!"inlineObject={kindOk} payload={created.payload}"
            | _ => "not a content cell"
      [("first.created.requestedSchema", toString schema.value),
       ("first.created.requestedByte", toString byte),
       ("first.created.atom", atomLine)]
  | _, _ => [("first.created.atom", "no requested atom")]

/-- The byte lines of a record under `pre`: the retained event against the signed ingress, the
legs' shape, then each charge lane: storage as `storageRelation`, a lane in `relative` as its
relation to the ingress's length (`relativeTo`), every other lane its value. -/
def chargeLines (pre : String) (relative : List Theory.ResourceCost.Lane) (ingress : List UInt8)
    (legs : List (World.Leg Minidregg.Kernel.DeployedBridge.deployedR)) (record : IntentRecord) :
    List Line :=
  [(s!"{pre}.event", eventRelation ingress record),
   (s!"{pre}.legs", legShape legs)] ++
  lanes.map fun (name, lane) => (s!"{pre}.charge.{name}",
    if lane = .storageBytes then storageRelation record legs
    else if relative.contains lane then relativeTo "ingress" ingress.length (record.exactCharge lane)
    else toString (record.exactCharge lane))

/-- The lanes of an accepted Objective invocation that measure the call besides storage:
none (every other lane is the request's capacity). -/
def acceptedRelative : List Theory.ResourceCost.Lane := []

/-- **The projection of an accepted invocation** onto what the driver asked for:
who signed and how many signature checks, which cells it writes (by kind and by
role), what it guards, what it spends, and what it is charged. `ingress` is the call's
signed ingress (`DeclaredResourceController.signedBytes`). -/
def projectAccepted (deployment : CanonicalCellRegistry.Deployment)
    (command : DeclaredResourceController.Command) (record : IntentRecord) (receipts : List Nat)
    (ingress : List UInt8) (legs : List (World.Leg Minidregg.Kernel.DeployedBridge.deployedR)) :
    List Line :=
  let targetCells := command.targets.map fun target => target.target
  [("first.verdict", "accepted"),
   ("first.subject", toString (record.subject.map (·.value))),
   ("first.targets", toString command.targets.length),
   ("first.receipts", toString receipts.length),
   ("first.receipts.signedBySubject", toString (receipts.all (· == command.subject.value))),
   ("first.writes", ", ".intercalate (record.writes.map fun write => kindOf write.canonicalPostBytes)),
   ("first.writes.targets", toString (targetCells.all fun cell =>
      record.writes.any fun write => write.cellId.value == cell)),
   ("first.writes.payCell", toString (record.writes.any fun write =>
      write.cellId == PayCellDomain.cellIdOf deployment)),
   ("first.guards.authorityCell", toString (record.readGuards.any fun guard =>
      guard.cellId.value == deployment.authorityCellId)),
   ("first.guards.writtenCells", toString (record.readGuards.any fun guard =>
      record.writes.any fun write => write.cellId == guard.cellId)),
   ("first.nullifiers", toString record.nullifiers.length),
   ("first.pay.computeSteps", payComputeSteps deployment record command.subject.value)] ++
  createdAtom command record ++
  chargeLines "first" acceptedRelative ingress legs record

/-- The projection of a refused call: its verdict and the refusal's name. -/
def projectRefused (reason : String) : List Line :=
  [("refused.verdict", "refused"), ("refused.reason", reason)]

/-- The last component of a refusal's printed name (`…Reject.objectiveSource`). -/
def reasonName (printed : String) : String :=
  ((printed.splitOn ".").getLast?.getD printed).trim

/-- The field-by-field difference of two projections (empty when equal). -/
def diff (expected actual : List Line) : List String :=
  let keys := (expected.map Prod.fst ++ actual.map Prod.fst).eraseDups
  keys.filterMap fun key =>
    match expected.lookup key, actual.lookup key with
    | some e, some a => if e == a then none else some s!"{key}: authority {e}, run {a}"
    | some e, none => some s!"{key}: authority {e}, run has no such field"
    | none, some a => some s!"{key}: run {a}, authority has no such field"
    | none, none => none

end Minidregg.Fixtures.NativeAcceptedFixtureProjection
