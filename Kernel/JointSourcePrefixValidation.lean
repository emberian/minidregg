/- Native historical-prefix validation for the common source log.
The proposed parent can be prepared rather than physically committed. This
module reconstructs its exact records in memory, then executes the real native
source walk at every original height. It never appends to physical storage.
-/
module

public import Kernel.NativeHostReplay
public import Compiler.GenericSimplexSourceAnchor

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Init.System.ST
import all Init.System.IO

@[expose] public section

namespace Minidregg.Kernel.JointSourcePrefixValidation
open Minidregg.Theory
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexSourceAnchor
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.NativeHost
set_option autoImplicit false

/-- Inert engine blocks do not create source history or source heights. -/
def sourceRecords (block : Block) : Block := block.filter (fun bytes => !bytes.isEmpty)

private def decodeRecords : Block → Option (List IntentRecord)
  | [] => some []
  | bytes :: rest => do
      let record ← DurableCheckpointCodec.recordFrame.decode bytes
      let tail ← decodeRecords rest
      some (record :: tail)

/-- Opaque source-private checked-prefix capability. The supplied records have
been freshly admitted at their actual original source prefixes, under the fixed
native verifier and deployment source configuration. Signature validity for an
engine proposal is not a constructor of this capability. -/
structure Validated (config : NativeHost.Config) (expected : Context) (block : Block) where
  private mk ::
  contextPinned : config.jointConsensus = some expected
  target : Durable
  anchorExact : expected.instanceBytes = anchorBytes config.genesisHeight target.image.seed
  recordsExact : target.image.accepted.map DurableCheckpointCodec.recordFrame.encode = sourceRecords block
  checked : NativeHostReplay.Verified config target

inductive Result (config : NativeHost.Config) (expected : Context) (block : Block) where
  | accepted (validated : Validated config expected block)
  | rejected (detail : String)
  /-- Native helper/dependency availability and source refusal are deliberately
  not conflated with proof of invalidity. A bounded controller queue may refetch
  and retry. Only an accepted token enables internal Input.checked. -/
  | retry (failure : NativeHostReplay.Failure)

/-- This function receives the fixed host Config and the source seed retained
by that deployment. Neither roster, verifier callback, nor seed is taken from
a network proposal. Exact context+anchor checks precede native source replay.
The full-history profile supports genesis replay; checkpoint epoch migration is
not silently interpreted as a new genesis. -/
def validate (config : NativeHost.Config) (origin : Opened config) (expected : Context) (block : Block) :
    IO (Result config expected block) := do
  let seed := origin.durable.image.seed
  if contextPinned : config.jointConsensus = some expected then
    if expected.scope != digestStream.encode config.deployment.domain then
      return .rejected "source consensus scope mismatch"
    if anchorExact : expected.instanceBytes = anchorBytes config.genesisHeight seed then
      if seedIdentity seed != config.expectedSeed then return .rejected "pinned source seed mismatch"
      let some records := decodeRecords (sourceRecords block)
        | return .rejected "noncanonical source record in proposed prefix"
      let image : Image := Image.ofAccepted seed records
      match built : DurableReceiverIO.loadImage ResourceBirthCodec.rootBytes (config.logStart seed) image with
      | .error detail => return .rejected detail
      | .ok target =>
          have imageExact := DurableReceiverIO.loadImage_image built
          if recordsExact : target.image.accepted.map DurableCheckpointCodec.recordFrame.encode = sourceRecords block then
            -- A proposed prefix has no Store: the walk reads its history through the Reader of a
            -- throwaway Store holding exactly these records (`scratchReader`). The proposal carries
            -- no prior commitment, so the scratch commitment is the prefix's own height and root;
            -- what makes the result authoritative is the walk re-admitting every record at its
            -- original height, over exactly the block's records (`recordsExact`). A scratch Store
            -- that cannot be written or read is an availability failure (`retry`), never "absent".
            let checkedValue ← IO.FS.withTempDir fun directory => do
              let scratch ← config.scratch directory
              let commitment : DurableHistoryStore.Commitment :=
                ⟨target.image.accepted.length,
                  NativeHostCodec.worldRoot config.deployment.domain config.profile.semantics target.image,
                  NativeHostCodec.worldRoot config.deployment.domain config.profile.semantics⟩
              match ← DurableHistoryStore.scratchReader scratch.physicalTransport ResourceBirthCodec.rootBytes
                  target.image target.logStart commitment with
              | .error detail => return .error ⟨0, s!"scratch history Store: {detail}"⟩
              | .ok ⟨_, reader⟩ => NativeHostReplay.verifyLoaded config reader target
            match checkedValue with
            | .error failure => return .retry failure
            | .ok checked =>
                have pinnedAnchor : expected.instanceBytes = anchorBytes config.genesisHeight target.image.seed := by
                  rw [imageExact]; exact anchorExact
                return .accepted ⟨contextPinned,target,pinnedAnchor,recordsExact,checked⟩
          else return .rejected "source record frame roundtrip mismatch"
    else return .rejected "exact source genesis anchor mismatch"
  else return .rejected "consensus context is not deployment pinned"

/-- Opaque source-private capability for the common case: one record, freshly admitted by
the native source at a verified tip. The history it stands for is the tip's records followed
by `record`; the tip's own records were admitted when it was verified, so nothing below the
tip is executed again. -/
structure ValidatedNext (config : NativeHost.Config) (expected : Context) {target : Durable}
    (tip : NativeHostReplay.Verified config target) (record : Bytes) where
  private mk ::
  contextPinned : config.jointConsensus = some expected
  anchorExact : expected.instanceBytes = anchorBytes config.genesisHeight tip.opened.durable.image.seed
  derived : NativeHostReplay.Derived config tip.opened
  recordExact : DurableCheckpointCodec.recordFrame.encode (IntentRecord.ofIntent derived.intent) = record

/-- What the verified tip says of one proposed record. -/
inductive NextResult (config : NativeHost.Config) (expected : Context) {target : Durable}
    (tip : NativeHostReplay.Verified config target) (record : Bytes) where
  | granted (validated : ValidatedNext config expected tip record)
  /-- Never a record of this source on this tip: the consensus context is not this
  deployment's, the bytes are not a canonical record, or the tip's own derivation from the
  record's ingress is another record. The derivation is a function of the tip, so no retry on
  the same tip changes it. -/
  | invalid (detail : String)
  /-- The tip's admission did not grant the record's ingress now. A refusal and an
  unavailable dependency (the signature verifier, the history Reader) are not told apart:
  the caller may ask again. -/
  | refused (detail : String)

/-- Admit one proposed record at the verified tip: the same fresh native derivation the
ordered receiver runs before its append (`JointOrderedSourceReceiver.apply`), compared with
the proposed bytes. One admission, whatever the height of the tip. -/
def validateNext (config : NativeHost.Config) {target : Durable}
    (tip : NativeHostReplay.Verified config target) (expected : Context) (record : Bytes) :
    IO (NextResult config expected tip record) := do
  if contextPinned : config.jointConsensus = some expected then
    if expected.scope != digestStream.encode config.deployment.domain then
      return .invalid "source consensus scope mismatch"
    if anchorExact : expected.instanceBytes =
        anchorBytes config.genesisHeight tip.opened.durable.image.seed then
      let some decoded := DurableCheckpointCodec.recordFrame.decode record
        | return .invalid "noncanonical source record"
      match ← NativeHostReplay.deriveVerified tip decoded.event.canonicalBytes with
      | .error detail => return .refused detail
      | .ok derived =>
        if recordExact : DurableCheckpointCodec.recordFrame.encode
            (IntentRecord.ofIntent derived.intent) = record then
          return .granted ⟨contextPinned,anchorExact,derived,recordExact⟩
        else return .invalid "the tip derives another record from this ingress"
    else return .invalid "exact source genesis anchor mismatch"
  else return .invalid "consensus context is not deployment pinned"

/-- The engine prefix granted by native validation is exactly the source
history admitted by the real replay walk. It is not merely physically valid
raw journal bytes. -/
theorem validated_source_records {config : NativeHost.Config} {expected : Context} {block : Block}
    (v : Validated config expected block) :
    v.checked.opened.durable.image.accepted.map DurableCheckpointCodec.recordFrame.encode = sourceRecords block := by
  rw [v.checked.exactImage]
  exact v.recordsExact

/-- Inert engine slots do not change any source clock, authority, record or
charge. Only exact filtered-source equality transports this admission token;
raw BFT ancestry and certificate safety remain distinct engine obligations. -/
def Validated.stutter {config : NativeHost.Config} {expected : Context} {before after : Block}
    (v : Validated config expected before) (same : sourceRecords before = sourceRecords after) :
    Validated config expected after :=
  ⟨v.contextPinned,v.target,v.anchorExact,v.recordsExact.trans same,v.checked⟩

theorem validated_stutter_source_image {config : NativeHost.Config} {expected : Context}
    {before after : Block} (v : Validated config expected before)
    (same : sourceRecords before = sourceRecords after) :
    (v.stutter same).target.image = v.target.image := rfl

end Minidregg.Kernel.JointSourcePrefixValidation
