/- Native historical-prefix validation for the common source log.
The proposed parent can be prepared rather than physically committed. This
module reconstructs its exact records in memory, then executes the real native
source walk at every original height. It never appends to physical storage.
-/
import Kernel.NativeHostReplay
import Compiler.GenericSimplexSourceAnchor
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
      if DurableCheckpointCodec.recordFrame.encode record != bytes then none else
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
      let image : Image := ⟨seed,records⟩
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
                  simpa only [imageExact] using anchorExact
                return .accepted ⟨contextPinned,target,pinnedAnchor,recordsExact,checked⟩
          else return .rejected "source record frame roundtrip mismatch"
    else return .rejected "exact source genesis anchor mismatch"
  else return .rejected "consensus context is not deployment pinned"

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
