/- Closed operator-local neutral policy carry. The request never supplies
replacement data, grants or a claimed equivalence flag. It names retained
artifacts and independent operator custody; actual old audit, source-derived
mapping, native target validation and detached authorization are all required.
Publication still belongs to the quiesced, atomic infra switch. -/
import Compiler.CarriedSegmentIO
import Compiler.NeutralPolicyCarry
import Compiler.CarryConfiguration

namespace Minidregg.Compiler.NeutralCarriedSegmentIO

open Lean
open Minidregg.Kernel
open Minidregg.Kernel.CarriedSegment
open Minidregg.Compiler
open Minidregg.Compiler.CarriedSegmentIO

set_option autoImplicit false

private def liftResult {α : Type} (result : Except String α) : IO α := IO.ofExcept result
private def hex (bytes : List UInt8) : String :=
  let digit := fun n : Nat => Char.ofNat (if n < 10 then '0'.toNat + n else 'a'.toNat + n - 10)
  String.ofList (bytes.flatMap fun byte => [digit (byte.toNat / 16), digit (byte.toNat % 16)])

/-- A closed legacy cut cannot simultaneously change deployment parameters,
factory templates, tariffs, evaluators or observed runtime settings. Other
schema transitions require their own closed transformations and compositions.
The signed artifact pins identify the reviewed old and target implementations;
this is an authorized external cut, not a universal equivalence theorem. -/
def checkProfiles (source target : SourceCapsule) : IO Unit := do
  let sourceConfig ← liftResult (Json.parse (← IO.FS.readFile source.configuration))
  let targetConfig ← liftResult (Json.parse (← IO.FS.readFile target.configuration))
  liftResult (CarryConfiguration.checkLegacy sourceConfig targetConfig)
  let old ← liftResult (Json.parse (← IO.FS.readFile source.profile))
  let next ← liftResult (Json.parse (← IO.FS.readFile target.profile))
  let oldFields ← liftResult old.getObj?
  let nextFields ← liftResult next.getObj?
  if Json.obj (oldFields.erase "semantics") != Json.obj (nextFields.erase "semantics") then
    throw (IO.userError "neutral policy carry changes non-policy runtime profile fields")

private def checkTarget (config : NativeHost.Config) (target : SourceCapsule) : IO Unit := do
  checkCapsule target
  let actual : Identity := ⟨config.deployment.domain, config.profile.semantics, config.expectedSeed⟩
  if actual != target.identity then throw (IO.userError "carry target actual profile differs")
  -- The native receiver running this transformation is itself the pinned target.
  liftResult (← RetainedArtifactIO.checkedFile (← IO.appPath) (hex target.pins.host))
  liftResult (← RetainedArtifactIO.checkedFile config.storage.binary (hex target.pins.storageHelper))
  liftResult (← RetainedArtifactIO.checkedFile config.signature.binary (hex target.pins.signatureVerifier))
  if config.storage.root != target.storage.root || config.storage.key != target.storage.key then
    throw (IO.userError "carry target staging Store differs from selected capsule")
  let described ← withExecutionConfig target fun execution =>
    IO.Process.output { cmd := target.host.toString, args := #[execution.toString, "profile"] }
  if described.exitCode != 0 || described.stderr != "" ||
      described.stdout != (← IO.FS.readFile target.profile) then
    throw (IO.userError "carry target retained profile differs from actual runtime")

/-- Build a signing plan from the actual source cut. The detached signature is
collected only after the target endpoint has been derived; its value never
appears in the accepted event and therefore cannot make a root cycle. -/
def prepare (config : NativeHost.Config) (source target : SourceCapsule)
    (trustedOperator nonce : List UInt8) : IO (Except String (Prepared config)) := do
  try
    checkTarget config target
    let audited ← liftResult (← auditSource source)
    checkProfiles source target
    let plan ← liftResult (NeutralPolicyCarry.deriveStoreV2 config.deployment
      source.identity.semantics target.identity.semantics audited.durable)
    let body : Body := {
      source := source.identity
      cut := pointOf audited.durable
      sourceImage := imageDigest audited.durable.image
      sourceCapsule := source.pins
      target := target.identity
      targetCapsule := target.pins
      transformation := plan.transformation
      writes := writesDigest plan.changes
      originIndex := originIndexDigest audited.durable.image
      operatorPublicKey := trustedOperator
      nonce := nonce }
    return prepareDerived config audited trustedOperator body plan.changes
  catch error => return .error s!"neutral carry preparation refused: {error}"

def unsignedEdge (config : NativeHost.Config) (prepared : Prepared config) : EdgeSeal :=
  let old := Minidregg.Host.ReceiptContinuity.current prepared.source.durable
  let next := Minidregg.Host.ReceiptContinuity.current prepared.target.durable
  ⟨prepared.body, pointOf prepared.target.durable, old.siblings, next.siblings, []⟩

/-- Re-derive the entire plan at receipt of the detached seal. A changed source
cut, artifact, mapping, target endpoint or operator key refuses. Only exact
prepared history is staged; no active service pointer is changed here. -/
def receive (config : NativeHost.Config) (source target : SourceCapsule)
    (trustedOperator : List UInt8) (edge : EdgeSeal) :
    IO (Except String (NativeHost.Opened config)) := do
  let prepared ← prepare config source target trustedOperator edge.body.nonce
  let .ok prepared := prepared | return .error "neutral carry preparation refused"
  let expected := unsignedEdge config prepared
  if edge.body != expected.body || edge.targetStart != expected.targetStart ||
      edge.sourceSiblings != expected.sourceSiblings || edge.targetSiblings != expected.targetSiblings then
    return .error "neutral carry seal differs from the actual derived cut"
  let authorized ← authorizePrepared config prepared trustedOperator edge.signature
  let .ok authorized := authorized | return .error "neutral carry operator authorization refused"
  stageAuthorized config authorized

end Minidregg.Compiler.NeutralCarriedSegmentIO
