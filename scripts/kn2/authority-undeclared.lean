/- KN2-STORE-OPEN executed probe for the light authority families (delegate, revoke):
a key the request's basis did not declare is refused BY NAME on a real deployment
Store, never read as absent or unspent.

The Store is the deployment's pinned genesis (`Assurance.NativeAcceptedFixtureData`),
bootstrapped and opened as the Host opens a served Store (`NativeHostLight.start`);
every basis is `Light.basis` of that opening. The ingresses are hand-built and only
need to decode: every refusal below happens before any state is consulted.

 delegate:
  1. a basis without the transaction id: `CapabilityDelegationReceiver.replay` is
     `undeclared` (the Host refuses `undeclaredTransaction`); with it: `fresh`;
  2. a basis without the marker's nullifier: `CapabilityDelegationController.prepare`
     is exactly `.error .undeclaredMarker` (refused before any state read); with it,
     the refusal is a state one, never `undeclaredMarker`;
 revoke:
  3. a basis without the transaction id: `CapabilityRevocationReceiver.replay` is
     `undeclared`; with it: `fresh`.
The positive control end to end is the journeys (J3 delegates, JPRIV1 kicks = revokes)
on this tree's Host.

Usage: lake env lean --run scripts/kn2/authority-undeclared.lean STORE-HELPER -/
import Assurance.NativeAcceptedFixtureData
import Kernel.NativeHostLight
import Kernel.CapabilityDelegationReceiver
import Kernel.CapabilityRevocationReceiver
import Kernel.ObjectiveBendNativeAdmission

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Kernel
open Minidregg.Kernel.NativeHost
open Minidregg.Compiler
open Minidregg.Compiler.DurableCheckpointCodec
open Minidregg.Assurance.NativeAcceptedFixtureData

namespace AuthorityUndeclared

def hexBytes (text : String) : List UInt8 :=
  go text.toList []
where
  nibble (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  go : List Char → List UInt8 → List UInt8
    | a :: b :: rest, acc => go rest (UInt8.ofNat (nibble a * 16 + nibble b) :: acc)
    | _, acc => acc.reverse

def config (storage : DurableReceiverIO.NativeConfig) : NativeHost.Config where
  deployment := ⟨⟨pinDomain⟩, pinFactoryId, pinResourceBookId, pinAuthorityCellId⟩
  federation := ⟨pinFederation⟩
  template := ⟨⟨pinIssuer⟩, pinOwnerBudget, pinLifetime, CanonicalRuntimeProfile.defaultBirthSlack⟩
  tariff := ⟨pinTariffBase, pinTariffPerBirth, pinTariffPerGrant, pinTariffPerInitialPayloadByte,
    pinCollector, pinAsset⟩
  genesisHeight := pinGenesisHeight
  expectedSeed := ⟨pinExpectedSeed⟩
  storage := storage
  signature := ⟨""⟩
  invocationBindings := (ObjectiveBendNativeAdmission.decodePolicy (hexBytes pinObjectivePolicyHex)).map
    fun policy => [(.objectiveMethod, ObjectiveBendNativeAdmission.encodePolicy policy)]

def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"FAIL authority undeclared probe: {label}")

def verdict {R : Type} : ServedBasis.Ground.Replay R → String
  | .undeclared => "undeclared"
  | .fresh => "fresh"
  | .original _ => "original"
  | .conflict => "conflict"

/-- A signed envelope that decodes (its signature is never checked here). -/
def envelope : List UInt8 :=
  CredentialSignatureAdmission.canonicalEnvelopeCodec.encode
    ⟨⟨1, [], 0, 0, 0, 0, [], [], 0⟩, []⟩

def child : Capability .object where
  id := ⟨900⟩
  root := ⟨1⟩
  parent := some ⟨1⟩
  issuer := ⟨pinIssuer⟩
  holder := .bearer
  scope := { targets := .explicit ∅, verbs := ∅, maxCost := 0 }
  notBefore := 0
  notAfter := 0
  issuerEpoch := 0
  policyId := ⟨20⟩
  policyEpoch := 0
  ancestors := ∅
  channels := ∅

def delegateCommand : CapabilityDelegationController.Command .object where
  subject := ⟨1⟩
  nonce := 7
  expectedTargetRoot := ⟨0⟩
  declaration := { child := child, parentId := ⟨1⟩, target := ⟨20⟩, operationNullifier := 0 }

def revokeCommand : CapabilityRevocationController.Command .object where
  subject := ⟨1⟩
  nonce := 7
  target := ⟨20⟩
  victimKind := .object
  capability := ⟨900⟩
  controlCapability := ⟨1⟩
  expectedTargetRoot := ⟨0⟩
  expectedAuthorityRoot := ⟨0⟩

def run (binary : System.FilePath) (directory : System.FilePath) : IO Unit := do
  IO.FS.writeBinFile (directory / "key") ((List.range 32).map (fun i => UInt8.ofNat (i * 7 + 3))).toByteArray
  let cfg := config { binary := binary, root := directory / "store", key := directory / "key", checkpointEvery := 16 }
  let some seed := seedFrame.decode (hexBytes seedHex)
    | throw (IO.userError "FAIL the fixture seed no longer decodes")
  match ← DurableReceiverIO.bootstrap cfg.transport ResourceBirthCodec.rootBytes seed with
  | .error detail => throw (IO.userError s!"FAIL bootstrap: {detail}")
  | .ok () => pure ()
  let light ← match ← NativeHostLight.start cfg with
    | .ok light => pure light
    | .error detail => throw (IO.userError s!"FAIL light open of the pinned genesis: {detail}")
  let groundOf (keys : DurableView.Keys) (label : String) : IO (ServedBasis.Ground cfg.deployment) := do
    match ← light.basis keys with
    | .ok basis => pure (.ofBasis basis)
    | .error detail => throw (IO.userError s!"FAIL {label} basis: {detail}")
  let domain := cfg.deployment.domain
  let semantics := cfg.profile.semantics
  -- delegate
  let some delegation := CapabilityDelegationReceiver.decodeIngress
      (CapabilityDelegationReceiver.ingressCodec.encode
        ⟨CapabilityDelegationController.commandCodec.encode ⟨.object, delegateCommand⟩, envelope⟩)
    | throw (IO.userError "FAIL the delegation ingress does not decode")
  let dKeys := CapabilityDelegationReceiver.keys domain semantics delegation
  let dAll ← groundOf dKeys "delegation"
  let dNoTx ← groundOf ⟨[], dKeys.nullifiers⟩ "delegation without its transaction id"
  let dNoMarker ← groundOf ⟨dKeys.transactions, []⟩ "delegation without its marker"
  let dReplay := verdict (CapabilityDelegationReceiver.replay domain semantics dNoTx delegation)
  require s!"an undeclared delegation transaction id is `undeclared` (got {dReplay})" (dReplay == "undeclared")
  IO.println s!"refused as expected (delegate, undeclared transaction): replay {dReplay}"
  let dFresh := verdict (CapabilityDelegationReceiver.replay domain semantics dAll delegation)
  require s!"a declared, unrecorded delegation is `fresh` (got {dFresh})" (dFresh == "fresh")
  IO.println s!"control (delegate, declared transaction): replay {dFresh}"
  let ambient : CapabilityDelegationController.Ambient := ⟨cfg.federation, cfg.genesisHeight + dAll.height⟩
  match CapabilityDelegationController.prepare cfg.deployment cfg.profile ambient dNoMarker delegation.command.2 with
  | .error .undeclaredMarker => IO.println "refused as expected (delegate, undeclared marker): undeclaredMarker"
  | .error other => throw (IO.userError s!"FAIL a marker-less delegation refused otherwise: {repr other}")
  | .ok _ => throw (IO.userError "FAIL an undeclared delegation marker prepared")
  match CapabilityDelegationController.prepare cfg.deployment cfg.profile ambient dAll delegation.command.2 with
  | .error .undeclaredMarker => throw (IO.userError "FAIL a declared delegation marker was refused as undeclared")
  | .error other => IO.println s!"control (delegate, declared marker): refused on state, {repr other}"
  | .ok _ => IO.println "control (delegate, declared marker): prepares"
  -- revoke
  let some revocation := CapabilityRevocationReceiver.decodeIngress
      (CapabilityRevocationReceiver.ingressCodec.encode
        ⟨CapabilityRevocationController.commandCodec.encode ⟨.object, revokeCommand⟩, envelope⟩)
    | throw (IO.userError "FAIL the revocation ingress does not decode")
  let rKeys := CapabilityRevocationReceiver.keys domain semantics revocation
  let rAll ← groundOf rKeys "revocation"
  let rNoTx ← groundOf ⟨[], rKeys.nullifiers⟩ "revocation without its transaction id"
  let rReplay := verdict (CapabilityRevocationReceiver.replay domain semantics rNoTx revocation)
  require s!"an undeclared revocation transaction id is `undeclared` (got {rReplay})" (rReplay == "undeclared")
  IO.println s!"refused as expected (revoke, undeclared transaction): replay {rReplay}"
  let rFresh := verdict (CapabilityRevocationReceiver.replay domain semantics rAll revocation)
  require s!"a declared, unrecorded revocation is `fresh` (got {rFresh})" (rFresh == "fresh")
  IO.println s!"control (revoke, declared transaction): replay {rFresh}"
  IO.println "PASS authority undeclared: delegate (transaction id, marker) and revoke (transaction id) each refused by name"

end AuthorityUndeclared

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [binary] => IO.FS.withTempDir (AuthorityUndeclared.run binary)
  | _ => throw (IO.userError "usage: lean --run scripts/kn2/authority-undeclared.lean STORE-HELPER")
