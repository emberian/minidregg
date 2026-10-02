/- A real Ed25519 custody probe of the source enrollment receiver on one
source-built genesis image. Test keys are public deterministic fixtures. -/
import Kernel.NativeHostGenesis
import Kernel.ParticipantKeyEnrollmentReceiver
import Kernel.NativeHost
import Compiler.NativeHostProfile

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent

namespace ParticipantKeyEnrollmentProbe

def require (label : String) (yes : Bool) : IO Unit :=
  unless yes do throw (IO.userError s!"FAIL participant enrollment: {label}")

def rejected {e α : Type} : Except e α → Bool
  | .error _ => true
  | .ok _ => false

def sign (binary : System.FilePath) (seed : Nat) (frame : List UInt8) :
    IO (List UInt8 × List UInt8) :=
  IO.FS.withTempDir fun directory => do
    let framePath := directory / "frame.bin"
    let keyPath := directory / "public.bin"
    let sigPath := directory / "signature.bin"
    IO.FS.writeBinFile framePath frame.toByteArray
    let output ← IO.Process.output
      { cmd := binary.toString
        args := #[toString seed, framePath.toString, keyPath.toString, sigPath.toString] }
    require "fixture signer" (output.exitCode == 0)
    pure ((← IO.FS.readBinFile keyPath).toList, (← IO.FS.readBinFile sigPath).toList)

def hostTemplate : NativeHost.Config where
  deployment := ⟨⟨8500⟩, 10, 11, 12⟩
  federation := ⟨9⟩
  template := ⟨⟨5⟩, 100000, 10000, 64⟩
  tariff := ⟨3, 2, 1, 0, 99, 0⟩
  genesisHeight := 10
  expectedSeed := ⟨0⟩
  storage := ⟨"unused-in-template", "unused-in-template"⟩
  signature := ⟨"unused-in-template"⟩

def profile := hostTemplate.profile

def genesis (sponsorKey : List UInt8) : NativeHostGenesis.Config where
  deployment := ⟨⟨8500⟩, 10, 11, 12⟩
  federation := ⟨9⟩
  tariff := ⟨3, 2, 1, 0, 99, 0⟩
  expectedSemantics := profile.semantics
  issuerEpoch := 2
  genesisHeight := 10
  factoryPredicate := .all []
  enrollments :=
    [⟨⟨7007, 2, 1, 7, sponsorKey, 0, 100, none⟩, 7,
      ⟨41⟩, ⟨44⟩, ⟨46⟩, 100, .all []⟩]
  factoryController := ⟨⟨7⟩, ⟨43⟩⟩
  meterAllowance := fun _ => 10000000

def isCapabilityPlane : CredentialAuthorityState.AuthorityPlane → Bool
  | .capability _ => true
  | _ => false

/-- The capability planes of an authority store: the addresses a grant occupies. -/
def capabilityAddresses (store : Store.Store CredentialAuthorityState.layout) :
    Finset (Store.Address CredentialAuthorityState.layout) :=
  store.support.filter (fun address => isCapabilityPlane address.1 = true)

def run (verifier signer storeBinary : System.FilePath) : IO Unit := do
  let (sponsorPublic, _) ← sign signer 7 []
  let (newPublic, _) ← sign signer 8 []
  let cfg := genesis sponsorPublic
  let built ← match NativeHostGenesis.build profile cfg with
    | .error reason => throw (IO.userError s!"genesis build: {repr reason}")
    | .ok value => pure value
  let durable ← match DurableReceiverIO.loadBytes ResourceBirthCodec.rootBytes
      (DurableReceiverCodec.encode built.image) with
    | .error reason => throw (IO.userError s!"genesis load: {reason}")
    | .ok value => pure value
  let directory ← match CredentialAuthorityDomainReceiver.loadDirectory durable with
    | none => throw (IO.userError "directory unavailable")
    | some value => pure value
  let factory ← match directory.directory.slots cfg.deployment.factoryId with
    | .absent => throw (IO.userError "factory absent")
    | .present value => pure value
  let authority ← match CredentialAuthorityDomainReceiver.loadDeployment cfg.deployment
      durable.snapshot with
    | none => throw (IO.userError "authority unavailable")
    | some value => pure value
  let key : KeyRecord := ⟨7008, 2, 1, 8, newPublic, 0, 100, none⟩
  let command : ParticipantKeyEnrollment.Command :=
    ⟨⟨7⟩, ⟨43⟩, 71, factory.payload.root, authority.snapshot.cell.root, key⟩
  let ambient : ParticipantKeyEnrollment.Ambient := ⟨cfg.federation, cfg.genesisHeight⟩
  let prepared ← match ParticipantKeyEnrollment.prepare cfg.deployment profile ambient
      durable command with
    | .error reason => throw (IO.userError s!"preparation: {repr reason}")
    | .ok value => pure value
  let selected ← match CredentialSignatureAdmission.signingHeader authority.snapshot
      (ParticipantKeyEnrollment.marker cfg.deployment.domain profile.semantics command)
      ⟨.program, ParticipantKeyEnrollment.request cfg.deployment authority.snapshot
        profile.semantics ambient command⟩ with
    | .error reason => throw (IO.userError s!"sponsor header: {repr reason}")
    | .ok value => pure value
  let (_, sponsorSignature) ← sign signer 7
    (CredentialSignedEnvelopeController.headerCodec.encode selected)
  let (_, possessionSignature) ← sign signer 8
    (ParticipantKeyEnrollment.possessionFrame cfg.deployment.domain profile.semantics command)
  let envelope := CredentialSignedEnvelopeController.envelopeCodec.encode
    ⟨selected, sponsorSignature⟩
  let ingressBytes := ParticipantKeyEnrollment.ingressCodec.encode
    ⟨ParticipantKeyEnrollment.commandCodec.encode command, envelope, possessionSignature, [], []⟩
  let some ingress := ParticipantKeyEnrollment.decodeIngress ingressBytes
    | throw (IO.userError "canonical ingress decode")
  let accepted ← match ← ParticipantKeyEnrollmentReceiver.admitDecodedNative cfg.deployment
      profile ambient durable ⟨verifier⟩ ingress with
    | .error reason => throw (IO.userError s!"signed admission: {repr reason}")
    | .ok value => pure value
  let post := DataSnapshot.install durable.snapshot
    (ParticipantKeyEnrollmentReceiver.intent accepted)
  let some updated := CredentialAuthorityDomainReceiver.loadDeployment cfg.deployment post
    | throw (IO.userError "installed authority unreadable")
  require "physical installed authority equals prepared semantic post"
    (decide (updated.snapshot.logical = prepared.candidate.post.logical))
  require "new key selected from canonical installed authority"
    (decide (updated.snapshot.currentSigningKey ⟨8⟩ = some key))
  require "enrollment minted no capability"
    (decide (capabilityAddresses updated.snapshot.logical =
      capabilityAddresses authority.snapshot.logical))
  let badKey := { command with key := { key with keyId := 7007 } }
  require "global key-id collision refuses"
    (rejected (ParticipantKeyEnrollment.prepare cfg.deployment profile ambient durable badKey))
  let badSubject := { command with key := { key with subject := 7 } }
  require "existing subject refuses"
    (rejected (ParticipantKeyEnrollment.prepare cfg.deployment profile ambient durable badSubject))
  let stale := { command with expectedAuthorityRoot :=
    ⟨command.expectedAuthorityRoot.value + 1⟩ }
  require "stale authority root refuses before signatures"
    (match ParticipantKeyEnrollment.prepare cfg.deployment profile ambient durable stale with
      | .error .staleAuthority => true | _ => false)
  let badPossessionBytes := ParticipantKeyEnrollment.ingressCodec.encode
    ⟨ParticipantKeyEnrollment.commandCodec.encode command, envelope, sponsorSignature, [], []⟩
  let some badPossession := ParticipantKeyEnrollment.decodeIngress badPossessionBytes
    | throw (IO.userError "bad possession ingress decode")
  require "new-key possession cannot be sponsor signature"
    (rejected (← ParticipantKeyEnrollmentReceiver.admitDecodedNative cfg.deployment profile ambient
      durable ⟨verifier⟩ badPossession))
  let denyCfg := { cfg with factoryPredicate := .eq "authority/operation/enroll-key" 0 }
  let denyBuilt ← match NativeHostGenesis.build profile denyCfg with
    | .error reason => throw (IO.userError s!"denying-law genesis: {repr reason}")
    | .ok value => pure value
  let denyDurable ← match DurableReceiverIO.loadBytes ResourceBirthCodec.rootBytes
      (DurableReceiverCodec.encode denyBuilt.image) with
    | .error reason => throw (IO.userError s!"denying-law load: {reason}")
    | .ok value => pure value
  let some denyDirectory := CredentialAuthorityDomainReceiver.loadDirectory denyDurable
    | throw (IO.userError "denying-law directory unavailable")
  let .present denyFactory := denyDirectory.directory.slots denyCfg.deployment.factoryId
    | throw (IO.userError "denying-law factory absent")
  let some denyAuthority := CredentialAuthorityDomainReceiver.loadDeployment
      denyCfg.deployment denyDurable.snapshot
    | throw (IO.userError "denying-law authority unavailable")
  let denyCommand : ParticipantKeyEnrollment.Command :=
    ⟨command.sponsor, command.control, command.nonce,
      denyFactory.payload.root, denyAuthority.snapshot.cell.root, command.key⟩
  let denyHeader ← match CredentialSignatureAdmission.signingHeader denyAuthority.snapshot
      (ParticipantKeyEnrollment.marker denyCfg.deployment.domain profile.semantics denyCommand)
      ⟨.program, ParticipantKeyEnrollment.request denyCfg.deployment denyAuthority.snapshot
        profile.semantics ambient denyCommand⟩ with
    | .error reason => throw (IO.userError s!"denying-law sponsor header: {repr reason}")
    | .ok value => pure value
  let (_, denySponsorSignature) ← sign signer 7
    (CredentialSignedEnvelopeController.headerCodec.encode denyHeader)
  let (_, denyPossessionSignature) ← sign signer 8
    (ParticipantKeyEnrollment.possessionFrame denyCfg.deployment.domain
      profile.semantics denyCommand)
  let denyBytes := ParticipantKeyEnrollment.ingressCodec.encode
    ⟨ParticipantKeyEnrollment.commandCodec.encode denyCommand,
      CredentialSignedEnvelopeController.envelopeCodec.encode
        ⟨denyHeader, denySponsorSignature⟩,
      denyPossessionSignature, [], []⟩
  let some denyIngress := ParticipantKeyEnrollment.decodeIngress denyBytes
    | throw (IO.userError "denying-law ingress decode")
  require "current factory law locks out enrollment even with both valid signatures"
    (match ← ParticipantKeyEnrollmentReceiver.admitDecodedNative denyCfg.deployment
        profile ambient denyDurable ⟨verifier⟩ denyIngress with
      | .error .policyRejected => true | _ => false)
  IO.FS.withTempDir fun directory => do
    let transport := (DurableReceiverIO.NativeConfig.mk storeBinary (directory / "store")).transport
    match ← DurableReceiverIO.bootstrap transport ResourceBirthCodec.rootBytes built.seed with
    | .error reason => throw (IO.userError s!"native bootstrap: {reason}")
    | .ok () => pure ()
    let host : NativeHost.Config :=
      { hostTemplate with expectedSeed := NativeHost.seedIdentity built.seed }
    let host := { host with storage := ⟨storeBinary, directory / "store"⟩ }
    let host := { host with signature := ⟨verifier⟩ }
    let initial ← match ← NativeHost.openExisting host with
      | .error reason => throw (IO.userError s!"initial native host open: {reason}")
      | .ok value => pure value
    let observation : NativeObservationCodec.Intent :=
      ⟨⟨7⟩, 70071, .query ⟨.object, cfg.deployment.factoryId, .resource⟩,
        [⟨.object, cfg.deployment.factoryId, ⟨46⟩⟩]⟩
    let challenge ← match NativeHost.challengeLoaded host initial
        (NativeObservationCodec.intentCodec.encode observation) with
      | .error reason => throw (IO.userError s!"factory observation challenge: {reason}")
      | .ok value => pure value
    let [observationHeader] := challenge.headers
      | throw (IO.userError "factory observation must have one signing header")
    let (_, observationSignature) ← sign signer 7 observationHeader
    let signedObservation := NativeObservationCodec.signedCodec.encode
      ⟨challenge, [observationSignature]⟩
    let plan ← match ← NativeHost.enrollmentPlanAuthorizedLoaded host initial signedObservation
        (ParticipantKeyEnrollment.commandCodec.encode command) with
      | .error reason => throw (IO.userError s!"authorized enrollment plan: {reason}")
      | .ok value => pure value
    require "authenticated factory observation releases exact two-signature plan"
      (plan.commandBytes == ParticipantKeyEnrollment.commandCodec.encode command &&
       plan.possessionHeader == ParticipantKeyEnrollment.possessionFrame
         cfg.deployment.domain profile.semantics command)
    let wrongSponsor := { command with sponsor := ⟨8⟩ }
    require "factory observation cannot disclose a different sponsor's plan"
      (rejected (← NativeHost.enrollmentPlanAuthorizedLoaded host initial signedObservation
        (ParticipantKeyEnrollment.commandCodec.encode wrongSponsor)))
    let old ← match ← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes with
      | .error reason => throw (IO.userError s!"native old load: {reason}")
      | .ok value => pure value
    match ← ParticipantKeyEnrollmentReceiver.receiveLoaded cfg.deployment profile ambient
        ⟨verifier⟩ transport old ingressBytes with
    | .confirmed .installed _ => pure ()
    | _ => throw (IO.userError "native first enrollment was not installed")
    let current ← match ← DurableReceiverIO.load transport ResourceBirthCodec.rootBytes with
      | .error reason => throw (IO.userError s!"native current load: {reason}")
      | .ok value => pure value
    require "one retained enrollment record" (current.image.accepted.length == 1)
    let opened ← match ← NativeHost.openExisting host with
      | .error reason => throw (IO.userError s!"full native historical replay: {reason}")
      | .ok value => pure value
    require "full host replay retained enrollment" (opened.durable.image.accepted.length == 1)
    let (fourthPublic, _) ← sign signer 9 []
    let nextKey : KeyRecord := ⟨7009, 2, 1, 9, fourthPublic, 0, 100, none⟩
    let nextCommand : ParticipantKeyEnrollment.Command :=
      ⟨⟨8⟩, ⟨46⟩, 72, factory.payload.root, opened.authority.snapshot.cell.root, nextKey⟩
    let nextAmbient : ParticipantKeyEnrollment.Ambient :=
      ⟨cfg.federation, cfg.genesisHeight + opened.durable.image.accepted.length⟩
    let nextHeader ← match CredentialSignatureAdmission.signingHeader
        opened.authority.snapshot
        (ParticipantKeyEnrollment.marker cfg.deployment.domain profile.semantics nextCommand)
        ⟨.program, ParticipantKeyEnrollment.request cfg.deployment
          opened.authority.snapshot profile.semantics nextAmbient nextCommand⟩ with
      | .error reason => throw (IO.userError s!"new subject key selection: {repr reason}")
      | .ok value => pure value
    let (_, nextSignature) ← sign signer 8
      (CredentialSignedEnvelopeController.headerCodec.encode nextHeader)
    require "full replay selects new key for a fresh signed request"
      (match ← CredentialSignatureAdmission.verifyNative ⟨verifier⟩
          opened.authority.snapshot
          (ParticipantKeyEnrollment.marker cfg.deployment.domain profile.semantics nextCommand)
          (ParticipantKeyEnrollment.request cfg.deployment opened.authority.snapshot
            profile.semantics nextAmbient nextCommand)
          (CredentialSignedEnvelopeController.envelopeCodec.encode
            ⟨nextHeader, nextSignature⟩) with
        | .ok _ => true | .error _ => false)
    let (_, nextPossession) ← sign signer 9
      (ParticipantKeyEnrollment.possessionFrame cfg.deployment.domain profile.semantics nextCommand)
    let nextBytes := ParticipantKeyEnrollment.ingressCodec.encode
      ⟨ParticipantKeyEnrollment.commandCodec.encode nextCommand,
        CredentialSignedEnvelopeController.envelopeCodec.encode ⟨nextHeader, nextSignature⟩,
        nextPossession, [], []⟩
    let some nextIngress := ParticipantKeyEnrollment.decodeIngress nextBytes
      | throw (IO.userError "fresh next ingress decode")
    require "enrolled key alone cannot sponsor another enrollment without grant"
      (match ← ParticipantKeyEnrollmentReceiver.admitDecodedNative cfg.deployment profile
          nextAmbient opened.durable ⟨verifier⟩ nextIngress with
        | .error .capabilityRejected => true | _ => false)
    require "exact historical lookup returns original receipt"
      (match ParticipantKeyEnrollmentReceiver.replay cfg.deployment.domain profile.semantics
          current ingress with
        | some (.ok _) => true | _ => false)
    match ← ParticipantKeyEnrollmentReceiver.receiveLoaded cfg.deployment profile ambient
        ⟨verifier⟩ transport current ingressBytes with
    | .confirmed .replayed _ => pure ()
    | _ => throw (IO.userError "native exact repeat was not replayed")
    match ← ParticipantKeyEnrollmentReceiver.receiveLoaded cfg.deployment profile ambient
        ⟨verifier⟩ transport current badPossessionBytes with
    | .transactionConflict => pure ()
    | _ => throw (IO.userError "native changed same-identity ingress was not conflict")
  IO.println "PASS participant key enrollment: signed observation gates exact two-signature plan, current-law sponsor and lockout, new-key possession, canonical authority post, no grants, collisions/stale root/wrong signer refuse, durable original/replay/conflict, full Host replay selects new signer but withholds ungranted control"

end ParticipantKeyEnrollmentProbe

def main (args : List String) : IO Unit := do
  match args with
  | [verifier, signer, store] => ParticipantKeyEnrollmentProbe.run verifier signer store
  | _ => throw (IO.userError "usage: probe-participant-key-enrollment VERIFIER SIGN-PROBE SQLITE-STORE")
