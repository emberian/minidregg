/-
Run with two supplied 32-byte Ed25519 public-key files. This probe never
generates, imports, or stores private keys. Public keys are enrollment inputs;
the acceptance below does not claim proof of their corresponding possession.
-/
import Kernel.NativeHostGenesis
import Compiler.NativeHostProfile

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.NativeHostGenesis

namespace NativeHostGenesisProbe

def profile := NativeHostProfile.profile ⟨⟨5⟩, 100000, 10000⟩
  "genesis-acceptance-probe/no-deployment-claim".toUTF8.toList

def key (subject : Nat) (bytes : List UInt8) : KeyRecord :=
  ⟨7000 + subject, 2, CredentialSignatureAdmission.ed25519Algorithm,
    subject, bytes, 0, 100, false⟩

def config (alice bob : List UInt8) : Config where
  deployment := ⟨⟨8500⟩, 10, 11, 12⟩
  federation := ⟨9⟩
  tariff := ⟨3, 2, 1, 0, 99, 0⟩
  expectedSemantics := profile.semantics
  issuerEpoch := 2
  genesisHeight := 10
  factoryPredicate := .any [.memberOf "request/creator" [7, 8], .eq "request/subject" 7]
  enrollments :=
    [⟨key 7 alice, 7, ⟨41⟩, ⟨44⟩, ⟨46⟩, 100, .all []⟩,
     ⟨key 8 bob, 8, ⟨42⟩, ⟨45⟩, ⟨47⟩, 200, .all []⟩]
  factoryController := ⟨⟨7⟩, ⟨43⟩⟩
  meterAllowance := fun _ => 10000000

def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"FAIL native genesis: {label}")

def refused (label : String) (configuration : Config) : IO Unit := do
  match build profile configuration with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"FAIL native genesis accepted {label}")

def run (alice bob : List UInt8) : IO Unit := do
  let cfg := config alice bob
  let cfgBytes := configCodec.encode cfg
  require "strict source-config roundtrip"
    (configCodec.decode cfgBytes).isSome
  require "strict source-config trailing-byte refusal"
    (configCodec.decode (cfgBytes ++ [0])).isNone
  let built ← match build profile cfg with
    | .error error => throw (IO.userError s!"FAIL native genesis build: {repr error}")
    | .ok built => pure built
  require "zero accepted history" built.image.accepted.isEmpty
  require "all supplied keys in actual loaded authority"
    (built.authority.snapshot.authState.subjectKeyEpoch ⟨7⟩ == 2 &&
     built.authority.snapshot.authState.subjectKeyEpoch ⟨8⟩ == 2 &&
     decide (built.authority.snapshot.logical.fields (.subjectKey ⟨7⟩ 2) = some (key 7 alice)) &&
     decide (built.authority.snapshot.logical.fields (.subjectKey ⟨8⟩ 2) = some (key 8 bob)))
  require "explicit conserved allocations"
    (cfg.initialBook.balance 7 0 == 100 && cfg.initialBook.balance 8 0 == 200 &&
     cfg.initialBook.balance 0 0 == -300 && cfg.initialBook.balance 99 0 == 0 &&
     cfg.initialBook.totalAsset 0 == 0)
  require "seed restores exact actual receiving image"
    (built.image.restore ResourceBirthCodec.rootBytes).isSome
  let encoded := DurableReceiverCodec.encode built.image
  let reopened ← match DurableReceiverIO.loadBytes ResourceBirthCodec.rootBytes encoded with
    | .ok loaded => pure loaded
    | .error message => throw (IO.userError s!"FAIL reopen: {message}")
  require "reopened complete authority"
    (CredentialAuthorityDomainReceiver.load cfg.deployment.authorityAnchor reopened.snapshot).isSome
  require "reopened full physical directory"
    (CredentialAuthorityDomainReceiver.loadDirectory reopened).isSome
  let [first, second] := cfg.enrollments
    | throw (IO.userError "FAIL native genesis: expected two probe enrollments")
  refused "profile mismatch" { cfg with expectedSemantics := ⟨cfg.expectedSemantics.value + 1⟩ }
  refused "duplicate subject" { cfg with enrollments := [first, { second with key :=
    { second.key with subject := first.key.subject } }] }
  refused "duplicate public key" { cfg with enrollments := [first, { second with key :=
    { second.key with publicKey := first.key.publicKey } }] }
  refused "duplicate key identifier" { cfg with enrollments := [first, { second with key :=
    { second.key with keyId := first.key.keyId } }] }
  refused "duplicate account" { cfg with enrollments := [first, { second with accountId := first.accountId }] }
  refused "duplicate capability" { cfg with enrollments := [first, { second with
    spendCapabilityId := cfg.factoryController.capabilityId }] }
  refused "unfunded anonymous controller" { cfg with factoryController := ⟨⟨123456⟩, ⟨43⟩⟩ }
  refused "revoked key" { cfg with enrollments := [{ first with key := { first.key with revoked := true } }, second] }
  refused "inactive key" { cfg with enrollments := [{ first with key := { first.key with activeFrom := 2 } }, second] }
  refused "wrong key algorithm" { cfg with enrollments := [{ first with key := { first.key with algorithm := 100 } }, second] }
  refused "short key" { cfg with enrollments := [{ first with key := { first.key with publicKey := [] } }, second] }
  refused "funding the issuer well as an ordinary account" { cfg with tariff := { cfg.tariff with asset := first.accountId } }
  let sourceId := PolicySourceCell.physicalId cfg.deployment.domain
    (PolicyRecordCodec.digest (factoryPolicy profile cfg))
  refused "policy-source/catalogue physical collision"
    { cfg with deployment := { cfg.deployment with authorityCatalogueId := sourceId } }
  IO.println "PASS native genesis: supplied public keys, source-derived authority/policies/grants, conserved explicit budget, canonical zero-history restore; malformed configuration and physical alias refusal"

end NativeHostGenesisProbe

def main (args : List String) : IO Unit := do
  match args with
  | [alicePath, bobPath] =>
      NativeHostGenesisProbe.run (← IO.FS.readBinFile alicePath).toList
        (← IO.FS.readBinFile bobPath).toList
  | _ => throw (IO.userError "usage: probe-native-host-genesis <alice-public-key.bin> <bob-public-key.bin>")

#print axioms Minidregg.Kernel.NativeHostGenesis.fund_conserves
#print axioms Minidregg.Kernel.NativeHostGenesis.initialBook_conserved
#print axioms Minidregg.Kernel.NativeHostGenesis.Built.restore
#print axioms Minidregg.Kernel.NativeHostGenesis.incompatible_profile_refused
#print axioms Minidregg.Kernel.NativeHostGenesis.duplicate_subjects_refused
#print axioms Minidregg.Kernel.NativeHostGenesis.config_canonical
