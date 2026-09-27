/- Narrow executable check for the source-owned application birth JSON routes.
Run after compiling Host.Json in an isolated current Lean snapshot. -/
import Host.Json
import Kernel.ApplicationGrainBirth
import Kernel.ApplicationGrainSessionBirth

namespace Minidregg.Host.ApplicationBirthAuthoringCheck
open Lean
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Theory.CellRegistry
open Minidregg.Kernel

private def number (value : Nat) : Json := .str (toString value)
private def object (fields : List (String × Json)) : Json := .mkObj fields
private def emptyRule : Json := object [("type", .str "all"), ("predicates", .arr #[])]
private def meter : Json := object <| ["incidences", "turnBytes", "memoryTouches",
  "witnessBytes", "proofWork", "storageBytes", "networkBytes", "sideEffectCount",
  "feeDebit", "leaseByteBlocks"].map fun key => (key, number 100000)

private def operator : NativeHost.Config := {
  deployment := ⟨⟨8501⟩, 10, 11, 12⟩
  federation := ⟨9⟩
  template := ⟨⟨5⟩, 100000, 10000⟩
  tariff := ⟨3, 2, 1, 0, 99, 0⟩
  genesisHeight := 10
  expectedSeed := ⟨0⟩
  storage := ⟨"", ""⟩
  signature := ⟨""⟩ }

private def genesis : Json := object [
  ("domain", number 8501), ("factoryId", number 10),
  ("resourceBookId", number 11), ("authorityCatalogueId", number 12),
  ("federation", number 9), ("tariffBase", number 3),
  ("tariffPerBirth", number 2), ("tariffPerGrant", number 1),
  ("tariffPerInitialPayloadByte", number 0), ("collector", number 99),
  ("asset", number 0), ("expectedSemantics", number operator.profile.semantics.value),
  ("issuerEpoch", number 2), ("genesisHeight", number 10),
  ("factoryPredicate", emptyRule), ("enrollments", .arr #[]),
  ("factoryControllerSubject", number 8),
  ("factoryControllerCapability", number 53), ("meterAllowance", meter)]

private def template : Json := object [
  ("issuer", number 5), ("ownerBudget", number 100000), ("lifetime", number 10000)]

private def application (sameManifest : Bool := false) (sameCapability : Bool := false) : Json :=
  object [("app", number 8300), ("packageManifest", number (if sameManifest then 8300 else 8301)),
    ("snapshotManifest", number 8302), ("owner", number 8),
    ("appOwnerCapability", number 85),
    ("appControlCapability", number (if sameCapability then 85 else 86)),
    ("packageOwnerCapability", number 87), ("packageControlCapability", number 88),
    ("snapshotOwnerCapability", number 89), ("snapshotControlCapability", number 90)]

private def session (kind : String := "web") : Json := object [
  ("app", number 8300), ("session", number 8400), ("descriptor", number 8401),
  ("participant", number 8), ("kind", .str kind),
  ("sessionOwnerCapability", number 91), ("sessionControlCapability", number 92),
  ("descriptorOwnerCapability", number 93), ("descriptorControlCapability", number 94)]

private def requestWithSources (specField : String) (spec : Json)
    (sources : Array Json) : Json := object [
  ("genesis", genesis), ("template", template), ("creator", number 8),
  ("nonce", number 41000), (specField, spec),
  ("sourceCapabilities", .arr sources),
  ("funding", .arr #[]), ("feePayer", number 8)]

private def request (specField : String) (spec : Json) : Json :=
  requestWithSources specField spec #[number 42]

private def shape (kind : String) (source : Json)
    (births grants policies : Nat) : Bool :=
  match Minidregg.Host.Json.author kind source with
  | .error _ => false
  | .ok encoded =>
      match draftCodec.decode encoded with
      | some (.birth bytes sourceCaps) =>
          match (ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).decode bytes with
          | some descriptor =>
              sourceCaps == [⟨42⟩] && descriptor.births.length == births &&
              descriptor.grants.length == grants &&
              descriptor.initialPolicies.length == policies &&
              descriptor.fee.amount == descriptor.quotedFee operator.tariff
          | none => false
      | _ => false

private def refused (kind : String) (source : Json) : Bool :=
  match Minidregg.Host.Json.author kind source with
  | .error _ => true
  | .ok _ => false

private def repeatedSourceCapabilityPreserved : Bool :=
  let input := requestWithSources "application" (application) #[number 42, number 42]
  match Minidregg.Host.Json.author "application-birth" input with
  | .error _ => false
  | .ok encoded =>
      match draftCodec.decode encoded with
      | some (.birth _ selected) => selected == [⟨42⟩, ⟨42⟩]
      | _ => false

private def intentShape (kind fieldName : String) (birth : Json)
    (expectedBirths : Nat) : Bool :=
  let wrapped := object [("subject", number 8), ("nonce", number 41000),
    (fieldName, birth), ("grants", .arr #[])]
  match Minidregg.Host.Json.author kind wrapped with
  | .error _ => false
  | .ok encoded =>
      match NativeObservationCodec.intentCodec.decode encoded with
      | some intent =>
          match intent.purpose with
          | .prepare (.birth descriptorBytes sourceCaps) =>
              match (ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).decode
                  descriptorBytes with
              | some descriptor =>
                  intent.subject == ⟨8⟩ && sourceCaps == [⟨42⟩] &&
                    descriptor.births.length == expectedBirths
              | none => false
          | _ => false
      | none => false

def main : IO Unit := do
  let app := request "application" (application)
  let web := request "session" (session)
  unless shape "application-birth" app 3 6 3 &&
      shape "application-session-birth" web 2 4 2 &&
      intentShape "application-birth-intent" "applicationBirth" app 3 &&
      intentShape "application-session-birth-intent" "applicationSessionBirth" web 2 &&
      repeatedSourceCapabilityPreserved &&
      refused "application-birth" (request "application" (application true)) &&
      refused "application-birth" (request "application" (application false true)) &&
      refused "application-session-birth" (request "session" (session "invalid")) do
    throw (IO.userError "application birth JSON authoring check failed")
  IO.println "application birth JSON authoring: ok"

end Minidregg.Host.ApplicationBirthAuthoringCheck

def main : IO Unit := Minidregg.Host.ApplicationBirthAuthoringCheck.main
