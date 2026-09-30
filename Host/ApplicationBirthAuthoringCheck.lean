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

private def grainOperator : NativeHost.Config :=
  { operator with grainBirthTariff := some ⟨5, 2⟩ }

private def genesisWithSemantics (semantics : Nat) : Json := object [
  ("domain", number 8501), ("factoryId", number 10),
  ("resourceBookId", number 11), ("authorityCatalogueId", number 12),
  ("federation", number 9), ("tariffBase", number 3),
  ("tariffPerBirth", number 2), ("tariffPerGrant", number 1),
  ("tariffPerInitialPayloadByte", number 0), ("collector", number 99),
  ("asset", number 0), ("expectedSemantics", number semantics),
  ("issuerEpoch", number 2), ("genesisHeight", number 10),
  ("factoryPredicate", emptyRule), ("enrollments", .arr #[]),
  ("factoryControllerSubject", number 8),
  ("factoryControllerCapability", number 53), ("meterAllowance", meter)]

private def genesis : Json := genesisWithSemantics operator.profile.semantics.value
private def compositeGenesis : Json := genesisWithSemantics grainOperator.profile.semantics.value

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

private def compositeRequest (specField : String) (spec : Json) : Json := object [
  ("genesis", compositeGenesis), ("template", template), ("creator", number 8),
  ("nonce", number 41000), (specField, spec),
  ("sourceCapabilities", .arr #[number 42]),
  ("funding", .arr #[]), ("feePayer", number 8)]

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

private def peer (task capability observe root : Nat) : Json := object [
  ("task", number task), ("capability", number capability),
  ("observeCapability", number observe), ("targetRoot", number root),
  ("before", object [("generation", number 1), ("status", number 1),
    ("remaining", number 100), ("reserved", number 3)])]

private def composite (fieldName : String) (typedBirth : Json) : Json :=
  let metered := object [
    ("tariff", object [("base", number 5), ("perBirth", number 2)]),
    (fieldName, typedBirth), ("authorityRoot", number 777),
    ("tool", peer 6000 6001 6002 6003),
    ("parent", peer 7000 7001 7002 7003)]
  object [("subject", number 8), ("nonce", number 41000),
    (if fieldName = "applicationBirth" then "applicationGrainBirth"
      else "applicationSessionGrainBirth", metered), ("grants", .arr #[])]

private def compositeShape (kind fieldName : String) (typedBirth : Json)
    (expectedBirths expectedGrants : Nat) : Bool :=
  match Minidregg.Host.Json.author kind (composite fieldName typedBirth) with
  | .error _ => false
  | .ok encoded =>
      match NativeObservationCodec.intentCodec.decode encoded with
      | some intent =>
          match intent.purpose with
          | .prepare (.birth bytes sourceCaps) =>
              match GrainResourceBirthHostCodec.sourceCodec.decode bytes with
              | some source =>
                  intent.subject == ⟨8⟩ && sourceCaps == [⟨42⟩] &&
                    source.birth.births.length == expectedBirths &&
                    source.birth.grants.length == expectedGrants &&
                    source.toolTask == 6000 && source.parentTask == 7000 &&
                    source.authorityRoot.value == 777
              | none => false
          | _ => false
      | none => false

private def mismatchedCompositeTariff : Json :=
  let mismatched := object [
    ("genesis", compositeGenesis), ("template", template), ("creator", number 8),
    ("nonce", number 41000), ("application", application),
    ("sourceCapabilities", .arr #[number 42]), ("funding", .arr #[]),
    ("feePayer", number 8),
    ("grainBirthTariff", object [("base", number 6), ("perBirth", number 2)])]
  composite "applicationBirth" mismatched

private def custodyOperator : NativeHost.Config :=
  { grainOperator with completionCustodianKey := some (List.replicate 32 7) }

private def configuredRequest (fieldName : String) (spec : Json) : Json := object [
  ("genesis", genesisWithSemantics custodyOperator.profile.semantics.value),
  ("template", template), ("creator", number 8), ("nonce", number 41000),
  (fieldName, spec), ("sourceCapabilities", .arr #[number 42]),
  ("funding", .arr #[]), ("feePayer", number 8)]

private def wrapIntent (fieldName : String) (source : Json) : Json := object [
  ("subject", number 8), ("nonce", number 41000),
  (fieldName, source), ("grants", .arr #[])]

private def configuredChecks : IO Unit := do
  let app := configuredRequest "application" (application)
  let web := configuredRequest "session" (session)
  let resource := object [("kind", .str "object"), ("storage", .str "content"),
    ("target", number 8300), ("owner", number 8),
    ("ownerCapability", number 85), ("controlCapability", number 86),
    ("predicate", emptyRule)]
  let plain := configuredRequest "resources" (.arr #[resource])
  let grain := object [("tariff", object [("base", number 5), ("perBirth", number 2)]),
    ("birth", plain), ("authorityRoot", number 777),
    ("tool", peer 6000 6001 6002 6003), ("parent", peer 7000 7001 7002 7003)]
  for (kind, source) in [
      ("birth", plain), ("birth-intent", wrapIntent "birth" plain),
      ("grain-birth", grain), ("grain-birth-intent", wrapIntent "grainBirth" grain),
      ("application-birth", app),
      ("application-birth-intent", wrapIntent "applicationBirth" app),
      ("application-session-birth", web),
      ("application-session-birth-intent", wrapIntent "applicationSessionBirth" web),
      ("application-grain-birth-intent", composite "applicationBirth" app),
      ("application-session-grain-birth-intent", composite "applicationSessionBirth" web)] do
    match Minidregg.Host.Json.author kind source (some custodyOperator) with
    | .error reason => throw (IO.userError s!"configured {kind}: {reason}")
    | .ok _ => pure ()
    -- Losing the configured custodian must reproduce the old refusal.
    match Minidregg.Host.Json.author kind source (some grainOperator) with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"{kind}: accepted wrong custodian profile")
  for changed in [
      { custodyOperator with federation := ⟨10⟩ },
      { custodyOperator with genesisHeight := 11 },
      { custodyOperator with template := ⟨⟨6⟩, 100000, 10000⟩ },
      { custodyOperator with tariff := ⟨4, 2, 1, 0, 99, 0⟩ },
      { custodyOperator with deployment := ⟨⟨8502⟩, 10, 11, 12⟩ },
      { custodyOperator with completionCustodianKey := some (List.replicate 32 8) }] do
    match Minidregg.Host.Json.author "application-birth" app (some changed) with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "accepted mismatched deployment profile")
  match Minidregg.Host.Json.author "application-grain-birth-intent"
      (composite "applicationBirth" app)
      (some { custodyOperator with grainBirthTariff := some ⟨6, 2⟩ }) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "accepted mismatched enclosing tariff")
  let (context, _) ← IO.ofExcept <| Minidregg.Host.Json.applicationBirthContext
    "$" "application" app none (some 42) (some custodyOperator)
  unless context.height == 42 && context.profile.semantics == custodyOperator.profile.semantics do
    throw (IO.userError "loaded birth context lost current height or deployed semantics")
  IO.println "configured birth routes: 10 positive, 10 wrong-custodian refusals, 7 mismatches, loaded context: ok"

def main : IO Unit := do
  let app := request "application" (application)
  let web := request "session" (session)
  let appComposite := composite "applicationBirth" (compositeRequest "application" (application))
  match Minidregg.Host.Json.author "application-grain-birth-intent" appComposite with
  | .error detail =>
      throw (IO.userError s!"application composite source refused: {detail}")
  | .ok _ => pure ()
  for (label, passed) in [
      ("application bare", shape "application-birth" app 3 6 3),
      ("session bare", shape "application-session-birth" web 2 4 2),
      ("application bare intent", intentShape "application-birth-intent" "applicationBirth" app 3),
      ("session bare intent", intentShape "application-session-birth-intent" "applicationSessionBirth" web 2),
      ("application composite", compositeShape "application-grain-birth-intent" "applicationBirth"
        (compositeRequest "application" (application)) 3 6),
      ("session composite", compositeShape "application-session-grain-birth-intent"
        "applicationSessionBirth" (compositeRequest "session" (session)) 2 4),
      ("composite tariff mismatch", refused "application-grain-birth-intent" mismatchedCompositeTariff),
      ("repeated source capability", repeatedSourceCapabilityPreserved),
      ("duplicate app target", refused "application-birth" (request "application" (application true))),
      ("duplicate app capability", refused "application-birth" (request "application" (application false true))),
      ("invalid session kind", refused "application-session-birth" (request "session" (session "invalid")))] do
    unless passed do throw (IO.userError s!"application birth JSON authoring: {label} failed")
  IO.println "application birth JSON authoring: ok"
  configuredChecks

#eval main

end Minidregg.Host.ApplicationBirthAuthoringCheck
