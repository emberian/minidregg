/- Focused source-regression check; synthetic signed calls are not admissions. -/
import Host.Main

namespace Minidregg.Host.ProviderServicesAudit

open Lean
open Minidregg.Host
open Minidregg.Kernel
open Minidregg.Compiler.NativeHostCodec

set_option autoImplicit false

private def rate : Json := Json.mkObj [
  ("perOp", toJson "1"), ("inputMicroPerMillion", toJson "1"),
  ("outputMicroPerMillion", toJson "1")]

/-- A v2 tariff by route (`ProviderUsage.parseTariff`): user pays only its per-op fee. -/
private def tariff : Json := Json.mkObj [
  ("version", toJson "2"), ("model", toJson "fixture"),
  ("routes", Json.mkObj [("user", Json.mkObj [("perOp", toJson "4")]),
    ("pool", rate), ("homelab", rate)])]

private def service (resource : Nat) : ProviderMeteringSettings :=
  ⟨resource, tariff⟩

private def refused {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def legacy : AgentDispatchFixedSettings :=
  { issueIndex := 1, ticketResource := 2, packageManifest := 3,
    snapshotManifest := 4, sessionObserve := 5, manifestObserve := 6,
    enrollmentObserve := 7, parentTask := 8, parentCapability := 9,
    parentObserve := 10, purseTask := 20, purseCapability := 21,
    purseObserve := 22, payerSubject := 23, reserveAmount := 5,
    maximumCharge := 5 }

private def lifetime (grant : Nat) (index : Nat) : AgentLifetimeDispatchFixedSettings :=
  ⟨legacy, index, grant, 24⟩

private def call (targets : List Nat) : List UInt8 := Id.run do
  let target := fun resource : Nat =>
    ({ kind := .object, target := resource, capability := ⟨1⟩,
       schemaVersion := 1, expectedTargetRoot := ⟨2⟩,
       payload := .scalar [] } : DeclaredResourceController.Target)
  let command : DeclaredResourceController.Command :=
    { subject := ⟨3⟩,
      nonce := 5, targets := targets.map target }
  let signed : DeclaredResourceController.SignedCommand :=
    { commandBytes := DeclaredResourceController.commandCodec.encode command,
      targetEnvelopes := [], observeEnvelopes := [], authorityEnvelope := [] }
  return callCodec.encode (.invoke signed)

private def pair (first second : List UInt8) : List UInt8 :=
  let width := first.length
  [UInt8.ofNat (width % 256), UInt8.ofNat (width / 256 % 256),
    UInt8.ofNat (width / 65536 % 256), UInt8.ofNat (width / 16777216 % 256)] ++
    first ++ second

private def quoteFrame (metadata : String) (model : String := "fixture") : List UInt8 :=
  let request := ("{\"model\":\"" ++ model ++ "\"}").toUTF8.toList
  let response :=
    "{\"id\":\"a\",\"object\":\"chat.completion\",\"model\":\"fixture\",\"choices\":[{\"index\":0,\"finish_reason\":\"stop\"}],\"usage\":{\"prompt_tokens\":1,\"completion_tokens\":2,\"total_tokens\":3}}".toUTF8.toList
  pair metadata.toUTF8.toList (pair request response)

def check : IO Unit := do
  unless (checkedProviderServices [service 7950, service 7951]).isOk do
    throw (IO.userError "two distinct providers refused")
  unless refused (checkedProviderServices [service 7950, service 7950]) do
    throw (IO.userError "duplicate provider ID accepted")
  unless refused (checkedProviderServices [service 0]) do
    throw (IO.userError "zero provider ID accepted")
  unless providerFromReserveCall [7950, 7951] (call [7950]) == .ok 7950 do
    throw (IO.userError "signed current provider target not selected")
  unless refused (providerFromReserveCall [7950, 7951] (call [7952])) do
    throw (IO.userError "wrong signed provider target accepted")
  unless refused (providerFromReserveCall [7950, 7951] (call [7950, 7951])) do
    throw (IO.userError "ambiguous signed provider targets accepted")
  let .ok services := checkedProviderServices [service 7950, service 7951]
    | throw (IO.userError "provider tariffs did not parse")
  let v3 := fun (provider route : String) =>
    "{\"version\":\"3\",\"providerResourceId\":\"" ++ provider ++
      "\",\"route\":\"" ++ route ++
      "\",\"status\":\"200\",\"contentType\":\"application/json\",\"reserve\":\"5\"}"
  unless (ProviderUsage.quotePayload services (quoteFrame (v3 "7951" "pool"))).isOk do
    throw (IO.userError "configured provider pool quote refused")
  let .ok userQuote := ProviderUsage.quotePayload services (quoteFrame (v3 "7951" "user"))
    | throw (IO.userError "configured provider user quote refused")
  unless userQuote.getObjValAs? String "charge" == .ok "4" do
    throw (IO.userError "an own-key (user) call is charged other than its per-op fee")
  unless refused (ProviderUsage.quotePayload services (quoteFrame (v3 "7999" "pool"))) do
    throw (IO.userError "unconfigured provider quote accepted")
  unless refused (ProviderUsage.quotePayload services (quoteFrame (v3 "7951" "elsewhere"))) do
    throw (IO.userError "unknown route accepted")
  unless refused (ProviderUsage.quotePayload services
      (quoteFrame (v3 "7951" "pool") "wrong-model")) do
    throw (IO.userError "wrong request model accepted")
  let a := lifetime 31 41
  let b := lifetime 32 42
  let mixed := lifetime 32 41
  let .ok pins := checkedLifetimeDispatchServices [a, b]
    | throw (IO.userError "same-purse distinct full author pins refused")
  unless refused (checkedLifetimeDispatchServices [a, a]) do
    throw (IO.userError "duplicate lifetime author pin accepted")
  requireOneLifetimeDispatchPin pins (fun pin => decide (pin = a.selectors))
  try
    requireOneLifetimeDispatchPin pins (fun pin => decide (pin = mixed.selectors))
    throw (IO.userError "mixed full lifetime selectors accepted")
  catch error =>
    unless toString error == "lifetime dispatch request differs from unique full operator pin" do
      throw error
  IO.println "PASS provider A/B signed-call selection, tariffs, full author pins"

#eval check

end Minidregg.Host.ProviderServicesAudit
