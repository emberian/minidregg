/-
Read-only source-matched historical selector probe against two independently
accepted A/B Mini Stores. It opens and replays each Store through NativeHost,
then checks that the strict current Kernel selectors recognize the original B
operation and A result. It neither polls nor ACKs fn.
-/
import Host.Main

open Minidregg.Kernel

set_option autoImplicit false

private def requiredEnv (name : String) : IO String := do
  let some value ← IO.getEnv name
    | throw (IO.userError s!"missing {name}")
  unless !value.isEmpty do throw (IO.userError s!"empty {name}")
  pure value

def acceptedHistorySelectorsProbe : IO Unit := do
  let bSettings ← Minidregg.Host.loadSettings (← requiredEnv "FN_B_CONFIG")
  let bConfig := bSettings.config
  let bOpened ← IO.ofExcept (← NativeHost.openExisting bConfig)
  let some bPin := bConfig.fnGateway
    | throw (IO.userError "B has no independent gateway pin")
  let bMatches := bOpened.durable.image.accepted.filter fun record =>
    (FnConsumerOperation.originalBindingWithInbox bPin
      bConfig.deployment.domain bConfig.profile.semantics record).isSome
  unless bMatches.length == 1 do
    throw (IO.userError s!"B strict historical binding matches={bMatches.length}, expected 1")
  let aSettings ← Minidregg.Host.loadSettings (← requiredEnv "FN_A_CONFIG")
  let aConfig := aSettings.config
  let aOpened ← IO.ofExcept (← NativeHost.openExisting aConfig)
  let some aPin := aConfig.fnGateway
    | throw (IO.userError "A has no independent gateway pin")
  let aMatches := aOpened.durable.image.accepted.filter fun record =>
    (FnReplyConsumption.originalResult aPin
      aConfig.deployment.domain aConfig.profile.semantics record).isSome
  unless aMatches.length == 1 do
    throw (IO.userError s!"A strict historical result matches={aMatches.length}, expected 1")
  let revokedPathOption ← IO.getEnv "FN_B_REVOKED_CONFIG"
  if let some revokedPath := revokedPathOption then
    unless revokedPath.isEmpty do
      let revokedSettings ← Minidregg.Host.loadSettings revokedPath
      let revokedConfig := revokedSettings.config
      let revokedOpened ← IO.ofExcept (← NativeHost.openExisting revokedConfig)
      let some revokedPin := revokedConfig.fnGateway
        | throw (IO.userError "revoked B has no independent gateway pin")
      let revokedMatches := revokedOpened.durable.image.accepted.filter fun record =>
        (FnConsumerOperation.originalBindingWithInbox revokedPin
          revokedConfig.deployment.domain revokedConfig.profile.semantics record).isSome
      unless revokedMatches.length == 1 do
        throw (IO.userError s!"revoked B strict historical binding matches={revokedMatches.length}, expected 1")
  IO.println s!"PASS source-matched accepted B binding and A result selectors: B accepted={bOpened.durable.image.accepted.length}, A accepted={aOpened.durable.image.accepted.length}"

#eval acceptedHistorySelectorsProbe
