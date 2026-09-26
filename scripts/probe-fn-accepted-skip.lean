/-
Read-only replay probe for the isolated B empty-page run. Every recognized
skip is selected from an actually accepted Mini signed event, not a caller
cursor. The full signed command equality in originalSkip, together with
progressCommand_exact_action, establishes one tag-9 progress atom and no
application operation, reply, result, or outbox action for each matched skip.
-/
import Host.Main

open Minidregg.Kernel
open Lean

set_option autoImplicit false

private def requiredEnv (name : String) : IO String := do
  let some value ← IO.getEnv name
    | throw (IO.userError s!"missing {name}")
  unless !value.isEmpty do throw (IO.userError s!"empty {name}")
  pure value

def acceptedSkipProbe : IO Unit := do
  let settings ← Minidregg.Host.loadSettings (← requiredEnv "FN_B_SKIP_CONFIG")
  let config := settings.config
  let some gateway := config.fnGateway
    | throw (IO.userError "B skip Store has no independent gateway pin")
  let scopeJson ← Minidregg.Host.readJson (← requiredEnv "FN_B_SKIP_SCOPE")
  let scopePin : Minidregg.Host.FnPollScopePin ← IO.ofExcept (fromJson? scopeJson)
  let scope ← IO.ofExcept scopePin.progressScope
  let opened ← IO.ofExcept (← NativeHost.openExisting config)
  let mut prior : Nat := 0
  let mut count : Nat := 0
  for record in opened.durable.image.accepted do
    if let some skip := FnConsumerProgress.originalSkip gateway scope
        config.deployment.domain config.profile.semantics record then
      unless skip.fromPosition == prior &&
          skip.fromPosition < skip.toPosition &&
          skip.toPosition ≤ skip.fromPosition + FnConsumerProgress.maxPollScan do
        throw (IO.userError "accepted B skips are not an exact bounded cursor chain")
      prior := skip.toPosition
      count := count + 1
      IO.println s!"accepted Mini skip tx={record.transactionId.value} from={skip.fromPosition} to={skip.toPosition}"
  unless count ≥ 2 do
    throw (IO.userError s!"B had only {count} accepted bounded skips; expected at least two")
  IO.println s!"PASS {count} accepted progress-only Mini skips, exact cursor chain through {prior}; no application atom in signed skip commands"

#eval acceptedSkipProbe
