/- Full-peer consent entry with source-native lifecycle adapters. -/
import Host.ClientConsentCore
import Host.NativeLifecycleConsent
open Minidregg.Kernel
namespace Minidregg.Host.ClientConsentSession
private def lifecycleExpected : ClientConsentCore.ExtraExpected := fun settings config session operation request => do
  if NativeLifecycleConsent.supported operation then
    NativeLifecycleConsent.expectedPlanBytes config session.2 operation request
  else if NativeLifecycleConsent.managedSupported operation then do
    let some management := settings.lifecycleManagement
      | throw (IO.userError "local lifecycleManagement pin required before signing")
    NativeLifecycleConsent.expectedManagedPlanBytes config session.2
      management.managementSubject management.managementKeyId operation request
  else throw (IO.userError "unsupported specialized consent adapter")
def run (arguments : List String) : IO UInt32 :=
  ClientConsentCore.run lifecycleExpected arguments
end Minidregg.Host.ClientConsentSession
def main (arguments : List String) : IO UInt32 := do
  try Minidregg.Host.ClientConsentSession.run arguments
  catch error =>
    IO.eprintln s!"minidregg-client-consent: {error}"
    pure 1
