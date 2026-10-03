/- Independent full-peer ordinary/money/enrollment/fleet consent entry.
Higher lifecycle families refuse explicitly until the full entry is available. -/
import Host.ClientConsentCore
namespace Minidregg.Host.ClientConsentSpecializedSession
private def unsupported : ClientConsentCore.ExtraExpected := fun _ _ _ _ _ =>
  throw (IO.userError "this consent entry has no adapter for the selected lifecycle family")
def run (arguments : List String) : IO UInt32 :=
  ClientConsentCore.run unsupported arguments
end Minidregg.Host.ClientConsentSpecializedSession
def main (arguments : List String) : IO UInt32 := do
  try Minidregg.Host.ClientConsentSpecializedSession.run arguments
  catch error =>
    IO.eprintln s!"minidregg-client-consent: {error}"
    pure 1
