/- Core227: the full-peer Objective consent adapter. From the client's OWN
retained request and verified prefix it re-derives the final command with the
same quotation producer, re-derives the native signing plan for that command,
compares the proposal byte-for-byte, and returns only the headers the selected
current custody key signs.

The derivation refuses unless the CURRENT stored artifact and package equal the
bytes the client produced by its own pinned frontend replay
(`Source.expectedArtifact` / `expectedPackage`): an importer or invoker never
trusts a publisher's core. Producing those expected bytes is the client's
pinned frontend (trusted frontend boundary). -/
import Host.ClientConsentCore
import Host.ObjectiveInvocationQuote
namespace Minidregg.Host.ObjectiveConsent
open Minidregg.Compiler Minidregg.Kernel
open Minidregg.Compiler.NativeHostCodec
set_option autoImplicit false

/-- Role names the request's own subject: the invoker signs the command's
incidences. No other role is source-defined yet; others refuse. -/
def invokerRole : String := "invoker"

def extraObjective : ClientConsentCore.ExtraObjective :=
  fun _settings config session original publicKey role candidate => do
    unless role == invokerRole do throw (IO.userError "unsupported Objective custody role")
    let some request := ObjectiveBendQuoteRequest.decode original
      | throw (IO.userError "noncanonical retained Objective request")
    let key ← IO.ofExcept ((NativeObservationController.intentKey
      (NativeHost.observationContext config session.2.opened) request.subject).mapError
      (fun _ => "Objective request subject has no current signing key"))
    unless key == publicKey do throw (IO.userError "Objective request subject differs from custody signer")
    let derived ← IO.ofExcept (← ObjectiveInvocationQuote.derive config session.2.opened request)
    let commandBytes := DeclaredResourceController.commandCodec.encode derived.command
    let plan ← IO.ofExcept (NativeHost.prepareLoaded config session.2.opened (.invoke commandBytes))
    unless signingPlanCodec.encode plan == candidate do
      throw (IO.userError "proposed Objective signing plan differs from the locally derived plan")
    let some current := Minidregg.Theory.CredentialAuthorityState.currentSigningKey
        session.2.opened.authority.snapshot.logical request.subject
      | throw (IO.userError "Objective request subject has no current key")
    let headers := plan.slots.map SigningSlot.header
    for bytes in headers do
      let some header := CredentialSignedEnvelopeController.headerCodec.decode bytes
        | throw (IO.userError "derived Objective plan has a noncanonical header")
      unless header.keyId == current.keyId && header.keyEpoch == current.keyEpoch &&
          header.algorithm == current.algorithm do
        throw (IO.userError "derived Objective plan selects another custody signer")
    pure headers

end Minidregg.Host.ObjectiveConsent
