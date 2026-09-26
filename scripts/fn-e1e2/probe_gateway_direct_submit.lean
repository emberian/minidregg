/-
Native negative admission probe. The fixture must already contain an ordinary
subject's valid current mutate grant on the gateway content resource. This
source-owned probe uses the internal planner solely to form a signed call
without the public observation gate; it then enters the actual native receiver.
Absent capability, bad signature, or malformed command is NOT a pass.
-/
import Host.Main

open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel

namespace FnGatewayDirectSubmitProbe

set_option autoImplicit false

def env (name : String) : IO String := do
  let some value ← IO.getEnv name
    | throw (IO.userError s!"missing {name}")
  if value.isEmpty then throw (IO.userError s!"empty {name}")
  pure value

def decimalEnv (name : String) : IO Nat := do
  let value ← env name
  let some n := value.toNat?
    | throw (IO.userError s!"{name} is not decimal")
  unless toString n == value do
    throw (IO.userError s!"{name} is not canonical decimal")
  pure n

def checkedProcess (cmd : String) (args : Array String) : IO Unit := do
  let result ← IO.Process.output { cmd, args }
  unless result.exitCode == 0 do
    throw (IO.userError s!"{cmd} failed: {result.stderr}")

def signHeader (openssl directory keyDer : String) (header : List UInt8)
    (index : Nat) : IO (List UInt8) := do
  let input := s!"{directory}/header-{index}.bin"
  let output := s!"{directory}/signature-{index}.bin"
  IO.FS.writeBinFile input header.toByteArray
  checkedProcess openssl #["pkeyutl", "-sign", "-rawin", "-keyform", "DER",
    "-inkey", keyDer, "-in", input, "-out", output]
  let signature := (← IO.FS.readBinFile output).toList
  unless signature.length == 64 do
    throw (IO.userError "OpenSSL returned non-Ed25519 signature")
  pure signature

def run : IO Unit := do
  let settings ← Minidregg.Host.loadSettings (← env "FN_GATEWAY_CONFIG")
  let config := settings.config
  let some pin := config.fnGateway
    | throw (IO.userError "config has no independent fn gateway pin")
  let subjectValue ← decimalEnv "FN_GATEWAY_ORDINARY_SUBJECT"
  let capabilityValue ← decimalEnv "FN_GATEWAY_ORDINARY_CAPABILITY"
  let subject : SubjectId := ⟨subjectValue⟩
  let capability : CapabilityId := ⟨capabilityValue⟩
  unless subject != pin.subject do
    throw (IO.userError "ordinary and gateway subjects must differ")
  let directory ← env "FN_GATEWAY_PROBE_DIR"
  let openssl ← env "FN_GATEWAY_OPENSSL"
  let keySeed := (← IO.FS.readBinFile (← env "FN_GATEWAY_ORDINARY_KEY")).toList
  unless keySeed.length == 32 do
    throw (IO.userError "ordinary Ed25519 seed must be 32 bytes")
  -- RFC 8410 Ed25519 PrivateKeyInfo around the client's raw seed.
  let keyDer := s!"{directory}/ordinary.pk8.der"
  IO.FS.writeBinFile keyDer
    ([0x30, 0x2e, 0x02, 0x01, 0x00, 0x30, 0x05, 0x06, 0x03,
      0x2b, 0x65, 0x70, 0x04, 0x22, 0x04, 0x20] ++ keySeed).toByteArray
  let opened ← IO.ofExcept (← NativeHost.openExisting config)
  let some grant := readCapability opened.authority.snapshot.cell .object capability
    | throw (IO.userError "ordinary capability absent: invalid negative fixture")
  unless grant.head.id == capability && grant.head.holder == .subject subject &&
      grant.head.policyId == ⟨pin.target⟩ &&
      decide (⟨pin.target⟩ ∈ grant.head.scope.targets) &&
      decide (Verb.mutateObject ∈ grant.head.scope.verbs) do
    throw (IO.userError "ordinary grant does not cover gateway target mutation")
  let probeTarget : DeclaredResourceController.Target :=
    ⟨.object, pin.target, capability, 1, ⟨0⟩, .content ⟨[]⟩, none⟩
  let .present cell := opened.directory.directory.slots pin.target
    | throw (IO.userError "gateway target absent")
  let some pre := DeclaredResourceController.selectTarget config.deployment probeTarget cell
    | throw (IO.userError "gateway target is not a content resource")
  let nonce ← decimalEnv "FN_GATEWAY_PROBE_NONCE"
  let action : ContentResource.Action :=
    .createAtom ⟨⟨2 ^ 280 + nonce⟩⟩ (.inlineObject ⟨1⟩) [1]
  let command : DeclaredResourceController.Command :=
    ⟨subject, opened.authority.snapshot.cell.root, nonce,
      [⟨.object, pin.target, capability, 1, pre.root,
        .content ⟨[action]⟩, none⟩]⟩
  let plan ← IO.ofExcept (NativeHost.prepareLoaded config opened
    (.invoke (DeclaredResourceController.commandCodec.encode command)))
  let signatures ← (plan.slots.zipIdx).mapM fun (slot, index) =>
    signHeader openssl directory keyDer slot.header index
  let call ← IO.ofExcept (NativeHost.assemble plan signatures)
  IO.FS.writeBinFile s!"{directory}/direct-call.bin"
    (callCodec.encode call).toByteArray
  let outcome ← NativeHost.submitLoaded config opened call
  match outcome with
  | .refused phase detail =>
      let detailText := String.fromUTF8! detail.toByteArray
      unless phase == "invoke".toUTF8.toList &&
          (detailText.splitOn "policyRejected").length > 1 do
        throw (IO.userError s!"wrong receiver refusal: {detailText}")
  | _ => throw (IO.userError "ordinary signed call was not policy-refused")
  let publicOutcome ← NativeHost.submit config (callCodec.encode call)
  match publicOutcome with
  | .refused phase detail =>
      unless phase == "admission".toUTF8.toList &&
          detail == "request refused".toUTF8.toList do
        throw (IO.userError "public submission exposed unexpected refusal")
  | _ => throw (IO.userError "public direct submit did not refuse")
  let reopened ← IO.ofExcept (← NativeHost.openExisting config)
  unless decide (reopened.durable.bytes.toByteArray =
      opened.durable.bytes.toByteArray) do
    throw (IO.userError s!"refused ordinary call changed canonical durable image \
      (accepted count {opened.durable.image.accepted.length} → \
      {reopened.durable.image.accepted.length})")
  IO.println "PASS native receiver refused valid-grant ordinary subject at gateway policy"

end FnGatewayDirectSubmitProbe

#eval FnGatewayDirectSubmitProbe.run
