/- Current-image authoring of an independent governed Bend return release.
Only canonical signing-header bytes leave for custody; no key custody, signature
validation, authorization or durable success is manufactured here. The native
BendReturnRelease receiver remains the current authority and exact-event CAS. -/
import Kernel.BendReturnRelease

namespace Minidregg.Host.BendReturnReleaseAuthoring
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.BendReturnRelease
set_option autoImplicit false

structure Plan where
  spec : Spec
  canonicalHeader : List UInt8
  deriving DecidableEq, Repr

def planStream : StreamCodec Plan :=
  StreamCodec.xmap (StreamCodec.product specStream bytesStream)
    (fun p => (p.spec, p.canonicalHeader)) (fun p => ⟨p.1, p.2⟩)
    (by intro p; cases p; rfl)
def planCodec : LawfulCodec Plan :=
  ResourceBirthCodec.strictCodec
    (NativeHostCodec.framed "DREGG/BEND/RETURN-RELEASE-PLAN/v1".toUTF8.toList planStream)

def planFrom (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (spec : Spec)
    (prepared : Prepared (sourceContext config opened) config.profile config.federation
      (NativeHost.logicalHeight config opened.durable) spec) : Except String Plan := do
  let header ← (CredentialSignatureAdmission.signingHeader opened.authority.snapshot
    (marker spec) ⟨.object, prepared.wanted⟩).mapError
      (fun _ => "current Bend return signer refused")
  pure ⟨spec, CredentialSignedEnvelopeController.headerCodec.encode header⟩

def prepareLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (spec : Spec) : Except String Plan := do
  let some prepared := prepare (sourceContext config opened) config.profile config.federation
      (NativeHost.logicalHeight config opened.durable) spec
    | throw "current Bend return source, destination, root or profile refused"
  planFrom config opened spec prepared

def assemble (plan : Plan) (signature : List UInt8) : Except String (List UInt8) := do
  let some header := CredentialSignedEnvelopeController.headerCodec.decode plan.canonicalHeader
    | throw "Bend return signing header is malformed"
  if CredentialSignedEnvelopeController.headerCodec.encode header != plan.canonicalHeader then
    throw "Bend return signing header is noncanonical"
  if signature.length != 64 then
    throw "Bend return signature must be 64 bytes"
  pure <| ingressCodec.encode
    ⟨plan.spec, CredentialSignatureAdmission.canonicalEnvelopeCodec.encode ⟨header, signature⟩⟩

def assembleBytes (planBytes signature : List UInt8) : Except String (List UInt8) := do
  let some plan := planCodec.decode planBytes | throw "Bend return plan is noncanonical"
  assemble plan signature

theorem planFrom_spec_exact (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (spec : Spec)
    (prepared : Prepared (sourceContext config opened) config.profile config.federation
      (NativeHost.logicalHeight config opened.durable) spec)
    (plan : Plan) (success : planFrom config opened spec prepared = .ok plan) :
    plan.spec = spec := by
  unfold planFrom at success
  split at success <;> simp_all

theorem prepare_spec_exact (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (spec : Spec) (plan : Plan) (success : prepareLoaded config opened spec = .ok plan) :
    plan.spec = spec := by
  unfold prepareLoaded at success
  split at success
  · simp_all
  · exact planFrom_spec_exact config opened spec _ plan success

theorem plan_roundtrip (plan : Plan) : planCodec.decode (planCodec.encode plan) = some plan :=
  planCodec.decode_encode plan
theorem plan_canonical {bytes : List UInt8} {plan : Plan}
    (decoded : planCodec.decode bytes = some plan) : planCodec.encode plan = bytes :=
  ResourceBirthCodec.strictCodec_canonical _ decoded

theorem prepare_source_refused (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (spec : Spec)
    (refused : prepare (sourceContext config opened) config.profile config.federation
      (NativeHost.logicalHeight config opened.durable) spec = none) :
    prepareLoaded config opened spec =
      .error "current Bend return source, destination, root or profile refused" := by
  simp [prepareLoaded, refused]

theorem assemble_canonical (spec : Spec)
    (header : CredentialSignedEnvelopeController.SignedHeader) (signature : List UInt8)
    (length : signature.length = 64) :
    assemble ⟨spec, CredentialSignedEnvelopeController.headerCodec.encode header⟩ signature =
      .ok (ingressCodec.encode
        ⟨spec, CredentialSignatureAdmission.canonicalEnvelopeCodec.encode ⟨header, signature⟩⟩) := by
  simp [assemble, CredentialSignedEnvelopeController.headerCodec.decode_encode, length]

theorem assembly_ingress_roundtrip (spec : Spec)
    (header : CredentialSignedEnvelopeController.SignedHeader) (signature : List UInt8) :
    ingressCodec.decode (ingressCodec.encode
      ⟨spec, CredentialSignatureAdmission.canonicalEnvelopeCodec.encode ⟨header, signature⟩⟩) =
      some ⟨spec, CredentialSignatureAdmission.canonicalEnvelopeCodec.encode ⟨header, signature⟩⟩ :=
  ingressCodec.decode_encode _

/-- Exact two-object release fixture input: each governed result gets its own
current-image signing plan; failure of either prevents a successful pair. This
is authoring data only and does not claim atomic combined release or admission. -/
structure TwoResultPlans where
  first : Plan
  second : Plan

def prepareTwo (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (first second : Spec) : Except String TwoResultPlans := do
  let a ← prepareLoaded config opened first
  let b ← prepareLoaded config opened second
  pure ⟨a, b⟩

#assert_axioms planFrom_spec_exact
#assert_axioms prepare_spec_exact
#assert_axioms plan_roundtrip
#assert_axioms plan_canonical
#assert_axioms prepare_source_refused
#assert_axioms assemble_canonical
#assert_axioms assembly_ingress_roundtrip
end Minidregg.Host.BendReturnReleaseAuthoring
