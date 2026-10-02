/- Stable profile data, arithmetic premises and request projection shared by
receivers. Current runtime markers and the only current-profile constructor
remain in CanonicalRuntimeProfile. Native ingress cannot select a manifest. -/
import Compiler.CanonicalPolicyAdmission
import Compiler.ResourceBirthCodec

namespace Minidregg.Compiler.CanonicalRuntimeProfile

open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- The admission lag a birth may carry, in heights: the longest honest
authoring-to-admission gap the deployment tolerates. Every admission advances
the height (`nativeClockVersion`), so this counts other admissions, not
seconds: a birth authored at `H0` stays admissible through the next 64
admissions anyone makes. The deployed clock ticks once a minute and a busy
room adds a handful more per birth window (10-40 s measured), so 64 is an
order of magnitude over the honest gap and far under every owner grant
`lifetime`. -/
def defaultBirthSlack : Nat := 64

/-- First-order factory parameters are part of the one compatible runtime identity.
`birthSlack` is how many heights after its authored `notBefore` a birth may
still be admitted (`ResourceBirthPolicyController.Concrete.BirthWindow`). -/
structure FactoryTemplate where
  issuer : IssuerId
  ownerBudget : Nat
  lifetime : Nat
  birthSlack : Nat := defaultBirthSlack
  deriving DecidableEq, Repr

def FactoryTemplate.tuple (template : FactoryTemplate) : Nat × (Nat × (Nat × Nat)) :=
  (template.issuer.value, template.ownerBudget, template.lifetime, template.birthSlack)

def FactoryTemplate.ofTuple (tuple : Nat × (Nat × (Nat × Nat))) : FactoryTemplate :=
  ⟨⟨tuple.1⟩, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩

@[simp] theorem FactoryTemplate.ofTuple_tuple (template : FactoryTemplate) :
    ofTuple template.tuple = template := by
  cases template with
  | mk issuer budget lifetime slack => cases issuer; rfl

def factoryTemplateStream : StreamCodec FactoryTemplate :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
    FactoryTemplate.tuple FactoryTemplate.ofTuple FactoryTemplate.ofTuple_tuple

def FactoryTemplate.encode (template : FactoryTemplate) : List UInt8 :=
  factoryTemplateStream.encode template

/-- Reuse the canonical kind encoder; there is no second ordinal table in the views. -/
def requestKindTag (kind : ResourceKind) : Nat :=
  ((ResourceBirthCodec.resourceKindStream.encode kind).head (by
    cases kind <;> decide)).toNat

/-- Shared scalar header for every native operation's predicate view. Digest fields
remain bound by the complete authorization request and the source-derived context.
The target resource and selected policy are distinct coordinates. Grant
generation and current source revision are also distinct signed coordinates. -/
def requestSlots {kind : ResourceKind} (request : Request kind) : List (String × Int) :=
  [("request/kind", Int.ofNat (requestKindTag kind)),
   ("request/verb", Int.ofNat (CredentialAuthorityEntryCodec.verbTag request.verb)),
   ("request/subject", Int.ofNat request.subject.value),
   ("request/subjectKeyEpoch", Int.ofNat request.subjectKeyEpoch),
   ("request/federation", Int.ofNat request.federation.value),
   ("request/height", Int.ofNat request.height),
   ("request/policyEpoch", Int.ofNat request.policyEpoch),
   ("request/policyRevision", Int.ofNat request.policyRevision),
   ("request/nonce", Int.ofNat request.nonce),
   ("request/target", Int.ofNat request.target.value),
   ("target/policyId", Int.ofNat request.policyId.value),
   ("request/cost", Int.ofNat request.cost)]

theorem request_kind_exact {kind : ResourceKind} (request : Request kind) :
    (⟨requestSlots request⟩ : Minidregg.Pred.State).get "request/kind" =
      some (Int.ofNat (requestKindTag kind)) := by
  simp [Minidregg.Pred.State.get, requestSlots]

theorem request_verb_exact {kind : ResourceKind} (request : Request kind) :
    (⟨requestSlots request⟩ : Minidregg.Pred.State).get "request/verb" =
      some (Int.ofNat (CredentialAuthorityEntryCodec.verbTag request.verb)) := by
  simp [Minidregg.Pred.State.get, requestSlots]

theorem request_target_and_policy_exact {kind : ResourceKind} (request : Request kind) :
    (⟨requestSlots request⟩ : Minidregg.Pred.State).get "request/target" =
        some (Int.ofNat request.target.value) ∧
      (⟨requestSlots request⟩ : Minidregg.Pred.State).get "target/policyId" =
        some (Int.ofNat request.policyId.value) := by
  simp [Minidregg.Pred.State.get, requestSlots]

def runtimeStream : StreamCodec (List (List UInt8) × FactoryTemplate) :=
  StreamCodec.product (StreamCodec.list bytesStream) factoryTemplateStream

/-- The framing and hash function are stable; only the compiled manifest supplied
by the native builder varies. No receiver or request decodes a profile. -/
def receiverSemanticsFrom (components : List (List UInt8))
    (template : FactoryTemplate) (parameters : List UInt8 := [])
    (disabled : List Digest := []) : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE.RUNTIME.SEMANTICS/v3".toUTF8.toList
    ((StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.list digestStream))).encode
      (runtimeStream.encode (components, template), parameters, disabled))).digest

/-- Native runtime profiles always enable scalar order with its actual arithmetic
premises. The common compiler bundle is derived below, so a template/profile
disagreement or research fallback cannot be stored in this type. -/
structure Profile (F : Type) [Field F] where
  template : FactoryTemplate
  fieldIdentity : Digest
  characteristic : Nat
  characteristicCorrect : CharP F characteristic
  orderWidth : Nat
  orderNoWrap : PredOrder.NoWrap F orderWidth
  /-- Source-owned deployment parameters, never selected by an operation. -/
  receiverParameters : List UInt8 := []
  /-- Compiled-in evaluators (`Evaluator.registry`) this deployment's operator disabled,
  by id: a run on one refuses `evaluatorDisabled` (`Kernel.Run.resolve`). Committed in
  `semantics`. -/
  disabledEvaluators : List Digest := []
  /-- Source manifest supplied by the compiled native builder, never an ingress field. -/
  runtimeComponents : List (List UInt8)

def Profile.fromComponents {F : Type} [Field F] (components : List (List UInt8)) (template : FactoryTemplate)
    (fieldIdentity : Digest) (characteristic : Nat)
    (characteristicCorrect : CharP F characteristic) (orderWidth : Nat)
    (orderNoWrap : PredOrder.NoWrap F orderWidth) (receiverParameters : List UInt8 := [])
    (disabledEvaluators : List Digest := []) : Profile F :=
  ⟨template, fieldIdentity, characteristic, characteristicCorrect, orderWidth, orderNoWrap,
    receiverParameters, disabledEvaluators, components⟩

def Profile.compilerProfile {F : Type} [Field F] (profile : Profile F) :
    PolicyCompilerProfile F :=
  .source (receiverSemanticsFrom profile.runtimeComponents profile.template profile.receiverParameters profile.disabledEvaluators)
    profile.fieldIdentity
    profile.characteristic profile.characteristicCorrect
    (.scalar profile.orderWidth) profile.orderNoWrap

def Profile.semantics {F : Type} [Field F] (profile : Profile F) : Digest :=
  profile.compilerProfile.semantics

theorem Profile.receiverSemantics_exact {F : Type} [Field F] (profile : Profile F) :
    profile.compilerProfile.descriptor?.map (·.receiverSemantics) =
      some (receiverSemanticsFrom profile.runtimeComponents profile.template profile.receiverParameters
        profile.disabledEvaluators) := rfl

theorem Profile.order_enabled {F : Type} [Field F] (profile : Profile F) :
    profile.compilerProfile.compiler = .scalar profile.orderWidth := rfl

theorem Profile.canonical_compatible {F : Type} [Field F] (profile : Profile F)
    (context : PolicyStepContext) :
    profile.compilerProfile.compatible (.canonical context) = true := rfl

theorem Profile.actual_characteristic {F : Type} [Field F] (profile : Profile F) :
    CharP F profile.characteristic := profile.characteristicCorrect

end Minidregg.Compiler.CanonicalRuntimeProfile
