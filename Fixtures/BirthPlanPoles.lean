/-
# Fixtures.BirthPlanPoles -- the plan keystones' poles on a concrete birth (item 7, audit pass 24)

`PlanRefusalSound`, `PlanPassNotLawRefused` and `LawRefusalDisclosed`
(`ResourceBirthPolicyController`) quantify over every `Pending`. Their poles are here, at
declaration level: one concrete `Pending` whose factory verdict is `some true` and one whose
verdict is `some false`, built by the real path. That path is a source-built genesis
(`NativeHostGenesis.build`) opened purely (`DurableReceiverIO.openState`/`openLoaded`,
`NativeHost.validateLoaded`), then the ordinary descriptor of one neutral content birth
(`ResourceReserveBirthFixture`), `ResourceBirthController.Concrete.prepareDraft` and
`ResourceBirthPolicyController.Concrete.preparePending`. The two genesis images differ only
in the factory law: `birth/7001 = <the newborn's exact post root>` passes, and the same law
at that root plus one refuses.

**Evaluated natively (law 9, confessed).** Every root on the path is a cSHAKE digest, and
kernel evaluation costs about 0.13 s per hashed byte (measured on hbox, 2026-10-28). So the
poles are decided by `native_decide`. Lean 4.30 records each native evaluation as its own
auxiliary axiom (`…._native.native_decide.ax_…`), and the pin at the end names exactly those. It lives in
`Fixtures`, which no keystone module, umbrella or axiom census imports. The umbrella target
list builds `Fixtures` (`scripts/pipeline/umbrella-targets`), so the merge gate elaborates
this file and checks its pin (audit pass 24). `scripts/kn2/neutral-birth.lean` remains the end-to-end run against a
native Store.
-/
import Kernel.NativeHostGenesis
import Kernel.NativeHost
import Verify.ResourceReserveBirthFixture

namespace Minidregg.Fixtures.BirthPlanPoles

open Minidregg.Verify

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Compiler
open Minidregg.Kernel

set_option autoImplicit false

def tariff : CreationTariff := ⟨0, 0, 0, 0, 99, 0⟩

def hostTemplate : NativeHost.Config := NativeHost.Config.ofInputs {
  deployment := ⟨⟨8500⟩, 10, 11, 12⟩
  federation := ⟨9⟩
  template := ⟨⟨5⟩, 100000, 10000, 64⟩
  tariff := tariff
  genesisHeight := 10
  expectedSeed := ⟨0⟩
  storage := { binary := "unused", root := "unused", key := "unused", checkpointEvery := 16 }
  signature := ⟨"unused"⟩ }

/-- A 32-byte creator key. The plan poles need no signature, so any key bytes serve. -/
def creatorKey : List UInt8 := (List.range 32).map fun i => UInt8.ofNat (i + 1)

def genesis (factory : Minidregg.Pred.Pred) : NativeHostGenesis.Config where
  deployment := hostTemplate.deployment
  federation := hostTemplate.federation
  tariff := tariff
  expectedSemantics := hostTemplate.profile.semantics
  issuerEpoch := 2
  genesisHeight := 10
  factoryPredicate := factory
  enrollments := [⟨⟨7007, 2, 1, 7, creatorKey, 0, 100, none⟩, 7, ⟨41⟩, ⟨44⟩, ⟨46⟩, 100, .all []⟩]
  factoryController := ⟨⟨7⟩, ⟨43⟩⟩
  meterAllowance := fun _ => 10000000
  clockTickers := []
  tailBound := 1000
  clockGenesisNow := 0
  clockMaxStepSeconds := 300
  issuanceCap := 1000000000000000
  payControlCapabilityId := ⟨47⟩
  clockControlCapabilityId := ⟨48⟩
  platformGrainBirth := none
  platformCustodianKey := none
  platformOwnerBudget := 100000
  platformLifetime := 10000

/-- The genesis image opened purely: the same open and validation as `NativeHost.openExisting`,
over the seed instead of a Store. -/
def opened (factory : Minidregg.Pred.Pred) :
    Except String ((config : NativeHost.Config) × NativeHost.Opened config) := do
  let built ← match NativeHostGenesis.build hostTemplate.profile (genesis factory) with
    | .error reason => throw s!"genesis build: {repr reason}"
    | .ok value => pure value
  let some key := DurableCheckpointCodec.MacKey.ofBytes?
      ((List.range 32).map fun i => UInt8.ofNat (i * 7 + 3)) | throw "mac key"
  let config : NativeHost.Config :=
    NativeHost.Config.ofInputs { hostTemplate.toInputs with expectedSeed := NativeHost.seedIdentity built.seed }
  let logStart := config.logStart built.seed
  let state ← DurableReceiverIO.openState key ResourceBirthCodec.rootBytes logStart built.seed none [] 0
  let ⟨loaded, _⟩ ← DurableReceiverIO.openLoaded key ResourceBirthCodec.rootBytes logStart built.seed
    [] [] state
  let opened ← NativeHost.validateLoaded config loaded
  pure ⟨config, opened⟩

/-- The newborn: one empty content cell at 7001, owner 7; neutral (no room, no kind). -/
def born : ResourceReserveBirthFixture.Born :=
  ResourceReserveBirthFixture.content 7001 ⟨7⟩ ⟨1001⟩ ⟨1101⟩

/-- The exact post root the factory step names the newborn by. -/
def bornRoot : Nat := (ResourceBirthController.birthWrite born.item.create).exactPost.value

/-- A pending birth with everything it is indexed by. -/
abbrev PendingAt :=
  (config : NativeHost.Config) × (pins : FactoryPins) ×
    (ground : Minidregg.Compiler.ServedBasis.Ground config.deployment) ×
    (descriptor : Descriptor ResourceBirthController.Concrete.Registry) × (height : Height) ×
    (prepared : ResourceBirthController.Concrete.PreparedBirth config.profile.compilerProfile
      config.deployment pins ground descriptor) ×
    ResourceBirthPolicyController.Concrete.Pending (profile := config.profile) prepared height

/-- The real plan path for the one-birth descriptor on the genesis whose factory law is
`factory`. -/
def pendingOf (factory : Minidregg.Pred.Pred) : Option PendingAt :=
  match opened factory with
  | .error _ => none
  | .ok ⟨config, o⟩ =>
    let descriptor := ResourceReserveBirthFixture.ordinaryDescriptor config (genesis factory) o
      ⟨7⟩ 71 7 [born]
    let height := NativeHost.logicalHeight config o.durable
    match ResourceBirthController.Concrete.prepareDraft config.profile.compilerProfile
        config.profile.disabledEvaluators config.deployment o.pins (.ofLoaded o.durable o.directory o.authority) descriptor height with
    | .error _ => none
    | .ok prepared =>
      match ResourceBirthPolicyController.Concrete.preparePending (profile := config.profile)
          prepared.prepared height with
      | .error _ => none
      | .ok pending =>
        some ⟨config, o.pins, .ofLoaded o.durable o.directory o.authority, prepared.descriptor, height, prepared.prepared, pending⟩

/-- The law that names the newborn's exact post root. -/
def passLaw : Minidregg.Pred.Pred := .eq (ReceivingLaw.birthSlot 7001) (Int.ofNat bornRoot)

/-- The same law at a root the newborn does not have. -/
def refuseLaw : Minidregg.Pred.Pred := .eq (ReceivingLaw.birthSlot 7001) (Int.ofNat bornRoot + 1)

def verdictIs (expected : Bool) : Option PendingAt → Bool
  | some ⟨_, _, _, _, _, _, pending⟩ => pending.factoryVerdict == some expected
  | none => false

theorem pass_verdict : verdictIs true (pendingOf passLaw) = true := by native_decide

theorem refuse_verdict : verdictIs false (pendingOf refuseLaw) = true := by native_decide

theorem inhabited_of_verdict {expected : Bool} :
    ∀ found : Option PendingAt, verdictIs expected found = true →
      ∃ (config : NativeHost.Config) (pins : FactoryPins)
        (ground : Minidregg.Compiler.ServedBasis.Ground config.deployment)
        (descriptor : Descriptor ResourceBirthController.Concrete.Registry) (height : Height)
        (prepared : ResourceBirthController.Concrete.PreparedBirth config.profile.compilerProfile
          config.deployment pins ground descriptor)
        (pending : ResourceBirthPolicyController.Concrete.Pending (profile := config.profile)
          prepared height),
        pending.factoryVerdict = some expected
  | some ⟨config, pins, ground, descriptor, height, prepared, pending⟩, holds =>
      ⟨config, pins, ground, descriptor, height, prepared, pending, by
        simpa [verdictIs] using holds⟩
  | none, holds => by simp [verdictIs] at holds

/-- **Satisfiable pole (pass 16 (1)).** A concrete `Pending`, built by the real plan path,
whose factory verdict is `some true`: `PlanPassNotLawRefused` is not vacuous. -/
theorem plan_passes_inhabited :
    ∃ (config : NativeHost.Config) (pins : FactoryPins)
      (ground : Minidregg.Compiler.ServedBasis.Ground config.deployment)
      (descriptor : Descriptor ResourceBirthController.Concrete.Registry) (height : Height)
      (prepared : ResourceBirthController.Concrete.PreparedBirth config.profile.compilerProfile
        config.deployment pins ground descriptor)
      (pending : ResourceBirthPolicyController.Concrete.Pending (profile := config.profile)
        prepared height),
      pending.factoryVerdict = some true :=
  inhabited_of_verdict _ pass_verdict

/-- **Teeth pole (pass 16 (1)).** A concrete `Pending` whose factory law evaluates false:
verdict `some false`, so `PlanRefusalSound` and `LawRefusalDisclosed` are not vacuous. -/
theorem plan_refuses_inhabited :
    ∃ (config : NativeHost.Config) (pins : FactoryPins)
      (ground : Minidregg.Compiler.ServedBasis.Ground config.deployment)
      (descriptor : Descriptor ResourceBirthController.Concrete.Registry) (height : Height)
      (prepared : ResourceBirthController.Concrete.PreparedBirth config.profile.compilerProfile
        config.deployment pins ground descriptor)
      (pending : ResourceBirthPolicyController.Concrete.Pending (profile := config.profile)
        prepared height),
      pending.factoryVerdict = some false :=
  inhabited_of_verdict _ refuse_verdict

/-! ## The deny-if-credential law at genesis

`not (witnessed vk)` reads "refuse when credential `vk` is presented". First-party `eval` fails a
`witnessed` leaf closed, so its negation is true on every step: before
`Compiler.supported_no_witnessed` this factory law admitted every birth, and with that refusal
alone the world's factory would refuse every birth. Genesis now refuses the law by name. -/

/-- The deny-if-credential factory law. -/
def denyIfCredentialLaw : Minidregg.Pred.Pred := .not (.witnessed ⟨"vk"⟩)

/-- The fail-open reading that the refusal closes: first-party `eval` admits this step. -/
example : Minidregg.Pred.eval denyIfCredentialLaw ⟨[]⟩ ⟨[]⟩ = true := by decide

/-- Whether genesis refused with `witnessedLaw`. -/
def refusedWitnessed {α : Type} : Except NativeHostGenesis.Error α → Bool
  | .error .witnessedLaw => true
  | _ => false

/-- **Teeth and premise inhabitation for `NativeHostGenesis.witnessed_law_refused` (audit:
Pred.witnessed).** The same genesis that births the plan poles (a valid configuration:
`pass_verdict` opens it with `passLaw`), with the deny-if-credential factory law, is refused by
name. -/
theorem genesis_refuses_witnessed :
    refusedWitnessed (NativeHostGenesis.build hostTemplate.profile (genesis denyIfCredentialLaw)) =
      true := by
  native_decide

/-! ## The axiom pin: the standard three plus exactly the native evaluations. -/

/--
info: 'Minidregg.Fixtures.BirthPlanPoles.plan_passes_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 pass_verdict._native.native_decide.ax_1_1]
-/
#guard_msgs (whitespace := lax) in #print axioms plan_passes_inhabited

/--
info: 'Minidregg.Fixtures.BirthPlanPoles.plan_refuses_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 refuse_verdict._native.native_decide.ax_1_1]
-/
#guard_msgs (whitespace := lax) in #print axioms plan_refuses_inhabited

/--
info: 'Minidregg.Fixtures.BirthPlanPoles.genesis_refuses_witnessed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 genesis_refuses_witnessed._native.native_decide.ax_1_1]
-/
#guard_msgs (whitespace := lax) in #print axioms genesis_refuses_witnessed

end Minidregg.Fixtures.BirthPlanPoles
