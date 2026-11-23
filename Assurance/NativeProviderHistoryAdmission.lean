/- Focused executable predicates plus the real credential receiving gate.
These fixtures do not fabricate a verified Store or claim native receipt evidence.
The shared-Store journey separately exercises history replay and append races. -/
import Kernel.NativePlanHeight
import Kernel.NativeProviderHistory

namespace Minidregg.Assurance.NativeProviderHistoryAdmission

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel
open Minidregg.Kernel.CredentialSignedEnvelopeController
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def key : KeyRecord := ⟨1, 0, 1, 9, [1, 2, 3], 0, 100, none⟩
def registry : KeyRegistryProjection := ⟨registryCodecVersion, ⟨7⟩, 0, [key]⟩
def header : SignedHeader :=
  ⟨envelopeCodecVersion, [4, 5], 80, 1, 0, 1, [6], [7, 8], 99⟩
def state (height : Nat) : ControllerState :=
  ⟨stateCodecVersion, ⟨7⟩, registryDigest (registryCodec.encode registry),
    0, header.footprint, height, []⟩
def prepareAt (height : Nat) (h : SignedHeader) :
    Except (Failure Unit) Prepared :=
  prepare 9 header.domain header.message (stateCodec.encode (state height))
    (registryCodec.encode registry) (envelopeCodec.encode ⟨h, [9]⟩)
def acceptedAt (height : Nat) (h : SignedHeader) : Bool :=
  match prepareAt height h with | .ok _ => true | .error _ => false
def expiredAt (height : Nat) (h : SignedHeader) : Bool :=
  match prepareAt height h with | .error .expired => true | _ => false

/-! The receiving-parser fixtures below run `prepare` over the registry DIGEST, so only the
compiled evaluator reaches them (`native_decide` + `#assert_compiled`). The facts about
`pinHeader` and the strict-advance step hold for every height and header and are kernel proofs. -/

-- Actual receiving parser accepts this unsigned fixture through semantic
-- preparation only; cryptographic finish is intentionally not fabricated.
theorem pinned_accepted_at_height : acceptedAt 20 (NativePlanHeight.pinHeader 20 header) = true := by
  native_decide
#assert_compiled pinned_accepted_at_height

/-- A same-height prefix does NOT retire a still-admissible call: its next append position
`n + 1` is outside that prefix, at every height. Strict advancement is essential. -/
theorem same_height_prefix_excludes_next (n : Nat) : ¬ (n + 1 ≤ n) := Nat.not_succ_le_self n
#assert_axioms same_height_prefix_excludes_next

theorem pinned_expired_after_height : expiredAt 21 (NativePlanHeight.pinHeader 20 header) = true := by
  native_decide
#assert_compiled pinned_expired_after_height
theorem unpinned_accepted_past_pin : acceptedAt 21 header = true := by native_decide
#assert_compiled unpinned_accepted_past_pin
theorem pin_keeps_earlier_deadline :
    expiredAt 20 (NativePlanHeight.pinHeader 20 { header with validUntil := 19 }) = true := by
  native_decide
#assert_compiled pin_keeps_earlier_deadline

/-- The height pin never touches what the signer signs over or the nullifier, for every
height and header. -/
theorem pinHeader_message (height : Nat) (h : SignedHeader) :
    (NativePlanHeight.pinHeader height h).message = h.message := rfl
theorem pinHeader_nullifier (height : Nat) (h : SignedHeader) :
    (NativePlanHeight.pinHeader height h).nullifier = h.nullifier := rfl
#assert_axioms pinHeader_message pinHeader_nullifier

def before : ProviderRoute.State := ⟨⟨1, 1, 12, 0⟩, 0⟩
def held : ProviderRoute.State := ProviderRoute.after (.reserve 3) 3 before
def reserveCommand : DeclaredResourceController.Command :=
  { subject := ⟨9⟩, nonce := 101,
    targets := [ProviderRoute.target (.reserve 3) 3 8974 ⟨103⟩ ⟨10⟩ before] }
def fenceCommand : DeclaredResourceController.Command :=
  { subject := ⟨9⟩, nonce := 102,
    targets := [ProviderRoute.target .disconnect 3 8974 ⟨103⟩ ⟨11⟩ held] }
def call (command : DeclaredResourceController.Command) : ByteArray :=
  (callCodec.encode (.invoke ⟨DeclaredResourceController.commandCodec.encode command, [], [], []⟩)).toByteArray

theorem fence_exact : NativeProviderHistory.exactHardFence ⟨8974⟩ (call reserveCommand)
    (call fenceCommand) = true := by native_decide
#assert_compiled fence_exact
def parentWitness : DeclaredResourceController.Target :=
  AgentGrain.Operation.input.target 8971 ⟨75⟩ ⟨12⟩ ⟨1, 4, 997, 3⟩
theorem fence_exact_with_parent_witness : NativeProviderHistory.exactHardFence ⟨8974⟩
    (call { reserveCommand with targets := parentWitness :: reserveCommand.targets })
    (call fenceCommand) = true := by native_decide
theorem fence_refuses_input_reserve : NativeProviderHistory.exactHardFence ⟨8974⟩
    (call { reserveCommand with targets :=
      [ProviderRoute.target .input 3 8974 ⟨103⟩ ⟨10⟩ held] }) (call fenceCommand) = false := by
  native_decide
theorem fence_refuses_cancel_witness : NativeProviderHistory.exactHardFence ⟨8974⟩
    (call { reserveCommand with targets :=
      AgentGrain.Operation.cancel.target 8971 ⟨75⟩ ⟨12⟩ ⟨1, 4, 997, 3⟩ :: reserveCommand.targets })
    (call fenceCommand) = false := by native_decide
theorem fence_refuses_other_provider : NativeProviderHistory.exactHardFence ⟨8975⟩
    (call reserveCommand) (call fenceCommand) = false := by native_decide
theorem fence_refuses_other_subject : NativeProviderHistory.exactHardFence ⟨8974⟩
    (call reserveCommand) (call { fenceCommand with subject := ⟨20⟩ }) = false := by native_decide
theorem fence_refuses_settle : NativeProviderHistory.exactHardFence ⟨8974⟩ (call reserveCommand)
    (call { fenceCommand with targets :=
      [ProviderRoute.target (.settle 3) 3 8974 ⟨103⟩ ⟨11⟩ held] }) = false := by native_decide
theorem fence_refuses_extra_targets : NativeProviderHistory.exactHardFence ⟨8974⟩
    (call reserveCommand)
    (call { fenceCommand with targets := fenceCommand.targets ++ reserveCommand.targets })
      = false := by native_decide
#assert_compiled fence_exact_with_parent_witness
#assert_compiled fence_refuses_input_reserve
#assert_compiled fence_refuses_cancel_witness
#assert_compiled fence_refuses_other_provider
#assert_compiled fence_refuses_other_subject
#assert_compiled fence_refuses_settle
#assert_compiled fence_refuses_extra_targets

def plan : SigningPlan :=
  ⟨⟨1⟩, ⟨2⟩, ⟨3⟩, 20,
    .invoke (DeclaredResourceController.commandCodec.encode reserveCommand),
    [⟨4, 0, headerCodec.encode header⟩, ⟨1, 0, headerCodec.encode header⟩]⟩
def pinnedPlanCorrect : Bool :=
  match NativePlanHeight.pin plan with
  | .error _ => false
  | .ok pinned =>
      decide (pinned.domain = plan.domain) && decide (pinned.semantics = plan.semantics) &&
      decide (pinned.worldRoot = plan.worldRoot) && pinned.height == plan.height &&
      (draftCodec.encode pinned.finalizedDraft == draftCodec.encode plan.finalizedDraft) &&
      pinned.slots.length == 2 && pinned.slots.all (fun slot =>
        decide (headerCodec.decode slot.header = some (NativePlanHeight.pinHeader 20 header)))
theorem pin_plan_correct : pinnedPlanCorrect = true := by native_decide
#assert_compiled pin_plan_correct
def pinRefused (candidate : SigningPlan) : Bool :=
  match NativePlanHeight.pin candidate with | .error _ => true | .ok _ => false
theorem pin_refuses_no_slots : pinRefused { plan with slots := [] } = true := by native_decide
theorem pin_refuses_noncanonical_slots :
    pinRefused { plan with slots := [⟨4, 0, []⟩, ⟨1, 0, []⟩] } = true := by native_decide
theorem pin_refuses_noncanonical_draft :
    pinRefused { plan with finalizedDraft := .invoke [] } = true := by native_decide
#assert_compiled pin_refuses_no_slots
#assert_compiled pin_refuses_noncanonical_slots
#assert_compiled pin_refuses_noncanonical_draft

-- Pure bounds/matching fixtures; only checkPrior supplies a receipt drawn
-- from the actual verifier-minted history used by API17.
def priorPoint : NativeProviderHistory.PriorChecked := ⟨23, ⟨42⟩⟩
def priorReceipt : Receipt := ⟨⟨100⟩, ⟨101⟩, 23, ⟨42⟩⟩
/-- `priorBounds`, for every reserve count, current count and point: a nonempty reserve
prefix no longer than the point, which is no later than now. -/
theorem priorBounds_iff (reserveCount currentCount : Nat) (point : NativeProviderHistory.PriorChecked) :
    NativeProviderHistory.priorBounds reserveCount currentCount point = true ↔
      0 < reserveCount ∧ reserveCount ≤ point.acceptedCount ∧ point.acceptedCount ≤ currentCount := by
  simp [NativeProviderHistory.priorBounds]

/-- `priorReceiptMatches`, for every point and receipt: both the count and the world root agree. -/
theorem priorReceiptMatches_iff (point : NativeProviderHistory.PriorChecked) (receipt : Receipt) :
    NativeProviderHistory.priorReceiptMatches point receipt = true ↔
      receipt.acceptedCount = point.acceptedCount ∧ receipt.worldRoot = point.worldRoot := by
  simp [NativeProviderHistory.priorReceiptMatches]

theorem prior_bounds_inside : NativeProviderHistory.priorBounds 19 27 priorPoint = true := by decide
theorem prior_bounds_empty_reserve : NativeProviderHistory.priorBounds 0 27 priorPoint = false := by
  decide
theorem prior_bounds_reserve_after_point :
    NativeProviderHistory.priorBounds 24 27 priorPoint = false := by decide
theorem prior_bounds_point_after_now :
    NativeProviderHistory.priorBounds 19 22 priorPoint = false := by decide
theorem prior_receipt_matches :
    NativeProviderHistory.priorReceiptMatches priorPoint priorReceipt = true := by decide
theorem prior_receipt_other_root : NativeProviderHistory.priorReceiptMatches priorPoint
    { priorReceipt with worldRoot := ⟨43⟩ } = false := by decide
theorem prior_receipt_other_count : NativeProviderHistory.priorReceiptMatches priorPoint
    { priorReceipt with acceptedCount := 24 } = false := by decide
#assert_axioms priorBounds_iff priorReceiptMatches_iff prior_bounds_inside
  prior_bounds_empty_reserve prior_bounds_reserve_after_point prior_bounds_point_after_now
  prior_receipt_matches prior_receipt_other_root prior_receipt_other_count

end Minidregg.Assurance.NativeProviderHistoryAdmission
