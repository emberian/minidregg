/-
Typed, source-owned quote for a provider-reported Chat Completions usage record.
The operator pins the tariff and funds an independent AgentGrain allowance.
Neither these counts nor this quote authenticate a provider invoice. The native
receiver still decides whether an authored settlement is admitted.
-/
import Kernel.AgentGrain

namespace Minidregg.Kernel.ProviderMetering

open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Compiler
open Minidregg.Kernel

set_option autoImplicit false

/-- AgentGrain permission micro-units charged per million reported tokens.
The version is an operator-controlled tariff identity, not a provider price feed. -/
structure Tariff where
  version : Nat
  model : String
  inputMicroPerMillion : Nat
  outputMicroPerMillion : Nat
  deriving DecidableEq, Repr

/-- Counts asserted in one complete upstream response. The parser, not the
worker, must construct these from the retained response bytes. -/
structure Usage where
  promptTokens : Nat
  completionTokens : Nat
  totalTokens : Nat
  deriving DecidableEq, Repr

def maxReportedTokens : Nat := 1000000000
def maxRate : Nat := 1000000000000
def million : Nat := 1000000

def Tariff.valid (tariff : Tariff) : Prop :=
  0 < tariff.version ∧
  0 < tariff.model.toUTF8.size ∧
  tariff.model.toUTF8.size ≤ 256 ∧
  tariff.inputMicroPerMillion ≤ maxRate ∧
  tariff.outputMicroPerMillion ≤ maxRate

def Usage.valid (usage : Usage) : Prop :=
  usage.totalTokens = usage.promptTokens + usage.completionTokens ∧
  usage.promptTokens ≤ maxReportedTokens ∧
  usage.completionTokens ≤ maxReportedTokens

/-- Round the aggregate charge upward once, to an integral permission
micro-unit. No floating-point arithmetic or per-category double rounding. -/
def charge (tariff : Tariff) (usage : Usage) : Nat :=
  (usage.promptTokens * tariff.inputMicroPerMillion +
    usage.completionTokens * tariff.outputMicroPerMillion + million - 1) / million

def weighted (tariff : Tariff) (usage : Usage) : Nat :=
  usage.promptTokens * tariff.inputMicroPerMillion +
    usage.completionTokens * tariff.outputMicroPerMillion

/-- The one rounding point is the ceiling of the aggregate numerator,
including the zero-usage case. -/
theorem charge_rounding (tariff : Tariff) (usage : Usage) :
    weighted tariff usage ≤ charge tariff usage * million ∧
      charge tariff usage * million < weighted tariff usage + million := by
  unfold charge weighted million
  omega

/-- Unambiguous length-prefixing keeps model/version/rates distinct before the
repository's domain-separated cSHAKE projection. -/
def tariffBytes (tariff : Tariff) : List UInt8 :=
  Sp800185Cshake256.encodeString tariff.model.toUTF8.toList ++
  Sp800185Cshake256.leftEncode tariff.version ++
  Sp800185Cshake256.leftEncode tariff.inputMicroPerMillion ++
  Sp800185Cshake256.leftEncode tariff.outputMicroPerMillion

def tariffDigest (tariff : Tariff) : Digest :=
  (Sp800185Cshake256.hash "DREGG.PROVIDER.TARIFF/v1".toUTF8.toList
    (tariffBytes tariff)).digest

def requestDigest (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.PROVIDER.REQUEST/v1".toUTF8.toList bytes).digest

def responseDigest (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.PROVIDER.RESPONSE/v1".toUTF8.toList bytes).digest

/-- A quote identifies the exact retained request/response bytes, reported
usage, configured tariff and held allowance. Its evidence is external data;
the proof fields establish only arithmetic and allowance bounds. -/
structure Quote where
  tariff : Tariff
  tariffValid : tariff.valid
  usage : Usage
  usageValid : usage.valid
  request : List UInt8
  response : List UInt8
  reserve : Nat
  amount : Nat
  amountExact : amount = charge tariff usage
  amountBound : amount ≤ reserve

def prepare (tariff : Tariff) (usage : Usage) (request response : List UInt8)
    (reserve : Nat) : Option Quote :=
  if ht : 0 < tariff.version ∧ 0 < tariff.model.toUTF8.size ∧
      tariff.model.toUTF8.size ≤ 256 ∧
      tariff.inputMicroPerMillion ≤ maxRate ∧
      tariff.outputMicroPerMillion ≤ maxRate then
   if hv : usage.totalTokens = usage.promptTokens + usage.completionTokens ∧
      usage.promptTokens ≤ maxReportedTokens ∧
      usage.completionTokens ≤ maxReportedTokens then
    if hb : charge tariff usage ≤ reserve then
      some ⟨tariff, ht, usage, hv, request, response, reserve,
        charge tariff usage, rfl, hb⟩
    else none
   else none
  else none

def Quote.operation (quote : Quote) : AgentGrain.Operation :=
  .settle (Int.ofNat quote.amount)

theorem Quote.operation_after (quote : Quote) (state : AgentGrain.State) :
    quote.operation.after state = AgentGrain.settle state (Int.ofNat quote.amount) := rfl

theorem Quote.charge_within_hold (quote : Quote) :
    0 ≤ (Int.ofNat quote.amount : Int) ∧
      (Int.ofNat quote.amount : Int) ≤ Int.ofNat quote.reserve := by
  constructor
  · exact Int.natCast_nonneg _
  · exact Int.ofNat_le.mpr quote.amountBound

/-- The controller must establish this equality from the fresh signed
provider state; the quote's reserve field alone is not a receipt. -/
theorem Quote.charge_within_signed_hold (quote : Quote) (state : AgentGrain.State)
    (held : state.reserved = Int.ofNat quote.reserve) :
    0 ≤ (Int.ofNat quote.amount : Int) ∧
      (Int.ofNat quote.amount : Int) ≤ state.reserved := by
  simpa [held] using quote.charge_within_hold

theorem Quote.exact_budget_change (quote : Quote) (state : AgentGrain.State) :
    (quote.operation.after state).remaining +
      (quote.operation.after state).reserved =
      state.remaining + state.reserved - Int.ofNat quote.amount := by
  simp [Quote.operation_after, AgentGrain.settle]

/-- Once the native receiver admits the exact authored settlement, its budget
decreases by precisely the Lean quote. The quote does not itself prove receipt
authenticity, authority, or receiver admission. -/
theorem Quote.admitted_budget_nonincrease (quote : Quote) (state : AgentGrain.State)
    (admitted : AgentGrain.accepts state (quote.operation.after state) = true) :
    (quote.operation.after state).remaining +
      (quote.operation.after state).reserved ≤ state.remaining + state.reserved :=
  AgentGrain.accepted_budget_nonincrease state (quote.operation.after state) admitted

end Minidregg.Kernel.ProviderMetering
