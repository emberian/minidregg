/-
Stable quote commitments and exact-duration paid-entry quotes. Only economic
inputs and the deployment's source profile occur here: no world root, authority
revision, journal length or unrelated resource state can invalidate a quote.
The receiver supplies its actual account birth fee, computed with its ordinary
birth descriptor, and uses these same constructors when receiving payment.
-/
import Kernel.PayEnrolClaim
import Kernel.PayEnrolQuote
import Compiler.CanonicalRuntimeProfileCore

namespace Minidregg.Kernel.PayEnrolPricing

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Theory.ResourceBirth (CreationTariff)
open Minidregg.Kernel.PayTariff
open Minidregg.Kernel.PayEnrolClaim (FixedQuote Mode)
set_option autoImplicit false

/-- The factory tariff is committed in full, including destination and asset. -/
def creationTerms (tariff : CreationTariff) : List Nat :=
  [tariff.base, tariff.perBirth, tariff.perGrant, tariff.perInitialPayloadByte,
    tariff.collector, tariff.asset]

def quoteTerms (quote : FixedQuote) : List Nat :=
  [quote.amountAtomic, quote.credit, quote.birthFee, quote.requestedWeeks,
    quote.membershipCredit, quote.creditedRemainder, quote.minimumStarterCredit]

/-- Stable public deployment identity and exact receiving asset/recipient.
The full source profile belongs to pricing, so an upgrade can retain a stale
quote as pending value instead of misclassifying it as a foreign deployment. Caller-selected chain RPC endpoints are deliberately absent. -/
def deploymentContextCommitment (domain expectedSeed : Digest)
    (mint tokenProgram recipient : Address32) : Digest :=
  (Sp800185Cshake256.hash "DREGG/PAY/DEPLOYMENT/v2".toUTF8.toList
    (digestStream.encode domain ++ digestStream.encode expectedSeed ++
      bytesStream.encode mint ++ bytesStream.encode tokenProgram ++
      bytesStream.encode recipient)).digest

def deploymentCommitment (domain expectedSeed : Digest) (tariff : Tariff)
    (recipient : Address32) : Digest :=
  deploymentContextCommitment domain expectedSeed tariff.mint tariff.tokenProgram recipient

/-- Expiry and current key/epoch are signed separately by the v2 memo/claim
acceptance. Their passage does not change the price commitment itself. -/
def pricingCommitment (semantics : Digest) (tariff : Tariff)
    (creation : CreationTariff) (template : CanonicalRuntimeProfile.FactoryTemplate)
    (mode : Mode) (quote : FixedQuote) : Digest :=
  (Sp800185Cshake256.hash "DREGG/PAY/EXACT-WEEKS-PRICING/v2".toUTF8.toList
    (digestStream.encode semantics ++ tariffStream.encode tariff ++
      (StreamCodec.list StreamCodec.nat).encode (creationTerms creation) ++
      CanonicalRuntimeProfile.factoryTemplateStream.encode template ++
      ([match mode with | .enroll => 1 | .renew => 2] : List UInt8) ++
      (StreamCodec.list StreamCodec.nat).encode (quoteTerms quote))).digest

/-- A new purchase chooses the smallest atomic transfer covering the requested
split and journal floor. The same fixed-deposit receiver gate checks the result;
rounding remains spendable instead of purchasing unrequested extra weeks. -/
def quotePurchase (tariff : Tariff) (birthFee weeks starter : Nat) :
    Except PayEnrolClaim.QuoteReject FixedQuote :=
  let target := birthFee + weeks * tariff.weekCredit + starter
  let amount := max (PayEnrolQuote.atomicCeil target tariff.creditPerAtomic) tariff.journalFloor
  PayEnrolClaim.quoteFixed amount tariff birthFee weeks starter

theorem quotePurchase_split (tariff : Tariff) (birthFee weeks starter : Nat)
    (quote : FixedQuote) (accepted : quotePurchase tariff birthFee weeks starter = .ok quote) :
    quote.birthFee + quote.membershipCredit + quote.creditedRemainder = quote.credit ∧
      starter ≤ quote.creditedRemainder := by
  have split := PayEnrolClaim.quoteFixed_success_split _ tariff birthFee weeks starter quote accepted
  exact ⟨split.2.2.2.2.2.1, split.2.2.2.2.2.2⟩

private def fixtureTariff : Tariff :=
  { exampleTariff with
    creditPerAtomic := 1
    maxPerObservation := 100000
    nodeHourRate := 1
    enrolIndex := some 0
    journalFloor := 1 }

/-- The intended useful starting bundle is one week plus 347 spendable credits;
those credits are not silently converted into additional membership. -/
theorem useful_starter_survives :
    quotePurchase fixtureTariff 7 1 347 = .ok ⟨522, 522, 7, 1, 168, 347, 347⟩ := by
  set_option maxRecDepth 2048 in decide

#assert_axioms quotePurchase_split
#assert_axioms useful_starter_survives
end Minidregg.Kernel.PayEnrolPricing
