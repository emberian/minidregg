/- Signed account views expose the authenticated reader's admitted compute cut.
No quote is invented for missing activation, invalid history, or missing source
cells. The Book commitment is public consent data; issuer balances remain private.
-/
import Kernel.RunComputeBudgetDomain
import Kernel.ClockCellDomain

namespace Minidregg.Kernel.RunComputeView

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

structure ComputeQuote where
  subject : Nat
  bookRoot : Digest
  day : Nat
  usedSteps : Nat
  /-- Daily allowance, not the remaining allowance: subtract usedSteps. -/
  freeSteps : Nat
  creditsPerStep : Nat
  creditAsset : Option Nat
  deriving DecidableEq, Repr

def computeQuoteStream : StreamCodec ComputeQuote :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digestStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product StreamCodec.nat (StreamCodec.option StreamCodec.nat)))))))
    (fun quote => (quote.subject, quote.bookRoot, quote.day, quote.usedSteps,
      quote.freeSteps, quote.creditsPerStep, quote.creditAsset))
    (fun (subject, bookRoot, day, usedSteps, freeSteps, creditsPerStep, creditAsset) =>
      ⟨subject, bookRoot, day, usedSteps, freeSteps, creditsPerStep, creditAsset⟩)
    (by intro quote; cases quote; rfl)

/-- All inputs come from the same durable snapshot. Usage belongs to the signed
reader, independently of which account that reader is permitted to observe. -/
def load (deployment : CanonicalCellRegistry.Deployment)
    (physical : RunComputeBudgetDomain.Physical) (subject : SubjectId) : Option ComputeQuote := do
  let pay ← PayCellDomain.load deployment physical
  let clock ← ClockCellDomain.load deployment physical
  let _book ← RunComputeBudgetDomain.loadBook deployment physical
  let activation ← PayCell.computeActivationOf pay.cell.logical
  let quoted ← (RunComputeBudget.quote subject clock.clock activation
    (PayCell.computeUsageAt pay.cell.logical subject.value) 0).toOption
  let asset := (PayCell.tariffOf pay.cell.logical).bind fun tariff =>
    if tariff.valid then some tariff.asset else none
  pure ⟨subject.value, physical.model.roots (RunComputeBudgetDomain.bookId deployment),
    quoted.day, quoted.usedBefore, RunComputeBudget.freeStepsPerDay, 1, asset⟩

end Minidregg.Kernel.RunComputeView
