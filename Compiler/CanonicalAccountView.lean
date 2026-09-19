/- A source-owned private cut of the canonical Book. Both observation and
programmable account laws use this cut; unrelated accounts and lease records
are not scalar-oracle inputs to a caller's predicate. -/
import Compiler.CanonicalResourcePageMaterializer

namespace Minidregg.Compiler.CanonicalAccountView

open Minidregg.Theory
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

def accountBalanceMap (value : CanonicalResourceKernel.Book) (account : Nat) : Π₀ _ : Nat, Int :=
  DFinsupp.comapDomain' (fun asset => (account, asset))
    (h' := Prod.snd) (fun _ => rfl) value.balances

def accountCut (value : CanonicalResourceKernel.Book) (account : Nat) : List (Nat × Int) :=
  CanonicalResourcePageMaterializer.entries (accountBalanceMap value account)

theorem accountBalanceMap_exact (value : CanonicalResourceKernel.Book) (account asset : Nat) :
    accountBalanceMap value account asset = value.balance account asset := rfl

/-- Pointwise equality at this account suffices. There is deliberately no
premise on other balances, account registration, or lease records. -/
theorem accountCut_noninterference (left right : CanonicalResourceKernel.Book) (account : Nat)
    (same : ∀ asset, left.balance account asset = right.balance account asset) :
    accountCut left account = accountCut right account := by
  have equal : accountBalanceMap left account = accountBalanceMap right account := by
    ext asset
    exact same asset
  unfold accountCut
  rw [equal]

def balanceStream : StreamCodec (List (Nat × Int)) :=
  StreamCodec.list (StreamCodec.product StreamCodec.nat CanonicalResourcePageMaterializer.intStream)

private def byteSlots : Nat → List UInt8 → List (String × Int)
  | _, [] => []
  | offset, byte :: rest =>
      (s!"account/bytes/{offset}", Int.ofNat byte.toNat) :: byteSlots (offset + 1) rest

def slots (value : CanonicalResourceKernel.Book) (account : Nat) : List (String × Int) :=
  let balances := accountCut value account
  byteSlots 0 (balanceStream.encode balances) ++
    balances.map (fun pair => (s!"account/balance/{pair.1}", pair.2))

theorem slots_noninterference (left right : CanonicalResourceKernel.Book) (account : Nat)
    (same : ∀ asset, left.balance account asset = right.balance account asset) :
    slots left account = slots right account := by
  simp only [slots, accountCut_noninterference left right account same]

/-- info: 'Minidregg.Compiler.CanonicalAccountView.slots_noninterference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms slots_noninterference

end Minidregg.Compiler.CanonicalAccountView
