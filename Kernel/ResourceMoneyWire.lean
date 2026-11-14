/- Typed declarations only. Account/capability/signature identity is always the
containing native target; no Book post or raw balance write crosses this wire. -/
module

public import Kernel.ResourceMoneyOperationDomain

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Kernel.ResourceMoneyWire

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CanonicalResourceKernel
set_option autoImplicit false

/-- Shared with the existing compute-funding payload, with unchanged fields. -/
structure FundingConsent where
  asset : Nat
  credits : Nat
  expectedPayerBalance : Int
  expectedBookRoot : Digest
  deriving DecidableEq, Repr

def fundingStream : StreamCodec FundingConsent :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product Minidregg.Compiler.IntStream.intStream digestStream)))
    (fun funding => (funding.asset, funding.credits,
      funding.expectedPayerBalance, funding.expectedBookRoot))
    (fun (asset, credits, payer, bookRoot) => ⟨asset, credits, payer, bookRoot⟩)
    (by intro funding; cases funding; rfl)

structure ApplicationBatch where
  expectedBookRoot : Digest
  operations : List Operation
  deriving DecidableEq, Repr

def batchStream : StreamCodec ApplicationBatch :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.list CanonicalResourcePageMaterializer.operationStream))
    (fun batch => (batch.expectedBookRoot, batch.operations))
    (fun (root, operations) => ⟨root, operations⟩)
    (by intro batch; cases batch; rfl)

/-- Exactly one signed account leg carries the global ordered batch. Every
debit position belongs to its posting source's signed account leg. A payer can
add funding here, retaining one actual account target instead of two aliases. -/
structure Consent where
  batch : Option ApplicationBatch
  positions : List Nat
  funding : Option FundingConsent
  deriving DecidableEq, Repr

def consentStream : StreamCodec Consent :=
  StreamCodec.xmap
    (StreamCodec.product (StreamCodec.option batchStream)
      (StreamCodec.product (StreamCodec.list StreamCodec.nat)
        (StreamCodec.option fundingStream)))
    (fun consent => (consent.batch, consent.positions, consent.funding))
    (fun (batch, positions, funding) => ⟨batch, positions, funding⟩)
    (by intro consent; cases consent; rfl)

/-- Extracted by the native receiver from an actual signed account target. -/
structure Entry where
  account : AccountId
  consent : Consent
  deriving DecidableEq, Repr

def PositionSource (batch : ApplicationBatch) (entry : Entry) (position : Nat) : Prop :=
  match batch.operations[position]? with
  | none => False
  | some operation => operation.posting.source = entry.account

instance (batch : ApplicationBatch) (entry : Entry) (position : Nat) :
    Decidable (PositionSource batch entry position) := by
  unfold PositionSource
  split <;> infer_instance

/-- Every position is in range and names the containing account's source;
every operation has exactly one source consent and actual destination member.
Position uniqueness prevents counting one reserved debit twice. -/
def Covered (entries : List Entry) (batch : ApplicationBatch) : Prop :=
  (entries.map Entry.account).Nodup ∧
  (∀ entry ∈ entries, entry.consent.positions.Nodup ∧
    ∀ position ∈ entry.consent.positions,
      PositionSource batch entry position) ∧
  (∀ position ∈ List.finRange batch.operations.length,
    ∃ entry ∈ entries, position.val ∈ entry.consent.positions ∧
      (batch.operations[position]).posting.source = entry.account) ∧
  (∀ operation ∈ batch.operations,
    ∃ entry ∈ entries, operation.posting.destination = entry.account)

instance (entries : List Entry) (batch : ApplicationBatch) : Decidable (Covered entries batch) := by
  unfold Covered
  infer_instance

/-- Reuse the production verb distinctions; ordinary payment authority does
not issue an asset, extend credit in it (a floor is set from the issuer well,
under the same `mintAsset` verb as a mint), or destroy it. These are required from the SAME admitted
account capability in addition to whole-command/current-law admission. -/
def operationVerb : Operation → Verb .account
  | .mint _ _ _ => .mintAsset
  | .burn _ _ _ => .burnAsset
  | .setFloor _ _ _ => .mintAsset
  | _ => .transfer

def verbs (batch : ApplicationBatch) (entry : Entry) : List (Verb .account) :=
  (entry.consent.positions.filterMap fun position =>
    (batch.operations[position]?).map operationVerb).eraseDups

end Minidregg.Kernel.ResourceMoneyWire
