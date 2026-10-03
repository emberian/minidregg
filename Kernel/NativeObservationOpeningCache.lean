/- Exact source-owned salted opening reuse. Entries are keyed by the full
canonical packed bytes, including the write ratchet; roots are not cache keys.
Authorization and scope selection run afresh before using any cached renderer. -/
import Kernel.NativeHost

namespace Minidregg.Kernel.NativeObservationOpeningCache

open Minidregg.Compiler
open Minidregg.Compiler.NativeObservationCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.Store
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.NativeObservationController

set_option autoImplicit false

/-- Canonical entry, exact opening, and its already computed leaf. The renderer
chooses visibility without recomputing either the salt or the leaf hash. -/
def prepare {L : Layout.{0, 0, 0}} (wire : StoreCodec.Wire L) (store : Store L) :
    List (Minidregg.Theory.Store.Entry L × StoreCodec.Opening × List UInt8) :=
  (StoreCodec.entries wire store).map fun entry =>
    let opened := StoreCodec.opening wire store entry
    (entry, opened, opened.leaf)

def render {L : Layout.{0, 0, 0}} (visible : Address L → Prop) [DecidablePred visible]
    (prepared : List (Minidregg.Theory.Store.Entry L × StoreCodec.Opening × List UInt8)) :
    List StoreHiding.Item :=
  prepared.map fun item => if visible item.1.1 then .inl item.2.1 else .inr item.2.2

theorem render_prepare {L : Layout.{0, 0, 0}} (wire : StoreCodec.Wire L)
    (store : Store L) (visible : Address L → Prop) [DecidablePred visible] :
    render visible (prepare wire store) = StoreHiding.items wire visible store := by
  simp only [render, prepare, StoreHiding.items, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro entry _
  unfold StoreHiding.itemOf
  split <;> rfl

/-- This renderer certifies representation equality for every reader scope. -/
abbrev OpeningProvider := (fields : Option (Finset CellField)) →
  (packed : PackedCell CanonicalCellRegistry.registry) →
  { view : OpeningView // view = openingView fields packed }

def ordinaryOpening : OpeningProvider := fun fields packed =>
  ⟨openingView fields packed, rfl⟩

def resourceViewUsing (opening : OpeningProvider) (fields : Option (Finset CellField))
    (packed : PackedCell CanonicalCellRegistry.registry) (balances : List (Nat × Int))
    (computeQuote : Option RunComputeView.ComputeQuote := none) : ResourceView :=
  (packed.payload.root,
    PackedCell.bytes CanonicalCellRegistry.registry
      (ResourceObservationAdmission.narrowPacked fields packed),
    ResourceObservationAdmission.narrowBalances fields balances,
    (opening fields packed).val, computeQuote)

theorem resourceViewUsing_exact (opening : OpeningProvider)
    (fields : Option (Finset CellField)) (packed : PackedCell CanonicalCellRegistry.registry)
    (balances : List (Nat × Int)) (quote : Option RunComputeView.ComputeQuote) :
    resourceViewUsing opening fields packed balances quote =
      resourceView fields packed balances quote := by
  simp only [resourceViewUsing, resourceView, (opening fields packed).property]

/-- Only resource rendering differs. All non-resource views use the original
controller, including at-height authority. The equality below checks this seam. -/
def queryResultUsing {deployment : CanonicalCellRegistry.Deployment}
    {durable : NativeHost.Durable} {F : Type} [Field F] [DecidableEq F]
    {context : Context deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {genesisHeight : Nat} {intent : Intent}
    (accepted : AuthorizedIntent context profile federation genesisHeight intent)
    (opening : OpeningProvider) : Except RefusalReason (List UInt8) := do
  let .query query := intent.purpose | throw .malformed
  match query.view with
  | .resource | .resourceScope =>
      if present : 0 < intent.grants.length then
        let grant := intent.grants.get ⟨0, present⟩
        let checked := accepted.grants ⟨0, present⟩
        let some stored := CredentialAuthorityState.readCapability context.authority.snapshot.cell
          grant.kind grant.capability | throw .malformed
        let view := resourceViewUsing opening stored.head.scope.fields
          checked.selected.packed checked.selected.accountBalances
          (if query.kind = .account then
            RunComputeView.load deployment durable.snapshot intent.subject else none)
        if query.view == .resource then pure (resourceViewCodec.encode view)
        else pure (resourceScopeViewCodec.encode
          (grant.kind, grant.capability.value, stored.head.scope.fields, view))
      else throw .malformed
  | _ => accepted.queryResult

theorem queryResultUsing_exact {deployment : CanonicalCellRegistry.Deployment}
    {durable : NativeHost.Durable} {F : Type} [Field F] [DecidableEq F]
    {context : Context deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {federation : FederationId} {genesisHeight : Nat} {intent : Intent}
    (accepted : AuthorizedIntent context profile federation genesisHeight intent)
    (opening : OpeningProvider) : queryResultUsing accepted opening = accepted.queryResult := by
  cases purpose : intent.purpose with
  | prepare preparation => simp [queryResultUsing, AuthorizedIntent.queryResult, purpose]
  | query query =>
      cases view : query.view <;>
        simp [queryResultUsing, AuthorizedIntent.queryResult, purpose, view, resourceViewUsing_exact] <;> rfl

/-- Cached data remain private to the native Host. Every possible scope is
certified against the exact old opening, rather than retaining a reader view. -/
structure Entry where
  packed : PackedCell CanonicalCellRegistry.registry
  bytes : List UInt8
  bytesExact : bytes = PackedCell.bytes CanonicalCellRegistry.registry packed
  render : Option (Finset CellField) → OpeningView
  renderExact : ∀ fields, render fields = openingView fields packed

def Entry.prepare (packed : PackedCell CanonicalCellRegistry.registry) : Entry :=
  match selected : CanonicalCellRegistry.wire? packed.kind with
  | none => ⟨packed, PackedCell.bytes _ packed, rfl,
      fun _ => ([], []), by intro fields; simp [openingView, selected]⟩
  | some wire =>
      let prepared := NativeObservationOpeningCache.prepare wire packed.payload.logical
      ⟨packed, PackedCell.bytes _ packed, rfl,
        fun fields => (StoreCodec.frame wire,
          NativeObservationOpeningCache.render (ResourceObservationAdmission.Visible fields packed.kind) prepared),
        by
          intro fields
          simp only [openingView, selected]
          change (StoreCodec.frame wire, NativeObservationOpeningCache.render
            (ResourceObservationAdmission.Visible fields packed.kind)
            (NativeObservationOpeningCache.prepare wire packed.payload.logical)) = _
          rw [render_prepare]⟩

abbrev Cache := List Entry

/-- Only byte equality can reuse a retained packed value. The lawful codec
turns this into exact value equality; collision resistance is not a premise. -/
def provider (cache : Cache) : OpeningProvider := fun fields packed =>
  let bytes := PackedCell.bytes CanonicalCellRegistry.registry packed
  match cache.find? (fun entry => entry.bytes == bytes) with
  | none => ordinaryOpening fields packed
  | some entry =>
      if same : entry.bytes = bytes then
        have encoded : PackedCell.bytes CanonicalCellRegistry.registry entry.packed =
            PackedCell.bytes CanonicalCellRegistry.registry packed := by
          rw [← entry.bytesExact]; exact same
        have exact : entry.packed = packed := by
          have bytesExact : CanonicalCellRegistry.cellCodec.encode entry.packed =
              CanonicalCellRegistry.cellCodec.encode packed := encoded
          have decoded := congrArg CanonicalCellRegistry.cellCodec.decode bytesExact
          rw [CanonicalCellRegistry.cellCodec.decode_encode,
            CanonicalCellRegistry.cellCodec.decode_encode] at decoded
          exact Option.some.inj decoded
        ⟨entry.render fields, by rw [entry.renderExact, exact]⟩
      else ordinaryOpening fields packed

/-- A fixed entry ceiling bounds retention. A single currently accepted source
view can be large, but the cache cannot retain an unbounded history of views. -/
def retain (cache : Cache) (packed : PackedCell CanonicalCellRegistry.registry) : Cache :=
  let bytes := PackedCell.bytes CanonicalCellRegistry.registry packed
  let entry := match cache.find? (fun entry => entry.bytes == bytes) with
    | some retained => retained
    | none => Entry.prepare packed
  (entry :: cache.filter (fun old => old.bytes != bytes)).take 16

theorem retain_bounded (cache : Cache) (packed : PackedCell CanonicalCellRegistry.registry) :
    (retain cache packed).length ≤ 16 := by
  simp only [retain, List.length_take]
  exact Nat.min_le_left _ _

/-- Even arbitrary retained older revisions cannot change the returned opening;
full canonical equality is required before reusing their renderer. -/
theorem provider_exact (cache : Cache) (fields : Option (Finset CellField))
    (packed : PackedCell CanonicalCellRegistry.registry) :
    (provider cache fields packed).val = openingView fields packed :=
  (provider cache fields packed).property

/-- Admit first. A refused request cannot populate the cache, and no cached
entry supplies a key, grant, current policy decision, or historical authority. -/
def queryLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (cache : IO.Ref Cache) (bytes : List UInt8) : IO (Except Refusal (List UInt8)) := do
  let some signed := NativeObservationCodec.signedCodec.decode bytes
    | return .error (.of .malformed)
  match ← NativeObservationController.authorize config.signature
      (NativeHost.observationContext config opened) config.profile config.federation
      config.genesisHeight signed with
  | .error refusal => return .error refusal
  | .ok token =>
      match signed.challenge.intent.purpose with
      | .query query =>
          if query.view == .resource || query.view == .resourceScope then
            if present : 0 < signed.challenge.intent.grants.length then
              let packed := (token.grants ⟨0, present⟩).selected.packed
              cache.modify (fun old => retain old packed)
      | _ => pure ()
      match queryResultUsing token (provider (← cache.get)) with
      | .ok view => return .ok view
      | .error reason => return .error (.of reason)

/-- Same bounded coherent batch and all-or-nothing reply as NativeHost. Only
resource opening construction changes, by the exact-result theorem. -/
def queryWireLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (cache : IO.Ref Cache) (bytes : List UInt8) : IO (Except Refusal (List UInt8)) := do
  if !NativeObservationCodec.isBatch bytes then return ← queryLoaded config opened cache bytes
  unless bytes.length ≤ NativeObservationCodec.maxBatchBytes do
    return .error (.of .malformed)
  let some observations := NativeObservationCodec.batchCodec.decode bytes
    | return .error (.of .malformed)
  unless NativeObservationCodec.validBatch observations do return .error (.of .malformed)
  let mut views : List (List UInt8) := []
  for observation in observations do
    match ← queryLoaded config opened cache observation with
    | .error refusal => return .error refusal
    | .ok view => views := views ++ [view]
  let encoded := NativeObservationCodec.batchCodec.encode views
  if encoded.length ≤ NativeObservationCodec.maxBatchBytes then return .ok encoded
  else return .error (.of .malformed)

#assert_axioms resourceViewUsing_exact
#assert_axioms queryResultUsing_exact
#assert_axioms render_prepare
#assert_axioms provider_exact
#assert_axioms retain_bounded

end Minidregg.Kernel.NativeObservationOpeningCache
