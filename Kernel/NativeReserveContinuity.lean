/-
An exact, read-only continuity check for a confirmed provider reservation.

The caller retains the full receipt and signed call bytes returned by its
original reserve submission. The session is verifier-minted from admitted
history and refreshed against current physical Store bytes before this check.
No final-value comparison can substitute for the suffix write scan: a later
settle or re-reserve may restore the same visible coordinates. This checker
establishes reservation continuity, not all effective provider rights:
the physical controller must also check fresh signed parent/provider state.
-/
import Kernel.NativeHostSession

namespace Minidregg.Kernel.NativeReserveContinuity

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Compiler
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

/-- Current authority support is used to refuse an ordinary command that
purports to target an authority cell. An ordinary invocation's admitted marker
does write an authority nullifier, so these cells must not be used as a blunt
physical-write exclusion for otherwise unrelated invocations. -/
def authorityCells {config : Config} (session : NativeHostSession.Session config) :
    List CellId :=
  let snapshot := session.opened.authority.snapshot
  ⟨config.deployment.authorityCatalogueId⟩ ::
    snapshot.catalogue.pages.map (·.cellId) ++
    snapshot.entries.filterMap (fun entry =>
      match entry with
      | .policy _ _ _ address =>
          some ⟨PolicySourceCell.physicalId config.deployment.domain address⟩
      | _ => none)

def writesCell (record : DurableReceiver.IntentRecord) (cell : CellId) : Prop :=
  cell ∈ record.writes.map DataWrite.cellId

instance (record : DurableReceiver.IntentRecord) (cell : CellId) :
    Decidable (writesCell record cell) := inferInstanceAs
      (Decidable (cell ∈ record.writes.map DataWrite.cellId))

def Untouched (records : List DurableReceiver.IntentRecord) (cells : List CellId) : Prop :=
  records.all (fun record => cells.all (fun cell => !decide (writesCell record cell))) = true

instance (records : List DurableReceiver.IntentRecord) (cells : List CellId) :
    Decidable (Untouched records cells) := by
  unfold Untouched
  infer_instance

/-- A checked suffix preserves each protected cell through canonical durable
replay. This is a general property of the existing executor, independent of a
particular provider history or a sampled Store image. -/
theorem untouched_preserves_cell (rootBytes : List UInt8 → Digest)
    (before after : DataSnapshot rootBytes)
    (records : List DurableReceiver.IntentRecord) (cells : List CellId)
    (untouched : Untouched records cells)
    (restored : DurableReceiver.replay rootBytes before records = some after)
    (cell : CellId) (member : cell ∈ cells) :
    after.canonicalBytes cell = before.canonicalBytes cell := by
  have missing : cell ∉ records.flatMap (fun record => record.writes.map DataWrite.cellId) := by
    intro present
    simp only [List.mem_flatMap] at present
    rcases present with ⟨record, inRecords, inWrites⟩
    have allRecords := List.all_eq_true.mp untouched
    have allCells := List.all_eq_true.mp (allRecords record inRecords)
    have noWrite := allCells cell member
    have absent : decide (writesCell record cell) = false := by
      cases status : decide (writesCell record cell) <;> simp [status] at noWrite ⊢
    exact (decide_eq_false_iff_not.mp absent) inWrites
  exact DurableReceiver.replay_outside_support rootBytes before records cell missing after restored

/-- The only later ingress admitted here is an ordinary resource invocation.
Birth and authority management calls can change grants, keys, policy or
revocation state and therefore keep this conservative family fence closed.
Ordinary invocations add an authority nullifier marker, so their physical
authority write cannot by itself close the fence. This family check does not
prove that an ordinary invocation left every parent/policy dependency intact;
the caller composes fresh signed parent and provider checks. -/
def ordinaryOther {config : Config} (session : NativeHostSession.Session config)
    (providerCell : CellId) (record : DurableReceiver.IntentRecord) : Bool :=
  let bytes := record.event.canonicalBytes
  if (CapabilityRevocationReceiver.decodeIngress bytes).isSome ||
      (ResourceBirthPolicyController.Concrete.decodeIngress bytes).isSome ||
      (PolicyInstallReceiver.decodeIngress bytes).isSome ||
      (CapabilityDelegationReceiver.decodeIngress bytes).isSome then false
  else
    match DeclaredResourceController.decodeSignedBytes bytes with
    | some (_, _, signed) =>
        match DeclaredResourceController.commandCodec.decode signed.commandBytes with
        | some command =>
            command.targets.all (fun target =>
              decide (⟨target.target⟩ ∉ authorityCells session)) &&
            !decide (writesCell record providerCell)
        | none => false
    | none => false

/-- The public host call is an outer dispatch frame; the durable event retains
the family's canonical ingress. Decode the outer frame in Lean before comparing
it with original admitted event bytes. -/
def reserveIngress? (config : Config) (reserveCall : List UInt8) : Option (List UInt8) :=
  match NativeHostCodec.callCodec.decode reserveCall with
  | some (.invoke signed) =>
      some (DeclaredResourceController.signedBytes config.deployment.domain
        config.profile.semantics signed)
  | _ => none

def SafeSuffix {config : Config} (session : NativeHostSession.Session config)
    (providerCell : CellId) (records : List DurableReceiver.IntentRecord) : Prop :=
  records.all (ordinaryOther session providerCell) = true

instance {config : Config} (session : NativeHostSession.Session config)
    (providerCell : CellId) (records : List DurableReceiver.IntentRecord) :
    Decidable (SafeSuffix session providerCell records) := by
  unfold SafeSuffix
  infer_instance

theorem ordinaryOther_no_provider_write {config : Config}
    (session : NativeHostSession.Session config) (providerCell : CellId)
    (record : DurableReceiver.IntentRecord)
    (safe : ordinaryOther session providerCell record = true) :
    ¬ writesCell record providerCell := by
  dsimp [ordinaryOther] at safe
  split at safe <;> try simp at safe
  split at safe <;> try simp at safe
  split at safe <;> try simp at safe
  exact safe.2

theorem safeSuffix_no_provider_write {config : Config}
    (session : NativeHostSession.Session config) (providerCell : CellId)
    (records : List DurableReceiver.IntentRecord)
    (safe : SafeSuffix session providerCell records)
    (record : DurableReceiver.IntentRecord) (member : record ∈ records) :
    ¬ writesCell record providerCell :=
  ordinaryOther_no_provider_write session providerCell record
    ((List.all_eq_true.mp safe) record member)

/-- The result records exact evidence, rather than exporting a bare Boolean
whose connection to the verified Store could be lost by the caller. -/
structure Continuity {config : Config} (session : NativeHostSession.Session config)
    (anchor : NativeHostCodec.Receipt) (reserveCall : List UInt8)
    (providerCell : CellId) : Type where
  positive : 0 < anchor.acceptedCount
  receiptExact : session.verified.receipts[anchor.acceptedCount - 1]? = some anchor
  ingress : List UInt8
  reserveParsed : reserveIngress? config reserveCall = some ingress
  callExact :
    (session.target.image.accepted[anchor.acceptedCount - 1]?).map
      (fun record => record.event.canonicalBytes) = some ingress
  providerWritten :
    (session.target.image.accepted[anchor.acceptedCount - 1]?).any
      (fun record => decide (writesCell record providerCell)) = true
  suffixSafe :
    SafeSuffix session providerCell
      (session.target.image.accepted.drop anchor.acceptedCount)

theorem Continuity.no_later_provider_write {config : Config}
    {session : NativeHostSession.Session config} {anchor : NativeHostCodec.Receipt}
    {reserveCall : List UInt8} {providerCell : CellId}
    (checked : Continuity session anchor reserveCall providerCell)
    (record : DurableReceiver.IntentRecord)
    (later : record ∈ session.target.image.accepted.drop anchor.acceptedCount) :
    ¬ writesCell record providerCell :=
  safeSuffix_no_provider_write session providerCell _ checked.suffixSafe record later

/-- Requires the original complete receipt and original signed reserve call.
The receipt is checked against the semantic replay's recomputed prefix receipt,
including transaction, event, accepted count and prefix image boundary.
The physical caller must refresh the session immediately before invoking this
check; it still owns the external send race and exclusive upstream custody. -/
def check {config : Config} (session : NativeHostSession.Session config)
    (anchor : NativeHostCodec.Receipt) (reserveCall : List UInt8)
    (providerCell : CellId) : Except String (Continuity session anchor reserveCall providerCell) := do
  if positive : 0 < anchor.acceptedCount then
    if receiptExact :
        session.verified.receipts[anchor.acceptedCount - 1]? = some anchor then
      match parsed : reserveIngress? config reserveCall with
      | none => .error "reserve call is not a canonical signed invocation"
      | some ingress =>
          if callExact :
              (session.target.image.accepted[anchor.acceptedCount - 1]?).map
                (fun record => record.event.canonicalBytes) = some ingress then
            if providerWritten :
                (session.target.image.accepted[anchor.acceptedCount - 1]?).any
                  (fun record => decide (writesCell record providerCell)) = true then
              if suffixSafe :
                  SafeSuffix session providerCell
                    (session.target.image.accepted.drop anchor.acceptedCount) then
                return ⟨positive, receiptExact, ingress, parsed,
                  callExact, providerWritten, suffixSafe⟩
              else .error "provider rewrite or authority-changing ingress after reserve"
            else .error "confirmed call did not write the provider resource"
          else .error "confirmed reserve call differs from admitted history"
    else .error "confirmed reserve receipt differs from admitted prefix"
  else .error "reserve receipt has zero accepted count"

end Minidregg.Kernel.NativeReserveContinuity
