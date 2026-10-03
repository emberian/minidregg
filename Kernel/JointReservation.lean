/- Exact reservation obligations over native receiver intents. This module owns
resource exclusion and charge reservation; it does not assert that an ordinary
execution grant also authorizes an irrevocable reservation. Source policy must
admit that action before the agreement driver finalizes YES.
-/
import Kernel.JointDecisionRecovery

namespace Minidregg.Kernel.JointReservation

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.JointInvocationCandidate
open Minidregg.Kernel.JointDecisionRecovery

set_option autoImplicit false

structure Reservation where
  domain : Digest
  candidateBytes : List UInt8
  lineage : StableNullifier
  intent : IntentRecord
  sourceImageBytes : List UInt8
  generation : Nat

/-- Derived from the physical effect, including authority/clock/audience guards. -/
def Reservation.footprint (r : Reservation) : List CellId :=
  r.intent.writes.map DataWrite.cellId ++ r.intent.readGuards.map ReadGuard.cellId

/-- Compatibility protects exact read/write dependencies and single-use claims.
Read/read sharing is allowed; pairwise compatibility alone is NOT a proof of an
arbitrary application set invariant. Source evaluation supplies that invariant. -/
def Compatible (held : Reservation) (next : IntentRecord) : Prop :=
  (∀ write ∈ next.writes, write.cellId ∉ held.footprint) ∧
  (∀ guard ∈ next.readGuards, guard.cellId ∉ held.intent.writes.map DataWrite.cellId) ∧
  (∀ claim ∈ next.nullifiers, claim ∉ held.intent.nullifiers)

instance (held : Reservation) (next : IntentRecord) : Decidable (Compatible held next) :=
  inferInstanceAs (Decidable (
    (∀ write ∈ next.writes, write.cellId ∉ held.footprint) ∧
    (∀ guard ∈ next.readGuards, guard.cellId ∉ held.intent.writes.map DataWrite.cellId) ∧
    (∀ claim ∈ next.nullifiers, claim ∉ held.intent.nullifiers)))

abbrev Table := List Reservation

def heldCharge (domain : Digest) (table : Table) : Charge :=
  Charge.aggregate ((table.filter (fun r => r.domain == domain)).map (fun r => r.intent.exactCharge))

/-- This check applies to every ordinary local commit as well as new joint
reservations. Excluding the selected reservation at its installation is a typed
controller action, not a client-selected ignore list. -/
def allowed (domain : Digest) (table : Table) (intent : IntentRecord)
    (available : Charge) : Bool :=
  decide (∀ held ∈ table, held.domain = domain → Compatible held intent) &&
    Charge.fundedCheck (heldCharge domain table + intent.exactCharge) available

def reserve {Custody F : Type} [Field F] [DecidableEq F]
    (codec : StreamCodec Custody) (table : Table) {plan : Plan Custody}
    (i : Fin plan.candidate.participants.length)
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {command : Command} {signed : SignedCommand}
    (admission : CurrentAdmission deployment profile ambient durable command signed
      plan.candidate.participants[i]) : Option (Table × LocalYesProposal) := do
  let proposal ← proposeLocalYes codec i admission
  let projection := plan.candidate.participants[i]
  if !(allowed projection.domain table projection.intent durable.snapshot.model.available) then none
  else if ∃ held ∈ table, held.domain = projection.domain ∧ held.lineage = plan.candidate.lineage then none
  else
    let reservation : Reservation :=
      ⟨projection.domain, proposal.candidateBytes, plan.candidate.lineage,
        projection.intent, proposal.sourceImageBytes, projection.generation⟩
    some (table ++ [reservation], proposal)

/-- No timeout-based removal exists. Removal needs the shared Abort outcome or
actual completed installation; retention/epoch handoff keeps the whole table. -/
def releaseAborted {Custody : Type} (codec : StreamCodec Custody) {plan : Plan Custody}
    (state : State plan) (_aborted : Abort state) (table : Table) : Table :=
  table.filter (fun r => r.candidateBytes != (candidateStream codec).encode plan.candidate)

theorem allowed_compatible (domain : Digest) (table : Table) (intent : IntentRecord)
    (available : Charge) (accepted : allowed domain table intent available = true)
    (held : Reservation) (member : held ∈ table) (sameDomain : held.domain = domain) :
    Compatible held intent := by
  simp only [allowed, Bool.and_eq_true] at accepted
  have all : ∀ held ∈ table, held.domain = domain → Compatible held intent :=
    of_decide_eq_true accepted.1
  exact all held member sameDomain

theorem allowed_funded (domain : Digest) (table : Table) (intent : IntentRecord)
    (available : Charge) (accepted : allowed domain table intent available = true) :
    heldCharge domain table + intent.exactCharge ≤ available := by
  simp only [allowed, Bool.and_eq_true] at accepted
  exact (Charge.fundedCheck_eq_true_iff _ _).mp accepted.2

/-- An unrelated admitted install cannot alter bytes protected by a reservation.
This uses the actual durable installer and does not assume hash injectivity. -/
theorem compatible_install_preserves_bytes {rootBytes : List UInt8 → Digest}
    (held : Reservation) (intent : DataIntent rootBytes)
    (compatible : Compatible held (IntentRecord.ofIntent intent))
    (before : DataSnapshot rootBytes) (cell : CellId) (guarded : cell ∈ held.footprint) :
    (DataSnapshot.install before intent).canonicalBytes cell = before.canonicalBytes cell := by
  have missing : cell ∉ intent.writes.map DataWrite.cellId := by
    intro member
    obtain ⟨write, inWrites, same⟩ := List.mem_map.mp member
    have outside := compatible.1 write inWrites
    apply outside
    simpa [same] using guarded
  rw [DataSnapshot.install_canonicalBytes,
    Minidregg.Kernel.DurableReceiver.lookupPostBytes_missing intent.writes cell missing]
  rfl

/-- In particular, current authority and clock guards retain their exact roots
when every concurrent commit passes the same reservation gate. -/
theorem compatible_install_preserves_root {rootBytes : List UInt8 → Digest}
    (held : Reservation) (intent : DataIntent rootBytes)
    (compatible : Compatible held (IntentRecord.ofIntent intent))
    (before : DataSnapshot rootBytes) (cell : CellId) (guarded : cell ∈ held.footprint) :
    (DataSnapshot.install before intent).model.roots cell = before.model.roots cell := by
  rw [← (DataSnapshot.install before intent).coherent cell,
    compatible_install_preserves_bytes held intent compatible before cell guarded,
    before.coherent cell]

end Minidregg.Kernel.JointReservation
