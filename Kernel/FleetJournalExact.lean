/-
# Kernel.FleetJournalExact -- the fleet reads off the journal index are the scans (statements)

Ops 101 and 180 were scans of the accepted log (`NativeHost.fleetIncomingFrom`; the head's
filter). They are now reads of journal sequence rows (`NativeHost.fleetHeadLight`,
`NativeHost.fleetIncomingLight`). These are the two exactness statements, over a log and the
recomputed sequence heights (`Theory.JournalSequences.heights`, which the kept rows equal:
`Theory.JournalSequences.index_from_replay`, `DurableIndex.IndexRows.indexed_changes_exact`).

Both are proved (`incomingExact`, `headExact`): a record yields an incoming entry, or is one
of a payer's turns, exactly when it carries the name (`incoming_isSome_iff`,
`paid_iff`), which without a collision is membership of the name's sequence
(`JournalIndex.mem_sequences_iff`); the rest is `Theory.JournalSequences.scanFrom_take_shift`,
`filter_length_eq_count` and `filter_getLast?`. The served read of those heights is
`NativeHost.sequencePosition` (the cursor's position, `Theory.JournalSequences.belowM`) and
`NativeHost.sequencePage` (`Theory.JournalSequences.pageM`): `belowM_pure`, `below_spec`,
`pageM_pure`, `page_rows`, with `drop_below_eq_filter` joining a position to a height cursor.
-/
module

public import Kernel.NativeHost
import Theory.AssertAxioms

@[expose] public section

namespace Minidregg.Kernel.FleetJournalExact

open Minidregg.Kernel.DurableReceiver (IntentRecord)

set_option autoImplicit false

/-- The Store heights (from 1) of the records in a name's sequence, recomputed over a log. -/
def heights (name : JournalIndex.Name) (log : List IntentRecord) : List Nat :=
  Theory.JournalSequences.heights (log.map JournalIndex.sequences) name.id

/-- **Op 180 is the scan.** For a log in which no other name shares the ledger's sequence id,
the first `limit` entries of the scan above `cursor` are the entries read back at the first
`limit` sequence heights above the cursor (a logical height is `genesis` plus the Store's). -/
def IncomingExact : Prop :=
  ∀ (genesis account : Nat) (topic : List UInt8) (cursor limit : Nat) (log : List IntentRecord),
    ¬ JournalIndex.Collides (.fleetIncoming account topic) log →
    (NativeHost.fleetIncomingFrom account topic cursor (genesis + 1) log).take limit =
      (((heights (.fleetIncoming account topic) log).filter
          (fun height => cursor - genesis < height)).take limit).filterMap
        (fun height => (log[height - 1]?).bind
          (NativeHost.fleetIncomingEntry? account topic (genesis + height)))

/-- The accepted fleet turns a payer paid for, by the scan op 101 used. -/
def paidBy (payer : Nat) (log : List IntentRecord) : List IntentRecord :=
  log.filter fun record =>
    match FleetTurn.decodeIngress record.event.canonicalBytes with
    | some ingress => ingress.command.payer == payer
    | none => false

/-- **Op 101 is the scan.** For a log in which no other name shares the payer's sequence id,
the number of turns is the sequence's count and the newest turn is the record at its last
height. -/
def HeadExact : Prop :=
  ∀ (payer : Nat) (log : List IntentRecord),
    ¬ JournalIndex.Collides (.fleetPayer payer) log →
    (paidBy payer log).length =
        Theory.JournalSequences.count (log.map JournalIndex.sequences) (JournalIndex.Name.fleetPayer payer).id ∧
      (paidBy payer log).getLast? =
        ((heights (.fleetPayer payer) log).getLast?).bind (fun height => log[height - 1]?)

/-- A record yields a ledger entry for `(account, topic)` exactly when it carries that name. -/
theorem incoming_isSome_iff (account : Nat) (topic : List UInt8) (height : Nat) (record : IntentRecord) :
    (NativeHost.fleetIncomingEntry? account topic height record).isSome = true ↔
      JournalIndex.Name.fleetIncoming account topic ∈ JournalIndex.names record := by
  unfold NativeHost.fleetIncomingEntry? JournalIndex.names
  cases decoded : FleetTurn.decodeIngress record.event.canonicalBytes with
  | none => simp
  | some ingress =>
      cases paid : ingress.command.transfer with
      | none => simp [JournalIndex.fleetNames, paid]
      | some transfer =>
          by_cases dest : transfer.destination = account
          · subst dest
            cases published : ingress.command.publication with
            | none =>
                by_cases empty : topic = []
                · subst empty
                  simp [JournalIndex.fleetNames, paid, published, NativeHost.fleetTopicMatches]
                · have empty' : ¬ [] = topic := fun h => empty h.symm
                  simp [JournalIndex.fleetNames, paid, published, NativeHost.fleetTopicMatches, empty, empty']
            | some publication =>
                by_cases empty : topic = []
                · subst empty
                  simp [JournalIndex.fleetNames, paid, published, NativeHost.fleetTopicMatches]
                · have empty' : ¬ [] = topic := fun h => empty h.symm
                  by_cases same : publication.topic = topic
                  · subst same
                    simp [JournalIndex.fleetNames, paid, published, NativeHost.fleetTopicMatches, empty]
                  · have same' : ¬ topic = publication.topic := fun h => same h.symm
                    by_cases blank : publication.topic = []
                    · simp [JournalIndex.fleetNames, paid, published, NativeHost.fleetTopicMatches, empty,
                        empty', same, same', blank]
                    · simp [JournalIndex.fleetNames, paid, published, NativeHost.fleetTopicMatches, empty,
                        empty', same, same', blank]
          · have dest' : ¬ account = transfer.destination := fun h => dest h.symm
            cases published : ingress.command.publication with
            | none => simp [JournalIndex.fleetNames, paid, published, dest, dest']
            | some publication =>
                by_cases blank : publication.topic = []
                · simp [JournalIndex.fleetNames, paid, published, dest, dest', blank]
                · simp [JournalIndex.fleetNames, paid, published, dest, dest', blank]

/-- A record is one of `payer`'s turns exactly when it carries the payer's name. -/
theorem paid_iff (payer : Nat) (record : IntentRecord) :
    (match FleetTurn.decodeIngress record.event.canonicalBytes with
      | some ingress => ingress.command.payer == payer
      | none => false) = true ↔
      JournalIndex.Name.fleetPayer payer ∈ JournalIndex.names record := by
  unfold JournalIndex.names
  cases decoded : FleetTurn.decodeIngress record.event.canonicalBytes with
  | none => simp
  | some ingress =>
      have tail : JournalIndex.Name.fleetPayer payer ∈ JournalIndex.fleetNames ingress.command ↔
          payer = ingress.command.payer := by
        unfold JournalIndex.fleetNames
        cases ingress.command.transfer with
        | none => simp
        | some transfer =>
            cases ingress.command.publication with
            | none => simp
            | some publication => by_cases blank : publication.topic.isEmpty <;> simp [blank]
      simp only [tail, beq_iff_eq]
      exact eq_comm

private theorem fleetIncomingFrom_eq_scan (account : Nat) (topic : List UInt8) (after : Nat) :
    ∀ (start : Nat) (log : List IntentRecord),
      NativeHost.fleetIncomingFrom account topic after start log =
        Theory.JournalSequences.scanFrom (NativeHost.fleetIncomingEntry? account topic) after start log
  | _, [] => rfl
  | start, record :: rest => by
      simp only [NativeHost.fleetIncomingFrom, Theory.JournalSequences.scanFrom,
        fleetIncomingFrom_eq_scan account topic after (start + 1) rest]

theorem incomingExact : IncomingExact := by
  intro genesis account topic cursor limit log clean
  rw [fleetIncomingFrom_eq_scan]
  exact Theory.JournalSequences.scanFrom_take_shift JournalIndex.sequences
    (JournalIndex.Name.fleetIncoming account topic).id (NativeHost.fleetIncomingEntry? account topic)
    genesis cursor limit log
    (fun record inLog height => (incoming_isSome_iff account topic height record).trans
      (JournalIndex.mem_sequences_iff clean inLog).symm)

theorem headExact : HeadExact := by
  intro payer log clean
  have same : paidBy payer log =
      log.filter (fun record => decide ((JournalIndex.Name.fleetPayer payer).id ∈ JournalIndex.sequences record)) := by
    unfold paidBy
    apply List.filter_congr
    intro record inLog
    have carried := (paid_iff payer record).trans (JournalIndex.mem_sequences_iff clean inLog).symm
    by_cases member : (JournalIndex.Name.fleetPayer payer).id ∈ JournalIndex.sequences record
    · simpa [member] using carried.mpr member
    · have off := mt carried.mp member
      simpa [member] using off
  rw [same]
  exact ⟨Theory.JournalSequences.filter_length_eq_count JournalIndex.sequences _ log,
    Theory.JournalSequences.filter_getLast? JournalIndex.sequences _ 1 log⟩

#assert_axioms incomingExact
#assert_axioms headExact

end Minidregg.Kernel.FleetJournalExact
