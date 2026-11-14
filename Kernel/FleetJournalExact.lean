/-
# Kernel.FleetJournalExact -- the fleet reads off the journal index are the scans (statements)

Ops 101 and 180 were scans of the accepted log (`NativeHost.fleetIncomingFrom`; the head's
filter). They are now reads of journal sequence rows (`NativeHost.fleetHeadLight`,
`NativeHost.fleetIncomingLight`). These are the two exactness statements, over a log and the
recomputed sequence heights (`Theory.JournalSequences.heights`, which the kept rows equal:
`Theory.JournalSequences.index_from_replay`, `DurableIndex.IndexRows.indexed_changes_exact`).

Both are STATED here and owed as theorems. The route is proved in `Theory.JournalSequences`:
`scanFrom_take` (a bounded scan is the window's entries), `window_spec` (the window is the
bisection and the next positions), `filter_length_eq_count` and `filter_getLast?` (the count
and the newest member), with `JournalIndex.mem_sequences_iff` for the premise that a record
is in a name's sequence exactly when it carries the name. What remains is the bridge from
`fleetIncomingEntry?` and the head's filter to "carries the name", and the height shift by
`genesisHeight`.
-/
module

public import Kernel.NativeHost

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

end Minidregg.Kernel.FleetJournalExact
