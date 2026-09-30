/-
Selection inside the actual freshly admitted native replay trace. This is a
semantic specification for a future selective-origin witness, not a witness
codec, a cryptographic proof, or a confidentiality claim. The selected step
still depends on its complete verified prior state.
-/
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.FnSelectedHistoricalStep

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.NativeHostReplay

set_option autoImplicit false

/-- A selected original ingress and receipt in a complete, native-admitted
history. The prior trace is retained as a proposition, not disclosed bytes. -/
structure Selected (config : Config) (origin tip : Opened config)
    (records : List DurableReceiver.IntentRecord) (receipts : List Receipt)
    (signedIngress : List UInt8) (originalReceipt : Receipt) where
  priorRecords : List DurableReceiver.IntentRecord
  record : DurableReceiver.IntentRecord
  laterRecords : List DurableReceiver.IntentRecord
  priorReceipts : List Receipt
  laterReceipts : List Receipt
  before : Opened config
  after : Opened config
  recordsExact : records = priorRecords ++ record :: laterRecords
  receiptsExact : receipts = priorReceipts ++ originalReceipt :: laterReceipts
  ingressExact : record.event.canonicalBytes = signedIngress
  priorAdmitted : AdmittedReplay config origin priorRecords before priorReceipts
  selectedAdmitted : AdmittedStep config before after record originalReceipt
  laterAdmitted : AdmittedReplay config after laterRecords tip laterReceipts

/-- The original receipt is the tip of the selected accepted-prefix receipts,
even when the complete verified history has later accepted records. -/
theorem Selected.receipt_prefix_tip {config : Config} {origin tip : Opened config}
    {records : List DurableReceiver.IntentRecord} {receipts : List Receipt}
    {signedIngress : List UInt8} {originalReceipt : Receipt}
    (selected : Selected config origin tip records receipts signedIngress originalReceipt) :
    (selected.priorReceipts ++ [originalReceipt]).getLast? = some originalReceipt := by
  simp

/-- The admitted prior trace followed by this step reaches the selected
receipt without using any later record. This is still a full prior-state
semantic trace, not a selectively disclosed byte witness. -/
theorem Selected.prefix_admitted {config : Config} {origin tip : Opened config}
    {records : List DurableReceiver.IntentRecord} {receipts : List Receipt}
    {signedIngress : List UInt8} {originalReceipt : Receipt}
    (selected : Selected config origin tip records receipts signedIngress originalReceipt) :
    AdmittedReplay config origin (selected.priorRecords ++ [selected.record])
      selected.after (selected.priorReceipts ++ [originalReceipt]) :=
  AdmittedReplay.append selected.priorAdmitted
    (.cons selected.selectedAdmitted (.nil selected.after))

/-- Expose the exact stored record comparison, native admission and receipt
calculation supplied by the real replay step. No carried Boolean is trusted. -/
theorem Selected.admitted_record {config : Config} {origin tip : Opened config}
    {records : List DurableReceiver.IntentRecord} {receipts : List Receipt}
    {signedIngress : List UInt8} {originalReceipt : Receipt}
    (selected : Selected config origin tip records receipts signedIngress originalReceipt) :
    ∃ derived : Derived config selected.before,
      recordMatches selected.record derived.intent = true ∧
      NativeAdmission config selected.before derived.intent ∧
      selected.record = DurableReceiver.IntentRecord.ofIntent derived.intent ∧
      ∃ next : Durable,
        advance selected.before derived = .ok next ∧
        validateLoaded config next = .ok selected.after ∧
        originalReceipt =
          ⟨derived.intent.transactionId, derived.intent.event.eventId,
            selected.before.durable.image.accepted.length + 1,
            imageBoundary config next.image⟩ := by
  obtain ⟨derived, matched, next, advanced, validated, receipt⟩ := selected.selectedAdmitted
  exact ⟨derived, matched, derived.admission,
    (recordMatches_iff selected.record derived.intent).mp matched,
    next, advanced, validated, receipt⟩

/-- The selected signed ingress is the event bytes of the actual
native-admitted intent, not a separately supplied caller string. -/
theorem Selected.signed_ingress_admitted {config : Config} {origin tip : Opened config}
    {records : List DurableReceiver.IntentRecord} {receipts : List Receipt}
    {signedIngress : List UInt8} {originalReceipt : Receipt}
    (selected : Selected config origin tip records receipts signedIngress originalReceipt) :
    ∃ derived : Derived config selected.before,
      NativeAdmission config selected.before derived.intent ∧
      derived.intent.event.canonicalBytes = signedIngress := by
  obtain ⟨derived, _, admission, recordEq, _, _, _, _⟩ := selected.admitted_record
  refine ⟨derived, admission, ?_⟩
  calc
    derived.intent.event.canonicalBytes = selected.record.event.canonicalBytes := by
      rw [recordEq]
      rfl
    _ = signedIngress := selected.ingressExact

/-- Every in-range position of an actually admitted replay has a
selected record/receipt at that position and an admitted prior/later split.
The output ingress is read from the selected canonical stored record. -/
theorem select_at {config : Config} {origin tip : Opened config}
    {records : List DurableReceiver.IntentRecord} {receipts : List Receipt}
    (trace : AdmittedReplay config origin records tip receipts)
    (index : Nat) (within : index < records.length) :
    ∃ (signedIngress : List UInt8) (originalReceipt : Receipt)
      (selected : Selected config origin tip records receipts signedIngress originalReceipt),
      selected.priorRecords.length = index := by
  induction trace generalizing index with
  | nil _ => simp at within
  | @cons before middle after record tailRecords receipt tailReceipts step tail ih =>
      cases index with
      | zero =>
          let selected : Selected config before after
              (record :: tailRecords) (receipt :: tailReceipts)
              record.event.canonicalBytes receipt :=
            ⟨[], record, tailRecords, [], tailReceipts, before, middle,
              by simp, by simp, rfl, .nil before, step, tail⟩
          exact ⟨record.event.canonicalBytes, receipt, selected, rfl⟩
      | succ n =>
          have smaller : n < tailRecords.length := by simpa using within
          obtain ⟨signedIngress, originalReceipt, selected, count⟩ := ih n smaller
          let lifted : Selected config before after
              (record :: tailRecords) (receipt :: tailReceipts)
              signedIngress originalReceipt :=
            ⟨record :: selected.priorRecords, selected.record, selected.laterRecords,
              receipt :: selected.priorReceipts, selected.laterReceipts,
              selected.before, selected.after,
              by simpa only [List.cons_append] using congrArg (record :: ·) selected.recordsExact,
              by simpa only [List.cons_append] using congrArg (receipt :: ·) selected.receiptsExact,
              selected.ingressExact,
              .cons step selected.priorAdmitted,
              selected.selectedAdmitted, selected.laterAdmitted⟩
          exact ⟨signedIngress, originalReceipt, lifted, by simpa [lifted] using count⟩

/-- A verified native image supplies the admitted history used by selection;
no package-supplied trace can construct `Verified` on its own. -/
theorem select_verified {config : Config} {target : Durable}
    (verified : Verified config target) (index : Nat)
    (within : index < target.image.accepted.length) :
    ∃ (signedIngress : List UInt8) (originalReceipt : Receipt)
      (selected : Selected config verified.origin verified.opened
        target.image.accepted verified.receipts signedIngress originalReceipt),
      selected.priorRecords.length = index :=
  select_at verified.accepted_history index within

/-- info: 'Minidregg.Kernel.FnSelectedHistoricalStep.Selected.admitted_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Selected.admitted_record
/-- info: 'Minidregg.Kernel.FnSelectedHistoricalStep.Selected.prefix_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Selected.prefix_admitted
/-- info: 'Minidregg.Kernel.FnSelectedHistoricalStep.Selected.signed_ingress_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Selected.signed_ingress_admitted
/-- info: 'Minidregg.Kernel.FnSelectedHistoricalStep.select_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms select_at
/-- info: 'Minidregg.Kernel.FnSelectedHistoricalStep.select_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms select_verified

end Minidregg.Kernel.FnSelectedHistoricalStep
