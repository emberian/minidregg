/-
# Kernel.PayObservation — a finalized external transfer, as an ingress value

The observer (an enrolled subject holding an `observePayment` capability on
the deployment's pay cell) reports the finalized transfers it saw to the
deposit addresses of the pay cell's `book`, together with the finalized chain
tip it read them at.  An empty report is a heartbeat: it only advances the
deployment clock cell's `slot` (`Kernel.ClockCell`; the pay cell keeps no
clock since the final merge).

This module holds the values and the pure decision; the signed receiver is
`PayObservationReceiver` and the named theorems are in `PayObservationProofs`.

* `Observation` is the watcher's record (lane P1, `observations.json`): book
  index, the 32-byte deposit address, the 64-byte transaction signature, slot,
  block time, the atomic amount added to the address, mint and token program,
  and (v2, PAY §11) what the transaction carried as a memo
  (`PayEnrolMemo.MemoField`: absent, the raw bytes of the one memo, or the
  watcher's `memoUnbound`/`memoInvalid`).  An ordinary deposit index ignores
  the memo; the enrollment index (`Tariff.enrolIndex`) is decided by
  `PayEnrolDecision`.
* `nullifier domain o` is PAY §10 erratum 1: its canonical bytes are
  `"soltx:" ‖ signature(64) ‖ address(32)`, so one transaction paying two
  deposit addresses is two credits, and a second credit for the same
  (signature, address) is refused by the durable preflight.
* `tickNullifier domain tip` spends the tip's slot, so no two accepted
  reports carry the same tip slot.
* `decideObservations` is the whole decision on the pay cell, the clock cell
  and the Book: tariff valid, the tip's slot not behind the clock's slot, a
  heartbeat not sooner than
  `minTickSlots`, no (signature, address) twice in one report, every
  observation matching the tariff's mint and program, its index's address and
  an assigned payer that is not the issuer well, a positive amount at or before
  the tip, and the batch of issuer mints admitted by `Batch.Admission`.
-/
import Kernel.PayCellDomain
import Kernel.ClockCell
import Theory.CanonicalResourceKernel
import Compiler.CredentialSignatureAdmission

namespace Minidregg.Kernel.PayObservation

open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent (StableNullifier)
open Minidregg.Kernel.PayCell
open Minidregg.Kernel.PayTariff
open Minidregg.Theory.CanonicalResourceKernel (Book Batch Operation AccountId)
open Minidregg.Theory.IndexedProgram (LawfulCodec)
open Minidregg.Theory.Store (Patch)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Values -/

/-- One finalized transfer to one deposit address (P1's record). -/
structure Observation where
  index : Nat
  address : Address32
  signature : List UInt8
  slot : Nat
  blockTime : Nat
  amount : Nat
  mint : Address32
  tokenProgram : Address32
  memo : PayEnrolMemo.MemoField
  deriving DecidableEq, Repr

structure Command where
  observer : SubjectId
  capability : CapabilityId
  nonce : Nat
  expectedAuthorityRoot : Digest
  /-- The pay cell's exact pre-root: the report writes the clock. -/
  expectedPayRoot : Digest
  /-- The finalized tip the observer read the transfers at. -/
  tip : ChainTip
  /-- `[]` is a heartbeat. -/
  observations : List Observation
  deriving DecidableEq, Repr

/-! ## Codecs `DREGG/PAY/OBSERVATION/v2` and `…/SIGNED/v2` -/

def observationStream : StreamCodec Observation :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product bytesStream
        (StreamCodec.product bytesStream
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product StreamCodec.nat
                (StreamCodec.product bytesStream
                  (StreamCodec.product bytesStream PayEnrolMemo.memoFieldStream))))))))
    (fun o => (o.index, o.address, o.signature, o.slot, o.blockTime, o.amount, o.mint,
      o.tokenProgram, o.memo))
    (fun (index, address, signature, slot, blockTime, amount, mint, program, memo) =>
      ⟨index, address, signature, slot, blockTime, amount, mint, program, memo⟩)
    (by intro o; cases o; rfl)

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product capabilityIdStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product digestStream
            (StreamCodec.product digestStream
              (StreamCodec.product chainTipStream (StreamCodec.list observationStream)))))))
    (fun c => (c.observer, c.capability, c.nonce, c.expectedAuthorityRoot, c.expectedPayRoot,
      c.tip, c.observations))
    (fun (observer, capability, nonce, authorityRoot, payRoot, tip, observations) =>
      ⟨observer, capability, nonce, authorityRoot, payRoot, tip, observations⟩)
    (by intro c; cases c; rfl)

def commandFrame : List UInt8 := "DREGG/PAY/OBSERVATION/v2".toUTF8.toList

def commandCodec : LawfulCodec Command := framed commandFrame commandStream

theorem command_roundtrip (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command :=
  commandCodec.decode_encode command

theorem command_canonical {bytes : List UInt8} {command : Command}
    (accepted : commandCodec.decode bytes = some command) : commandCodec.encode command = bytes :=
  framed_canonical commandFrame commandStream accepted

/-- The signed ingress: the command bytes and the observer's envelope. -/
structure Ingress where
  commandBytes : List UInt8
  envelope : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream bytesStream)
    (fun ingress => (ingress.commandBytes, ingress.envelope))
    (fun (command, envelope) => ⟨command, envelope⟩)
    (by intro ingress; cases ingress; rfl)

def ingressFrame : List UInt8 := "DREGG/PAY/OBSERVATION/SIGNED/v2".toUTF8.toList

def ingressCodec : LawfulCodec Ingress := framed ingressFrame ingressStream

theorem ingress_roundtrip (ingress : Ingress) :
    ingressCodec.decode (ingressCodec.encode ingress) = some ingress :=
  ingressCodec.decode_encode ingress

theorem ingress_canonical {bytes : List UInt8} {ingress : Ingress}
    (accepted : ingressCodec.decode bytes = some ingress) : ingressCodec.encode ingress = bytes :=
  framed_canonical ingressFrame ingressStream accepted

/-! ## Nullifiers -/

/-- `"soltx:"` as bytes, spelled out so the kernel decides facts about it. -/
def soltxPrefix : List UInt8 := [115, 111, 108, 116, 120, 58]

theorem soltxPrefix_utf8 : soltxPrefix = "soltx:".toUTF8.toList := by decide +kernel

/-- `"soltx:" ‖ signature ‖ address`: the transfer's identity (PAY §10). -/
def nullifierBytes (o : Observation) : List UInt8 := soltxPrefix ++ o.signature ++ o.address

def nullifier (domain : Digest) (o : Observation) : StableNullifier :=
  ⟨1, domain,
    (Sp800185Cshake256.hash "DREGG.PAY.SOLTX.NULLIFIER/v1".toUTF8.toList (nullifierBytes o)).digest,
    nullifierBytes o⟩

/-- `"paytick:"` as bytes. -/
def tickPrefix : List UInt8 := [112, 97, 121, 116, 105, 99, 107, 58]

theorem tickPrefix_utf8 : tickPrefix = "paytick:".toUTF8.toList := by decide +kernel

def tickBytes (tip : ChainTip) : List UInt8 := tickPrefix ++ StreamCodec.nat.encode tip.slot

def tickNullifier (domain : Digest) (tip : ChainTip) : StableNullifier :=
  ⟨1, domain,
    (Sp800185Cshake256.hash "DREGG.PAY.TICK.NULLIFIER/v1".toUTF8.toList (tickBytes tip)).digest,
    tickBytes tip⟩

/-- Every nullifier a report spends: one per observation, then its tick. -/
def nullifiers (domain : Digest) (command : Command) : List StableNullifier :=
  command.observations.map (nullifier domain) ++ [tickNullifier domain command.tip]

/-- The nullifier names the transfer: with 64-byte signatures, equal
nullifiers are the same (signature, address). -/
theorem nullifier_binds_transfer (domain : Digest) (left right : Observation)
    (leftShaped : left.signature.length = 64) (rightShaped : right.signature.length = 64)
    (same : nullifier domain left = nullifier domain right) :
    left.signature = right.signature ∧ left.address = right.address := by
  have bytes : nullifierBytes left = nullifierBytes right := congrArg StableNullifier.canonicalBytes same
  simp only [nullifierBytes, List.append_assoc, List.append_cancel_left_eq] at bytes
  have lengths : left.signature.length = right.signature.length := by rw [leftShaped, rightShaped]
  exact List.append_inj bytes lengths

/-! ## The pure decision -/

inductive Reject where
  | malformedIngress | directoryUnavailable | authorityUnavailable | bookUnavailable
  | payUnavailable | staleAuthority | stalePay
  | tariffInvalid | clockUnavailable | tipBehindClock | tickTooSoon | duplicateInBatch
  | malformedObservation | wrongMint | wrongTokenProgram | unknownIndex | addressMismatch
  | unassignedIndex | payerIsIssuer | zeroAmount | observationAfterTip
  | enrolIndexNeedsReceiver
  | bookAdmission | validation | physicalPreparation
  | policyUnavailable | capabilityRejected | policyRejected | policyInputRange | policyCastAlias
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving DecidableEq, Repr

/-- One observation's credit: the payer the index is assigned to and the
tariff's credit for the observed amount (the full amount stays in the
command bytes the journal keeps). -/
structure Credit where
  index : Nat
  payer : AccountId
  amount : Nat
  credit : Nat
  deriving DecidableEq, Repr

def decideObservation (store : PayStore) (tariff : Tariff) (tip : ChainTip) (o : Observation) :
    Except Reject Credit :=
  if o.signature.length = 64 ∧ o.address.length = 32 then
    if o.mint = tariff.mint then
      if o.tokenProgram = tariff.tokenProgram then
        match bookAt store o.index with
        | none => .error .unknownIndex
        | some address =>
            if address = o.address then
              match assignmentAt store o.index with
              | none => .error .unassignedIndex
              | some payer =>
                  if payer = tariff.asset then .error .payerIsIssuer
                  else if 0 < o.amount then
                    if o.slot ≤ tip.slot then .ok ⟨o.index, payer, o.amount, tariff.creditFor o.amount⟩
                    else .error .observationAfterTip
                  else .error .zeroAmount
            else .error .addressMismatch
      else .error .wrongTokenProgram
    else .error .wrongMint
  else .error .malformedObservation

def decideAll (store : PayStore) (tariff : Tariff) (tip : ChainTip) :
    List Observation → Except Reject (List Credit)
  | [] => .ok []
  | o :: rest =>
      match decideObservation store tariff tip o with
      | .error reason => .error reason
      | .ok credit =>
          match decideAll store tariff tip rest with
          | .error reason => .error reason
          | .ok credits => .ok (credit :: credits)

/-- A decided report: the tariff it was priced at, the deployment clock it
advances, the tip, and one credit per observation in order. -/
structure Plan where
  tariff : Tariff
  clock : ClockCell.Clock
  tip : ChainTip
  credits : List Credit
  deriving DecidableEq, Repr

/-- The clock after a report: the chain slot becomes the tip's, and `now`
moves to the tip's block time when that is later (it never goes back; the
wall-clock ticker owns `now` otherwise). -/
def advanceClock (clock : ClockCell.Clock) (tip : ChainTip) : ClockCell.Clock :=
  ⟨max clock.now tip.blockTime, tip.slot⟩

def Plan.nextClock (plan : Plan) : ClockCell.Clock := advanceClock plan.clock plan.tip

/-- The Book batch: one issuer mint per credit, from the tariff asset's well. -/
def Plan.batch (plan : Plan) : Batch :=
  ⟨[], plan.credits.map fun credit => .mint plan.tariff.asset credit.payer credit.credit⟩

/-- The clock-cell patch: one guarded write of the whole clock, from the exact
current value to `nextClock` (`ClockCell.tickPatch`). -/
def Plan.patch (plan : Plan) : Patch ClockCell.layout := ClockCell.tickPatch plan.clock plan.nextClock

/-- A report's clock write is monotone in both coordinates. -/
theorem Plan.nextClock_monotone (plan : Plan) (behind : plan.clock.slot ≤ plan.tip.slot) :
    plan.clock.now ≤ plan.nextClock.now ∧ plan.clock.slot ≤ plan.nextClock.slot :=
  ⟨Nat.le_max_left _ _, behind⟩

/-- The (signature, address) pairs of a report. -/
def transfers (observations : List Observation) : List (List UInt8 × Address32) :=
  observations.map fun o => (o.signature, o.address)

def decideObservations (store : PayStore) (clock : ClockCell.Clock) (book : Book) (tip : ChainTip)
    (observations : List Observation) : Except Reject Plan :=
  match tariffOf store with
  | none => .error .payUnavailable
  | some tariff =>
      if tariff.valid then
        if clock.slot ≤ tip.slot then
          if observations = [] ∧ tip.slot < clock.slot + tariff.minTickSlots then .error .tickTooSoon
          else if (transfers observations).Nodup then
            if observations.any (fun o => tariff.enrolIndex == some o.index) then
              .error .enrolIndexNeedsReceiver
            else
            match decideAll store tariff tip observations with
            | .error reason => .error reason
            | .ok credits =>
                if (Plan.batch ⟨tariff, clock, tip, credits⟩).Admission book then
                  .ok ⟨tariff, clock, tip, credits⟩
                else .error .bookAdmission
          else .error .duplicateInBatch
        else .error .tipBehindClock
      else .error .tariffInvalid

/-! ### What an accepted decision says -/

theorem decideObservation_ok {store : PayStore} {tariff : Tariff} {tip : ChainTip} {o : Observation}
    {credit : Credit} (accepted : decideObservation store tariff tip o = .ok credit) :
    o.signature.length = 64 ∧ o.address.length = 32 ∧ o.mint = tariff.mint ∧
      o.tokenProgram = tariff.tokenProgram ∧ bookAt store o.index = some o.address ∧
      assignmentAt store o.index = some credit.payer ∧ credit.payer ≠ tariff.asset ∧
      0 < o.amount ∧ o.slot ≤ tip.slot ∧
      credit = ⟨o.index, credit.payer, o.amount, tariff.creditFor o.amount⟩ := by
  unfold decideObservation at accepted
  by_cases shaped : o.signature.length = 64 ∧ o.address.length = 32
  swap
  · rw [if_neg shaped] at accepted; cases accepted
  rw [if_pos shaped] at accepted
  by_cases mint : o.mint = tariff.mint
  swap
  · rw [if_neg mint] at accepted; cases accepted
  rw [if_pos mint] at accepted
  by_cases program : o.tokenProgram = tariff.tokenProgram
  swap
  · rw [if_neg program] at accepted; cases accepted
  rw [if_pos program] at accepted
  cases book : bookAt store o.index with
  | none => simp only [book] at accepted; cases accepted
  | some address =>
    simp only [book] at accepted
    by_cases same : address = o.address
    swap
    · rw [if_neg same] at accepted; cases accepted
    rw [if_pos same] at accepted
    cases assigned : assignmentAt store o.index with
    | none => simp only [assigned] at accepted; cases accepted
    | some payer =>
      simp only [assigned] at accepted
      by_cases issuer : payer = tariff.asset
      · rw [if_pos issuer] at accepted; cases accepted
      rw [if_neg issuer] at accepted
      by_cases positive : 0 < o.amount
      swap
      · rw [if_neg positive] at accepted; cases accepted
      rw [if_pos positive] at accepted
      by_cases early : o.slot ≤ tip.slot
      swap
      · rw [if_neg early] at accepted; cases accepted
      rw [if_pos early] at accepted
      cases accepted
      exact ⟨shaped.1, shaped.2, mint, program, same ▸ rfl, rfl, issuer, positive, early, rfl⟩

theorem decideAll_forall₂ {store : PayStore} {tariff : Tariff} {tip : ChainTip} :
    ∀ {observations : List Observation} {credits : List Credit},
      decideAll store tariff tip observations = .ok credits →
      List.Forall₂ (fun o credit => decideObservation store tariff tip o = .ok credit)
        observations credits
  | [], credits, accepted => by
      simp only [decideAll, Except.ok.injEq] at accepted
      subst accepted
      exact .nil
  | o :: rest, credits, accepted => by
      simp only [decideAll] at accepted
      cases first : decideObservation store tariff tip o with
      | error reason => simp only [first] at accepted; cases accepted
      | ok credit =>
        cases later : decideAll store tariff tip rest with
        | error reason => simp only [first, later] at accepted; cases accepted
        | ok credits' =>
          simp only [first, later, Except.ok.injEq] at accepted
          subst accepted
          exact .cons first (decideAll_forall₂ later)

/-- Everything an accepted report decided, in one statement. -/
theorem decideObservations_ok {store : PayStore} {clock : ClockCell.Clock} {book : Book}
    {tip : ChainTip} {observations : List Observation} {plan : Plan}
    (accepted : decideObservations store clock book tip observations = .ok plan) :
    tariffOf store = some plan.tariff ∧ plan.clock = clock ∧ plan.tariff.valid ∧
      plan.clock.slot ≤ tip.slot ∧
      ¬ (observations = [] ∧ tip.slot < plan.clock.slot + plan.tariff.minTickSlots) ∧
      (transfers observations).Nodup ∧
      decideAll store plan.tariff tip observations = .ok plan.credits ∧
      plan.tip = tip ∧ plan.batch.Admission book := by
  unfold decideObservations at accepted
  cases tariffFound : tariffOf store with
  | none => simp only [tariffFound] at accepted; cases accepted
  | some tariff =>
      simp only [tariffFound] at accepted
      by_cases valid : tariff.valid
      swap
      · rw [if_neg valid] at accepted; cases accepted
      rw [if_pos valid] at accepted
      by_cases ordered : clock.slot ≤ tip.slot
      swap
      · rw [if_neg ordered] at accepted; cases accepted
      rw [if_pos ordered] at accepted
      by_cases soon : observations = [] ∧ tip.slot < clock.slot + tariff.minTickSlots
      · rw [if_pos soon] at accepted; cases accepted
      rw [if_neg soon] at accepted
      by_cases distinct : (transfers observations).Nodup
      swap
      · rw [if_neg distinct] at accepted; cases accepted
      rw [if_pos distinct] at accepted
      by_cases enrolled : observations.any (fun o => tariff.enrolIndex == some o.index) = true
      · rw [if_pos enrolled] at accepted; cases accepted
      rw [if_neg enrolled] at accepted
      cases decided : decideAll store tariff tip observations with
      | error reason => simp only [decided] at accepted; cases accepted
      | ok credits =>
        simp only [decided] at accepted
        by_cases admitted : (Plan.batch ⟨tariff, clock, tip, credits⟩).Admission book
        swap
        · rw [if_neg admitted] at accepted; cases accepted
        rw [if_pos admitted] at accepted
        cases accepted
        exact ⟨rfl, rfl, valid, ordered, soon, distinct, decided, rfl, admitted⟩

theorem decideObservations_tip {store : PayStore} {clock : ClockCell.Clock} {book : Book}
    {tip : ChainTip} {observations : List Observation} {plan : Plan}
    (accepted : decideObservations store clock book tip observations = .ok plan) : plan.tip = tip :=
  (decideObservations_ok accepted).2.2.2.2.2.2.2.1

theorem decideObservations_admitted {store : PayStore} {clock : ClockCell.Clock} {book : Book}
    {tip : ChainTip} {observations : List Observation} {plan : Plan}
    (accepted : decideObservations store clock book tip observations = .ok plan) :
    plan.batch.Admission book :=
  (decideObservations_ok accepted).2.2.2.2.2.2.2.2

/-- **The enrollment index is not an ordinary deposit index** (PAY §11.4):
an accepted observation report never contains a transfer to
`tariff.enrolIndex`; those are decided by `PayEnrolDecision` only. -/
theorem enrol_index_not_ordinary {store : PayStore} {clock : ClockCell.Clock} {book : Book}
    {tip : ChainTip} {observations : List Observation} {plan : Plan}
    (accepted : decideObservations store clock book tip observations = .ok plan) :
    ∀ o ∈ observations, plan.tariff.enrolIndex ≠ some o.index := by
  intro o member same
  have present := (decideObservations_ok accepted).1
  unfold decideObservations at accepted
  rw [present] at accepted
  simp only at accepted
  have hit : observations.any (fun o => plan.tariff.enrolIndex == some o.index) = true :=
    List.any_eq_true.mpr ⟨o, member, by simp [same]⟩
  by_cases valid : plan.tariff.valid
  swap
  · rw [if_neg valid] at accepted; cases accepted
  rw [if_pos valid] at accepted
  by_cases ordered : clock.slot ≤ tip.slot
  swap
  · rw [if_neg ordered] at accepted; cases accepted
  rw [if_pos ordered] at accepted
  by_cases soon : observations = [] ∧ tip.slot < clock.slot + plan.tariff.minTickSlots
  · rw [if_pos soon] at accepted; cases accepted
  rw [if_neg soon] at accepted
  by_cases distinct : (transfers observations).Nodup
  swap
  · rw [if_neg distinct] at accepted; cases accepted
  rw [if_pos distinct, if_pos hit] at accepted
  cases accepted

#assert_axioms command_roundtrip
#assert_axioms command_canonical
#assert_axioms ingress_roundtrip
#assert_axioms ingress_canonical
#assert_axioms nullifier_binds_transfer
#assert_axioms soltxPrefix_utf8
#assert_axioms tickPrefix_utf8
#assert_axioms decideObservation_ok
#assert_axioms decideAll_forall₂
#assert_axioms decideObservations_ok
#assert_axioms enrol_index_not_ordinary
#assert_axioms decideObservations_tip
#assert_axioms decideObservations_admitted

end Minidregg.Kernel.PayObservation
