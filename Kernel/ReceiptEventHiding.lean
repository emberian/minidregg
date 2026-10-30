/-
# Kernel.ReceiptEventHiding — a receipt cannot be linked to its hidden command (K-RECEIPT-HIDE)

docs/RATCHET-LOG-DESIGN.md §1 found that a receipt exposes an unblinded command
fingerprint, so hiding a cell's root alone cannot give receipt-inclusive privacy.
This module states the property receipts must meet, refutes the retired
construction against it, and reduces the current construction to one named
cryptographic obligation.

## What a receipt shows, traced in the code

* `NativeHostCodec.Receipt` is `(transactionId, eventId, acceptedCount, worldRoot)`.
  `NativeHost.receiptOfRecord` fills `eventId` from the accepted record's
  `event.eventId`; op 102 (`receiptByTransactionVia`) serves it to anyone who
  names a transaction id, and `since` (`NativeObservationController.SinceEntry`)
  hands every reader the transaction ids of the visible cells' writers.
* A declared invocation, the path that writes the blinded Hyperdocument and
  DeclaredEffect cells, records `DeclaredResourceController.invocationEvent`.
  Its id was `effectsDigest domain semantics command`: an
  unkeyed cSHAKE of the unsigned command bytes. A reader who can name two
  candidate commands (subject, nonce, targets, body) hashes both and compares:
  `legacy_receipt_links` below is that distinguisher, with gap 1.
* The id is now `eventIdOfSigned (signedBytes …)`: a digest of the exact signed
  ingress the record already retained, which carries the authority signature
  that `withAcceptedOn` authenticates before anything else. The transaction id
  (subject, nonce), the height and the world root are unchanged.

## The property and its leakage

The observer is a reader without custody: it holds receipts, `since` entries and
its authorized resource views, never the durable journal or a signed ingress it
did not author. Both worlds submit the SAME transaction identity (domain,
semantics, subject, nonce), so the receipt's transaction id is equal leakage; the
public schedule (height) and the world root are equal leakage by the legality
rule of the design's §2 (the world root is the design's separate wrapper
obligation, not discharged here). What remains of the receipt is the event id,
so the receipt hides its command exactly when, given the common view, the event
ids of the two worlds are indistinguishable to budgeted readers
(`ReceiptUnlinkable`; the view takes no world argument, which is the
same-leakage rule).

A meaningful budget admits at least the reader's own hashing of byte strings
it chooses, up to a query bound (`BudgetAdmitsPublicHash`: point and
support-membership tests; unbounded lists would enumerate a finite support), and a
meaningful gap is below one; every statement here that claims hiding carries
both premises.

## What is and is not proved

* Proved: the retired fingerprint is linkable (`legacy_receipt_links`), the
  hybrid reduction (`unlinkable_of_idealReplacement`), replay and idempotence
  unchanged (`DeclaredResourceController.invocationEvent_eq_iff`), and the
  ideal-model satisfiable and premise-inhabitation witnesses.
* Open, and named: `IdealReplacement` for `eventIdOfSigned`, the cryptographic
  obligation. Its intended discharge is cSHAKE as a random oracle plus
  unforgeability of the credential signature scheme: a reader that queries the
  hash on the retained bytes has produced a signature on that exact signed
  header, which the reduction never requests from the signing oracle. This
  needs, beyond the envelope's validity: the signer's key stays secret, the
  exact header is signed only for this ingress, and neither the signature nor
  the complete ingress reaches a non-party. The last is false for the fn archive
  (`Kernel.FnArchive` posts exact durable record bytes, which include every
  signed ingress and every blinded cell's plaintext): a deployment that
  archives to a public fn group gives no hiding at all, receipts or roots.
* Follow-up statement: the random-oracle model proper (oracle table on the
  tape, readers bounded by query count), which turns `budgeted` from an
  uninterpreted computational predicate into a counted one.

## History

Old records carry `effectsDigest` ids; exact-retry recognition and the
historical re-admission compare whole records, so an old history does not
re-admit under this code. This change moves a world by fresh genesis.
-/
module

public import Kernel.DeclaredResourceController
public import Theory.FiniteTapeGap

@[expose] public section

namespace Minidregg.Kernel.ReceiptEventHiding

set_option autoImplicit false

open Minidregg.Theory.FiniteTapeGap
open Minidregg.Compiler
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Theory.TypedAuthorization (Digest)

/-! ## The game -/

/-- A reader: a function of its other observations (`view`: `since` entries,
authorized resource views, fleet polls, the receipt's transaction id, height and
world root) and the receipt's event id. -/
abbrev Reader (View : Type) := View → Digest → Bool

/-- Receipt unlinkability for one transaction identity. `viewOf tape` is the
reader's other observations and takes NO world: the same-leakage rule of the
design's §2 is built into the type (both worlds release the same observations
on every tape). `eventIdOf b tape` is the event id world `b` publishes when the
honest signer's coins and keys come from `tape`. `budgeted` is computational
and is not interpreted extensionally; `BudgetAdmitsPublicHash` pins the
distinguishers it must contain. -/
def ReceiptUnlinkable {View : Type} (tapes num den : Nat) (viewOf : Fin tapes → View)
    (eventIdOf : Bool → Fin tapes → Digest) (budgeted : Reader View → Prop) : Prop :=
  ∀ reader, budgeted reader →
    GapAtMost tapes num den (fun tape => reader (viewOf tape) (eventIdOf false tape))
      (fun tape => reader (viewOf tape) (eventIdOf true tape))

/-- The reader's own hashing: test whether the event id is among the hashes of
byte strings it chooses from its view. Point tests (one query) and
support-membership tests (many) are both of this form. -/
def PublicHashTest {View : Type} (queryBound : Nat) (hash : List UInt8 → Digest)
    (reader : Reader View) : Prop :=
  ∃ queries : View → List (List UInt8), (∀ view, (queries view).length ≤ queryBound) ∧
    reader = fun view eventId => decide (eventId ∈ (queries view).map hash)

/-- A budget is meaningful only if it admits every public-hash test of up to
`queryBound` queries. The bound is essential: an unbounded query list can
enumerate a whole finite support, which no real reader can. -/
def BudgetAdmitsPublicHash {View : Type} (queryBound : Nat) (hash : List UInt8 → Digest)
    (budgeted : Reader View → Prop) : Prop :=
  ∀ reader, PublicHashTest queryBound hash reader → budgeted reader

/-- The cryptographic obligation, as a hybrid: each world's event ids are
indistinguishable, to budgeted readers holding the common view, from ONE
world-independent ideal (its type takes no world). -/
def IdealReplacement {View : Type} (tapes num den : Nat) (viewOf : Fin tapes → View)
    (eventIdOf : Bool → Fin tapes → Digest) (ideal : Fin tapes → Digest)
    (budgeted : Reader View → Prop) : Prop :=
  ∀ reader, budgeted reader → ∀ world,
    GapAtMost tapes num den (fun tape => reader (viewOf tape) (eventIdOf world tape))
      (fun tape => reader (viewOf tape) (ideal tape))

/-- **The hybrid reduction.** An ideal replacement at gap `e` per world gives
unlinkability at `2e`. -/
theorem unlinkable_of_idealReplacement {View : Type} {tapes num den : Nat}
    {viewOf : Fin tapes → View} {eventIdOf : Bool → Fin tapes → Digest}
    {ideal : Fin tapes → Digest} {budgeted : Reader View → Prop}
    (replace : IdealReplacement tapes num den viewOf eventIdOf ideal budgeted) :
    ReceiptUnlinkable tapes (num + num) den viewOf eventIdOf budgeted := fun reader admitted =>
  (replace reader admitted false).trans (replace reader admitted true).symm

#assert_axioms unlinkable_of_idealReplacement

/-- **A public fingerprint is linkable.** If the event id each world publishes is
a hash of bytes the reader can name, and the two hashes differ, the reader's
one-query public-hash test separates the worlds with certainty: no gap below one
holds, whatever the common view. -/
theorem fingerprint_links {View : Type} {tapes num den : Nat} (viewOf : Fin tapes → View)
    (hash : List UInt8 → Digest) (named : Bool → List UInt8)
    (distinct : hash (named false) ≠ hash (named true))
    {budgeted : Reader View → Prop} (meaningful : BudgetAdmitsPublicHash 1 hash budgeted)
    (small : num < den) :
    ¬ ReceiptUnlinkable tapes num den viewOf (fun world _ => hash (named world)) budgeted := by
  intro unlinkable
  have admitted := meaningful _ ⟨fun _ => [named false], fun _ => le_refl _, rfl⟩
  exact not_gapAtMost_of_separating small (by simp) (fun _ => by simpa using distinct.symm)
    (unlinkable _ admitted)

#assert_axioms fingerprint_links

/-! ## The declared invocation: the retired id and the current one -/

/-- The public hash a reader computes for the retired id: the effects tag over
bytes it names. -/
def effectsHash (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.RESOURCE.TRANSACTION.EFFECT/v4".toUTF8.toList bytes).digest

theorem effectsDigest_eq_effectsHash (domain semantics : Digest) (command : Command) :
    effectsDigest domain semantics command =
      effectsHash (commandBytes domain semantics command) := rfl

/-- **Teeth: the retired event id links a receipt to its command.** For any two
candidate commands whose effects digests differ, any common view, a meaningful
budget and any gap below one, the receipts carrying `effectsDigest` are linkable. -/
theorem legacy_receipt_links {View : Type} {tapes num den : Nat} (viewOf : Fin tapes → View)
    (domain semantics : Digest) (command : Bool → Command)
    (distinct : effectsDigest domain semantics (command false) ≠
      effectsDigest domain semantics (command true))
    {budgeted : Reader View → Prop} (meaningful : BudgetAdmitsPublicHash 1 effectsHash budgeted)
    (small : num < den) :
    ¬ ReceiptUnlinkable tapes num den viewOf
      (fun world _ => effectsDigest domain semantics (command world)) budgeted :=
  fingerprint_links viewOf effectsHash (fun world => commandBytes domain semantics (command world))
    distinct meaningful small

#assert_axioms legacy_receipt_links

/-- A legal receipt-linking challenge for declared invocations: one transaction
identity, two different commands, a common reader view, and an honest signer
whose authority envelope on tape `tape` is `sign tape` of the world's command
bytes (the model of the credential envelope `withAcceptedOn` authenticates first;
its secrecy is the crypto premise, not a field here). -/
structure Challenge (tapes : Nat) (View : Type) where
  domain : Digest
  semantics : Digest
  command : Bool → Command
  sign : Fin tapes → List UInt8 → List UInt8
  signedOf : Bool → Fin tapes → SignedCommand
  viewOf : Fin tapes → View
  sameTransaction : transactionId domain semantics (command false) =
    transactionId domain semantics (command true)
  hiddenDifference : command false ≠ command true
  signsCommand : ∀ world tape, (signedOf world tape).commandBytes = commandCodec.encode (command world)
  honestSigner : ∀ world tape,
    (signedOf world tape).authorityEnvelope = sign tape (commandCodec.encode (command world))
  /-- Native verification takes a 64-byte signature (`CredentialSignatureIO`). -/
  signatureWidth : ∀ tape message, (sign tape message).length = 64

/-- The event ids a challenge's receipts carry under the current code. -/
def Challenge.eventIdOf {tapes : Nat} {View : Type} (challenge : Challenge tapes View)
    (world : Bool) (tape : Fin tapes) : Digest :=
  (invocationEvent challenge.domain challenge.semantics (challenge.command world)
    (challenge.signedOf world tape)).eventId

/-- **Keystone statement (K-RECEIPT-HIDE).** For a legal challenge, a gap below
one, and a budget that admits the reader's own hashing (both the retired effects
hash and the current event hash), the receipts of the current code are
unlinkable at `num/den` given the common view. -/
def DeclaredReceiptHiding {View : Type} (tapes queryBound num den : Nat)
    (challenge : Challenge tapes View) (budgeted : Reader View → Prop) : Prop :=
  num < den ∧
  BudgetAdmitsPublicHash queryBound effectsHash budgeted ∧
  BudgetAdmitsPublicHash queryBound eventIdOfSigned budgeted ∧
  ReceiptUnlinkable tapes num den challenge.viewOf challenge.eventIdOf budgeted

/-- The keystone follows from the named cryptographic obligation. -/
theorem declaredReceiptHiding_of_idealReplacement {View : Type} {tapes queryBound num den : Nat}
    (challenge : Challenge tapes View) {budgeted : Reader View → Prop}
    (small : num + num < den)
    (effects : BudgetAdmitsPublicHash queryBound effectsHash budgeted)
    (current : BudgetAdmitsPublicHash queryBound eventIdOfSigned budgeted)
    {ideal : Fin tapes → Digest}
    (replace : IdealReplacement tapes num den challenge.viewOf challenge.eventIdOf ideal budgeted) :
    DeclaredReceiptHiding tapes queryBound (num + num) den challenge budgeted :=
  ⟨small, effects, current, unlinkable_of_idealReplacement replace⟩

#assert_axioms declaredReceiptHiding_of_idealReplacement

/-! ## Witnesses

**Satisfiable and premise-inhabitation (ideal model).** The one-time-pad model:
tapes are `Fin size`, world `b`'s event id on tape `t` is `t + offset b`, with
distinct offsets (a genuinely different hidden choice: on EVERY tape the two
worlds publish different ids), and an empty common view. Each world is the ideal
(the identity) relabelled by a permutation of the tapes, so `IdealReplacement`
holds at gap 0 for every reader whatsoever; the budget is everything, so it
admits every public-hash test for any hash. This shows the obligation is
consistent with a meaningful budget. It is an ideal privacy witness: it is NOT an
inhabited `DeclaredReceiptHiding` for the cSHAKE instance, which needs the
random-oracle model with the oracle on the tape and query-bounded readers (the
follow-up statement). -/

/-- The pad model's event ids. -/
def padEventId (size : Nat) [NeZero size] (offset : Bool → Fin size) (world : Bool) (tape : Fin size) : Digest :=
  ⟨(tape + offset world).val⟩

def padIdeal (size : Nat) (tape : Fin size) : Digest := ⟨tape.val⟩

theorem pad_idealReplacement (size : Nat) [NeZero size] (offset : Bool → Fin size) :
    IdealReplacement size 0 1 (fun _ => ()) (padEventId size offset) (padIdeal size)
      (fun _ => True) := by
  intro reader _ world
  have positive : 0 < size := Nat.pos_of_ne_zero (NeZero.ne size)
  exact GapAtMost.zero_of_perm positive Nat.one_pos (fun tape => reader () (padIdeal size tape))
    (Equiv.addRight (offset world))

/-- Satisfiable with a real hidden choice: every reader, gap zero, and the two
worlds' ids differ on every tape. -/
theorem pad_unlinkable_with_hidden_choice :
    ReceiptUnlinkable 2 0 1 (fun _ => ()) (padEventId 2 fun world => if world then 1 else 0)
      (fun _ => True) ∧
    (∀ queryBound, BudgetAdmitsPublicHash (View := Unit) queryBound effectsHash (fun _ => True)) ∧
    (∀ queryBound, BudgetAdmitsPublicHash (View := Unit) queryBound eventIdOfSigned (fun _ => True)) ∧
    ∀ tape, padEventId 2 (fun world => if world then 1 else 0) false tape ≠
      padEventId 2 (fun world => if world then 1 else 0) true tape := by
  refine ⟨unlinkable_of_idealReplacement (pad_idealReplacement 2 _), fun _ _ _ => trivial,
    fun _ _ _ => trivial, ?_⟩
  decide

#assert_axioms pad_unlinkable_with_hidden_choice

/-- Teeth inside the same model: publishing a public hash of the world's choice
is refuted by the one-query test, so `ReceiptUnlinkable` is not satisfied by
every construction. -/
theorem fingerprint_in_pad_model_links :
    ¬ ReceiptUnlinkable 2 0 1 (fun _ => ())
      (fun world (_ : Fin 2) => (fun bytes : List UInt8 => (⟨bytes.length⟩ : Digest))
        (if world then [0] else []))
      (fun _ => True) :=
  fingerprint_links (fun _ => ()) (fun bytes => ⟨bytes.length⟩)
    (fun world => if world then [0] else []) (by decide) (fun _ _ => trivial) Nat.one_pos

#assert_axioms fingerprint_in_pad_model_links

end Minidregg.Kernel.ReceiptEventHiding
