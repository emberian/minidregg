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
  unchanged (`DeclaredResourceController.invocationEvent_eq_iff`), teeth on the
  current code for ingress reconstructible from the view
  (`public_signature_refutes`), the generic ideal-model consistency witness
  (`pad_unlinkable_with_hidden_choice`), and wire-shape inhabitation of the
  challenge at the native envelope shape (`DeployedShape.wire_shape_inhabited`:
  shape only, by `rfl`, budget everything; not premise inhabitation and not an
  admitted invocation). Owed: a joint witness including `IdealReplacement` at the
  deployed shape, and an unconditional `public_signer_refuted` (its `distinct`
  discharged).
* Scope: unlinkability against the admitted reader class (see the keystone),
  not yet computational hiding.
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
meta import Kernel.DeclaredResourceController
meta import Theory.TypedAuthorization

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
a hash of bytes the reader can reconstruct from its view, and on every view the
two worlds' hashes differ, the reader's one-query public-hash test separates the
worlds with certainty: no gap below one holds. -/
theorem fingerprint_links {View : Type} {tapes num den : Nat} (viewOf : Fin tapes → View)
    (hash : List UInt8 → Digest) (named : Bool → View → List UInt8)
    (distinct : ∀ view, hash (named false view) ≠ hash (named true view))
    {budgeted : Reader View → Prop} (meaningful : BudgetAdmitsPublicHash 1 hash budgeted)
    (small : num < den) :
    ¬ ReceiptUnlinkable tapes num den viewOf (fun world tape => hash (named world (viewOf tape)))
      budgeted := by
  intro unlinkable
  have admitted := meaningful _ ⟨fun view => [named false view], fun _ => le_refl _, rfl⟩
  exact not_gapAtMost_of_separating small (by simp)
    (fun tape => by simpa using (distinct (viewOf tape)).symm) (unlinkable _ admitted)

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
  fingerprint_links viewOf effectsHash (fun world _ => commandBytes domain semantics (command world))
    (fun _ => distinct) meaningful small

#assert_axioms legacy_receipt_links

/-- A syntactic receipt-linking challenge for declared invocations: one
transaction identity, two different commands, a common reader view, and an
envelope producer whose authority envelope on tape `tape` is the canonical
encoding of the envelope `sign tape` makes for the world's command bytes: a
signed header and a 64-byte signature, the wire shape
`CredentialSignatureAdmission.verifyNative` decodes (`Challenge.envelope_decodes`)
and whose signature it checks. It is not an admitted invocation: the header's
version, footprint and message binding, the target envelopes and the registry
are admission's checks, not fields here, and the producer's secrecy is the crypto
premise. -/
structure Challenge (tapes : Nat) (View : Type) where
  domain : Digest
  semantics : Digest
  command : Bool → Command
  sign : Fin tapes → List UInt8 → CredentialSignedEnvelopeController.SignedEnvelope
  signedOf : Bool → Fin tapes → SignedCommand
  viewOf : Fin tapes → View
  sameTransaction : transactionId domain semantics (command false) =
    transactionId domain semantics (command true)
  hiddenDifference : command false ≠ command true
  signsCommand : ∀ world tape, (signedOf world tape).commandBytes = commandCodec.encode (command world)
  honestSigner : ∀ world tape,
    (signedOf world tape).authorityEnvelope =
      CredentialSignedEnvelopeController.envelopeCodec.encode (sign tape (commandCodec.encode (command world)))
  /-- Native verification checks the decoded envelope's 64-byte signature
  (`CredentialSignatureIO`); the header beside it has no fixed width. -/
  signatureWidth : ∀ tape message, (sign tape message).signature.length = 64

/-- The native verifier's decode of a challenge's authority envelope is the
signer's envelope (`CredentialSignedEnvelopeController.prepare` begins with this
decode), with its 64-byte signature. -/
theorem Challenge.envelope_decodes {tapes : Nat} {View : Type} (challenge : Challenge tapes View)
    (world : Bool) (tape : Fin tapes) :
    CredentialSignedEnvelopeController.envelopeCodec.decode (challenge.signedOf world tape).authorityEnvelope =
        some (challenge.sign tape (commandCodec.encode (challenge.command world))) ∧
      (challenge.sign tape (commandCodec.encode (challenge.command world))).signature.length = 64 := by
  rw [challenge.honestSigner]
  exact ⟨CredentialSignedEnvelopeController.envelopeCodec.decode_encode _, challenge.signatureWidth _ _⟩

#assert_axioms Challenge.envelope_decodes

/-- The event ids a challenge's receipts carry under the current code. -/
def Challenge.eventIdOf {tapes : Nat} {View : Type} (challenge : Challenge tapes View)
    (world : Bool) (tape : Fin tapes) : Digest :=
  (invocationEvent challenge.domain challenge.semantics (challenge.command world)
    (challenge.signedOf world tape)).eventId

/-- **Keystone statement (K-RECEIPT-HIDE).** For a legal challenge, a gap below
one, a positive query bound (at bound 0 only the constant reader is a hash test,
so the budget premises would admit a budget of that reader alone), and a budget
that admits the reader's own hashing (both the retired effects hash and the
current event hash), the receipts of the current code are unlinkable at
`num/den`, given the common view, against the readers `budgeted` admits.

Scope: this is security against the admitted reader class. The budget premises
force only the public-hash tests into that class; a `budgeted` admitting nothing
else (for instance at bound 1, with four distinct publicly enumerable ingress
hashes over two tapes, where every admitted test has gap at most one half) can
meet the statement although a two-entry lookup table, not a hash test,
identifies the world. Computational hiding needs the counted reader model (the
follow-up statement: the random oracle on the tape, readers bounded by query
count) and a deployment-derived view. `public_signature_refutes` is the teeth on
the current code: ingress the reader can reconstruct from its view makes the
statement false at every admitted bound. -/
def DeclaredReceiptHiding {View : Type} (tapes queryBound num den : Nat)
    (challenge : Challenge tapes View) (budgeted : Reader View → Prop) : Prop :=
  num < den ∧ 0 < queryBound ∧
  BudgetAdmitsPublicHash queryBound effectsHash budgeted ∧
  BudgetAdmitsPublicHash queryBound eventIdOfSigned budgeted ∧
  ReceiptUnlinkable tapes num den challenge.viewOf challenge.eventIdOf budgeted

/-- The keystone follows from the named cryptographic obligation. -/
theorem declaredReceiptHiding_of_idealReplacement {View : Type} {tapes queryBound num den : Nat}
    (challenge : Challenge tapes View) {budgeted : Reader View → Prop}
    (small : num + num < den) (queries : 0 < queryBound)
    (effects : BudgetAdmitsPublicHash queryBound effectsHash budgeted)
    (current : BudgetAdmitsPublicHash queryBound eventIdOfSigned budgeted)
    {ideal : Fin tapes → Digest}
    (replace : IdealReplacement tapes num den challenge.viewOf challenge.eventIdOf ideal budgeted) :
    DeclaredReceiptHiding tapes queryBound (num + num) den challenge budgeted :=
  ⟨small, queries, effects, current, unlinkable_of_idealReplacement replace⟩

#assert_axioms declaredReceiptHiding_of_idealReplacement

/-- A budget admitting the hash tests of some positive bound admits the one-query
tests. -/
theorem BudgetAdmitsPublicHash.one {View : Type} {queryBound : Nat} {hash : List UInt8 → Digest}
    {budgeted : Reader View → Prop} (admits : BudgetAdmitsPublicHash queryBound hash budgeted)
    (positive : 0 < queryBound) : BudgetAdmitsPublicHash 1 hash budgeted := by
  rintro reader ⟨queries, short, rfl⟩
  exact admits _ ⟨queries, fun view => (short view).trans positive, rfl⟩

/-- **Teeth on the current code.** If the signer's ingress can be reconstructed
from the reader's view (`signed world view`: a constant public signature, or a
signature the view leaks) and on every view the two worlds' event ids differ,
`DeclaredReceiptHiding` fails at every query bound and every gap: the reader
hashes the left world's reconstructed ingress. -/
theorem public_signature_refutes {View : Type} {tapes queryBound num den : Nat}
    (challenge : Challenge tapes View) (signed : Bool → View → SignedCommand)
    (computable : ∀ world tape, challenge.signedOf world tape = signed world (challenge.viewOf tape))
    (distinct : ∀ view,
      eventIdOfSigned (signedBytes challenge.domain challenge.semantics (signed false view)) ≠
        eventIdOfSigned (signedBytes challenge.domain challenge.semantics (signed true view)))
    (budgeted : Reader View → Prop) :
    ¬ DeclaredReceiptHiding tapes queryBound num den challenge budgeted := by
  rintro ⟨small, positive, _, current, unlinkable⟩
  have computed : challenge.eventIdOf = fun world tape =>
      eventIdOfSigned (signedBytes challenge.domain challenge.semantics
        (signed world (challenge.viewOf tape))) := by
    funext world tape
    simp [Challenge.eventIdOf, computable]
  rw [computed] at unlinkable
  exact fingerprint_links challenge.viewOf eventIdOfSigned
    (fun world view => signedBytes challenge.domain challenge.semantics (signed world view))
    distinct (current.one positive) small unlinkable

#assert_axioms public_signature_refutes

/-! ## Witnesses

**Satisfiable and premise-inhabitation (ideal model).** The one-time-pad model:
tapes are `Fin size`, world `b`'s event id on tape `t` is `t + offset b`, with
distinct offsets (a genuinely different hidden choice: on EVERY tape the two
worlds publish different ids), and an empty common view. Each world is the ideal
(the identity) relabelled by a permutation of the tapes, so `IdealReplacement`
holds at gap 0 for every reader whatsoever; the budget is everything, so it
admits every public-hash test for any hash. This shows the obligation is
consistent with a meaningful budget. It is a generic ideal-model consistency
witness: it supplies no `Challenge`.

**Wire shape and the public signer** (`DeployedShape`): a `Challenge` at the
native envelope shape (a canonically encoded header and 64-byte signature, one
nonempty target list, two commands with one transaction identity differing in
their signed family context). Its signer is a constant public signature, so the
keystone is refuted for it at every bound (`public_signer_refuted_always`).

**The keystone inhabited at the deployed shape** (`DeployedRandomized`): the same
commands with the signer's randomness on four tapes and a constant view, against
exactly the query-bounded public-hash tests, `IdealReplacement` included
(`deployed_receiptHiding`, gap `1/2`, inhabitation at `q < T` only: a
four-query reader separates the worlds); a view leaking the tape refutes it
(`leaked_tape_refuted`). The cSHAKE instance against the counted random-oracle
reader model stays the follow-up statement. -/

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
    (fun world _ => if world then [0] else []) (fun _ => by decide) (fun _ _ => trivial) Nat.one_pos

#assert_axioms fingerprint_in_pad_model_links

/-! ## Compiled evaluation of event ids

The kernel cannot evaluate Keccak, so a distinctness fact about two concrete ids
is a compiled-evaluation fact (`native_decide`, pinned below). It is taken over
the pure-Lean fast path `Fast.cshake256Fast`, which equals the specification for
every input by a kernel proof (`cshake256Bytes_eq_fast`), so the evaluated code
is Lean's and not the native seam's (as `Theory.Sp800185Cshake256Conformance`). -/

/-- The event id over the fast path. -/
def fastEventId (bytes : List UInt8) : Digest :=
  Sp800185Cshake256.digestOfBytesLE
    (Sp800185Cshake256.Fast.cshake256Fast "DREGG.RESOURCE.TRANSACTION.EVENT/v5".toUTF8.toList bytes)

theorem eventIdOfSigned_eq_fast (bytes : List UInt8) : eventIdOfSigned bytes = fastEventId bytes := by
  simp only [eventIdOfSigned, fastEventId, Sp800185Cshake256.hash, Sp800185Cshake256.Output.digest,
    Sp800185Cshake256.Fast.cshake256Bytes_eq_fast]

#assert_axioms eventIdOfSigned_eq_fast

namespace DeployedShape

open Minidregg.Kernel.CredentialSignedEnvelopeController (SignedHeader SignedEnvelope envelopeCodec)

def target : Target :=
  { kind := .object, target := 0, capability := ⟨0⟩, schemaVersion := 0,
    expectedTargetRoot := ⟨0⟩, payload := .scalar [] }

/-- Two commands of one subject and nonce, differing in their signed family context. -/
def command (world : Bool) : Command :=
  { subject := ⟨1⟩, nonce := 0, targets := [target],
    family := some ⟨.ordinary, [if world then 1 else 0]⟩ }

def header (message : List UInt8) : SignedHeader :=
  { codecVersion := CredentialSignedEnvelopeController.envelopeCodecVersion, footprint := [], validUntil := 0, keyId := 0, keyEpoch := 0,
    algorithm := 0, domain := [], message := message, nullifier := 0 }

/-- A signer at the native envelope shape (its signature is a constant). -/
def sign (_ : Fin 1) (message : List UInt8) : SignedEnvelope := ⟨header message, List.replicate 64 0⟩

/-- One target envelope for the one target, as `admitAuthority` counts them. -/
def signedOf (world : Bool) (tape : Fin 1) : SignedCommand :=
  ⟨commandCodec.encode (command world),
    [envelopeCodec.encode (sign tape (commandCodec.encode (command world)))], [],
    envelopeCodec.encode (sign tape (commandCodec.encode (command world)))⟩

theorem sameTransaction : transactionId ⟨0⟩ ⟨0⟩ (command false) = transactionId ⟨0⟩ ⟨0⟩ (command true) := by
  simp only [transactionId, operationMarker, command]

theorem hiddenDifference : command false ≠ command true := by
  intro same
  have := congrArg Command.family same
  simp [command] at this

def challenge : Challenge 1 Unit where
  domain := ⟨0⟩
  semantics := ⟨0⟩
  command := command
  sign := sign
  signedOf := signedOf
  viewOf := fun _ => ()
  sameTransaction := sameTransaction
  hiddenDifference := hiddenDifference
  signsCommand := fun _ _ => rfl
  honestSigner := fun _ _ => rfl
  signatureWidth := fun _ _ => rfl

/-- **Wire-shape inhabitation only**, NOT premise inhabitation: every field is
by `rfl` and the budget admits every reader, and on this one-tape deterministic
instance `IdealReplacement` is refuted (`public_signer_refuted_always`). The
joint witness that includes `IdealReplacement` at the deployed shape is
`DeployedRandomized.deployed_receiptHiding`. What it shows: the challenge above (nonempty targets, one target envelope per target,
the current envelope codec version, its envelope decoding to a 64-byte
signature), a gap below one, query bound 1, and a budget admitting every reader
(so both public-hash classes). Shape only: no registry, ground or signature
verdict is constructed, so this is not an admitted invocation. -/
theorem wire_shape_inhabited :
    (∀ world tape, (challenge.command world).targets ≠ [] ∧
      (challenge.signedOf world tape).targetEnvelopes.length = (challenge.command world).targets.length ∧
      (challenge.sign tape (commandCodec.encode (challenge.command world))).header.codecVersion =
        CredentialSignedEnvelopeController.envelopeCodecVersion ∧
      envelopeCodec.decode (challenge.signedOf world tape).authorityEnvelope =
        some (challenge.sign tape (commandCodec.encode (challenge.command world))) ∧
      (challenge.sign tape (commandCodec.encode (challenge.command world))).signature.length = 64) ∧
    0 + 0 < 1 ∧ 0 < 1 ∧
    BudgetAdmitsPublicHash (View := Unit) 1 effectsHash (fun _ => True) ∧
    BudgetAdmitsPublicHash (View := Unit) 1 eventIdOfSigned (fun _ => True) :=
  ⟨fun world tape => ⟨by simp [challenge, command], rfl, rfl, challenge.envelope_decodes world tape⟩,
    Nat.one_pos, Nat.one_pos, fun _ _ => trivial, fun _ _ => trivial⟩

#assert_axioms wire_shape_inhabited

/-- Public-signer refutation, given that the two worlds' event ids differ
(discharged by `ids_differ`). -/
theorem public_signer_refuted {queryBound num den : Nat} (budgeted : Reader Unit → Prop)
    (distinct : eventIdOfSigned (signedBytes ⟨0⟩ ⟨0⟩ (signedOf false 0)) ≠
      eventIdOfSigned (signedBytes ⟨0⟩ ⟨0⟩ (signedOf true 0))) :
    ¬ DeclaredReceiptHiding 1 queryBound num den challenge budgeted :=
  public_signature_refutes challenge (fun world _ => signedOf world 0)
    (fun world tape => by rw [Subsingleton.elim tape 0]; rfl) (fun _ => distinct) budgeted

#assert_axioms public_signer_refuted

/-- The two worlds' signed ingresses hash apart: a compiled-evaluation fact
(the kernel cannot evaluate Keccak; `Theory.Sp800185Cshake256Conformance`). -/
theorem ids_differ :
    eventIdOfSigned (signedBytes ⟨0⟩ ⟨0⟩ (signedOf false 0)) ≠
      eventIdOfSigned (signedBytes ⟨0⟩ ⟨0⟩ (signedOf true 0)) := by
  rw [eventIdOfSigned_eq_fast, eventIdOfSigned_eq_fast]
  native_decide

/-- **The public signer is refuted**, at every query bound and gap. -/
theorem public_signer_refuted_always {queryBound num den : Nat} (budgeted : Reader Unit → Prop) :
    ¬ DeclaredReceiptHiding 1 queryBound num den challenge budgeted :=
  public_signer_refuted budgeted ids_differ

/-- info: 'Minidregg.Kernel.ReceiptEventHiding.DeployedShape.public_signer_refuted_always' depends on axioms: [propext, Classical.choice, Quot.sound, ids_differ._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms public_signer_refuted_always

end DeployedShape

/-! ## A joint witness at the deployed shape, `IdealReplacement` included

The keystone inhabited for a challenge at the native envelope shape whose
signer's randomness is the tape: four tapes, the signature on tape `t` a 64-byte
string carrying `t`, the reader's view constant (the custody premise: no reader
holds the signature), and the budget EXACTLY the query-bounded public-hash tests,
for every hash function at once (so both `effectsHash` and `eventIdOfSigned`).
`IdealReplacement` holds at `q/T` against that budget whenever each world's
event id is injective in the tape (`idealReplacement_of_injective`): a reader's
`q` queries hit at most `q` of the `T` tapes in either world. Injectivity of
each world's four ids is a compiled-evaluation fact (`randomized_ids_injective`).
The tape here carries two bits, so the gap is `1/4` per world and the keystone
holds at `1/2`. This is no extrapolation to a real signer: signature width is
not entropy, and the event digest's 256 bits bound how many tapes can have
distinct ids. Scope: the budget is the public-hash class only (the keystone's
stated scope), not the counted random-oracle reader model. -/

/-- A query-bounded public-hash test, for some hash function. -/
def AnyPublicHash {View : Type} (queryBound : Nat) (reader : Reader View) : Prop :=
  ∃ hash : List UInt8 → Digest, PublicHashTest queryBound hash reader

/-- An injective tape-to-id map is hit by at most as many tapes as there are hashes. -/
theorem count_mem_le {tapes : Nat} (ids : Fin tapes → Digest) (injective : Function.Injective ids)
    (hashes : List Digest) :
    (List.ofFn fun tape => decide (ids tape ∈ hashes)).count true ≤ hashes.length := by
  rw [List.ofFn_eq_map, List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
  refine le_trans (le_of_eq (List.length_map ids).symm)
    ((((List.nodup_finRange tapes).filter _).map injective).subperm ?_).length_le
  intro x member
  obtain ⟨tape, kept, rfl⟩ := List.mem_map.mp member
  simpa using (List.mem_filter.mp kept).2

/-- **Ideal replacement against public-hash tests.** With a constant view and an
event id injective in the tape in each world, every `q`-query public-hash test
is within `q/T` of the first world's ids. -/
theorem idealReplacement_of_injective {tapes queryBound : Nat} (positive : 0 < tapes)
    (eventIdOf : Bool → Fin tapes → Digest) (injective : ∀ world, Function.Injective (eventIdOf world)) :
    IdealReplacement tapes queryBound tapes (fun _ => ()) eventIdOf (eventIdOf false)
      (AnyPublicHash queryBound) := by
  rintro reader ⟨hash, queries, short, rfl⟩ world
  dsimp only
  have bound : ∀ w, (List.ofFn fun tape => decide (eventIdOf w tape ∈ (queries ()).map hash)).count true ≤
      queryBound := fun w => (count_mem_le (eventIdOf w) (injective w) ((queries ()).map hash)).trans
    (by rw [List.length_map]; exact short ())
  have mine := bound world
  have ideal := bound false
  refine ⟨positive, positive, ?_, ?_⟩
  · have := Nat.mul_le_mul_right tapes mine
    omega
  · have := Nat.mul_le_mul_right tapes ideal
    omega

#assert_axioms count_mem_le
#assert_axioms idealReplacement_of_injective

namespace DeployedRandomized

open Minidregg.Kernel.CredentialSignedEnvelopeController (SignedEnvelope envelopeCodec)

/-- The signer on tape `t`: the deployed header, a 64-byte signature carrying `t`. -/
def sign (tape : Fin 4) (message : List UInt8) : SignedEnvelope :=
  ⟨DeployedShape.header message, List.replicate 63 0 ++ [tape.val.toUInt8]⟩

def signedOf (world : Bool) (tape : Fin 4) : SignedCommand :=
  ⟨commandCodec.encode (DeployedShape.command world),
    [envelopeCodec.encode (sign tape (commandCodec.encode (DeployedShape.command world)))], [],
    envelopeCodec.encode (sign tape (commandCodec.encode (DeployedShape.command world)))⟩

def challenge : Challenge 4 Unit where
  domain := ⟨0⟩
  semantics := ⟨0⟩
  command := DeployedShape.command
  sign := sign
  signedOf := signedOf
  viewOf := fun _ => ()
  sameTransaction := DeployedShape.sameTransaction
  hiddenDifference := DeployedShape.hiddenDifference
  signsCommand := fun _ _ => rfl
  honestSigner := fun _ _ => rfl
  signatureWidth := fun _ _ => rfl

/-- Each world's four event ids are distinct (compiled evaluation). -/
theorem randomized_ids_injective : ∀ world, Function.Injective (challenge.eventIdOf world) := by
  have decided : ∀ world : Bool, ∀ a b : Fin 4,
      fastEventId (signedBytes ⟨0⟩ ⟨0⟩ (signedOf world a)) =
        fastEventId (signedBytes ⟨0⟩ ⟨0⟩ (signedOf world b)) → a = b := by
    native_decide
  intro world a b same
  simp only [Challenge.eventIdOf, invocationEvent_eventId, eventIdOfSigned_eq_fast] at same
  exact decided world a b same

/-- **The keystone, inhabited at the deployed shape**: gap `1/2`, one query,
the budget exactly the public-hash tests. Inhabitation at `q < T` only: with four
tapes, a four-query reader hashes every candidate ingress of one world and
separates the worlds, so this says nothing about readers with `q ≥ T`. -/
theorem deployed_receiptHiding :
    DeclaredReceiptHiding 4 1 (1 + 1) 4 challenge (AnyPublicHash 1) :=
  declaredReceiptHiding_of_idealReplacement challenge (by decide) Nat.one_pos
    (fun _ test => ⟨_, test⟩) (fun _ test => ⟨_, test⟩)
    (idealReplacement_of_injective (by decide) challenge.eventIdOf randomized_ids_injective)

/-- The same challenge with the tape in the reader's view (a leaked signature). -/
def leaky : Challenge 4 (Fin 4) where
  domain := ⟨0⟩
  semantics := ⟨0⟩
  command := DeployedShape.command
  sign := sign
  signedOf := signedOf
  viewOf := id
  sameTransaction := DeployedShape.sameTransaction
  hiddenDifference := DeployedShape.hiddenDifference
  signsCommand := fun _ _ => rfl
  honestSigner := fun _ _ => rfl
  signatureWidth := fun _ _ => rfl

/-- On every tape the two worlds' ingresses hash apart (compiled evaluation). -/
theorem leaked_distinct : ∀ tape : Fin 4,
    eventIdOfSigned (signedBytes ⟨0⟩ ⟨0⟩ (signedOf false tape)) ≠
      eventIdOfSigned (signedBytes ⟨0⟩ ⟨0⟩ (signedOf true tape)) := by
  simp only [eventIdOfSigned_eq_fast]
  native_decide

/-- Teeth in the same setting: a view that leaks the tape lets the reader
reconstruct the ingress, and the keystone fails at every bound and gap. -/
theorem leaked_tape_refuted {queryBound num den : Nat} (budgeted : Reader (Fin 4) → Prop) :
    ¬ DeclaredReceiptHiding 4 queryBound num den leaky budgeted :=
  public_signature_refutes leaky signedOf (fun _ _ => rfl) leaked_distinct budgeted

/-- info: 'Minidregg.Kernel.ReceiptEventHiding.DeployedRandomized.deployed_receiptHiding' depends on axioms: [propext, Classical.choice, Quot.sound, randomized_ids_injective._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms deployed_receiptHiding
/-- info: 'Minidregg.Kernel.ReceiptEventHiding.DeployedRandomized.leaked_tape_refuted' depends on axioms: [propext, Classical.choice, Quot.sound, leaked_distinct._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms leaked_tape_refuted

end DeployedRandomized


end Minidregg.Kernel.ReceiptEventHiding
