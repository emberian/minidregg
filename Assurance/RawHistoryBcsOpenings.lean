/-
# Assurance.RawHistoryBcsOpenings -- the retained-history carrier before binding

`SemanticHistoryPcsEventRealization` names the object this module builds and
says exactly why the existing one cannot be wrapped into it:
`HistoryBcsOpenings` verifies its columns against a `BindingCommitment`, so
`bcsWord_eq_historyLink` erases every unequal opening attempt before a
collision reduction can read it.  `no_retained_opening_mismatch` proves that
erasure is total: inside that carrier a mismatch is not unused, it is
*unrepresentable*.

This module supplies the carrier over an arbitrary executable
`OpeningScheme` -- the deployed Merkle checker has no binding field -- and
separates the two things the old structure fused:

* a **transcript**, which is roots plus columns the verifier actually
  accepted, and nothing else; and
* a **root attribution**, which claims each submitted root is the executable
  commitment of the head's retained link word.

That separation is what makes the honest three-way split statable, in exactly
the shape the resume order asks for:

1. no attribution -- the adversary's root is not the commitment of the word it
   is being read as.  Which ledger event that should be charged to (transport,
   not PCS) is NAMED here and proved nowhere; this module only makes the case
   representable instead of impossible;
2. attribution with an unequal accepted column -- a *retained* equivocation at
   a named round and query coordinate, which is the `BindingFailure` shape the
   landed Merkle reduction turns into an exact framed collision; and
3. attribution with every column pinned -- erasure recovery alone returns the
   head's retained link word, leaving the intrinsic MCA/PCS extraction event
   as the only residual.

No probability, collision resistance, ROM transport, or native semantics is
claimed here.  The one thing proved is that the evidence survives: the branch
`HistoryBcsOpenings` deletes is a constructed disjunct with a witness.
-/

import Assurance.SemanticHistoryBcsGame

namespace Minidregg.Assurance.RawHistoryBcsOpenings

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryBcsClaimProjection
open Minidregg.Assurance.SemanticHistoryBcsGame
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticHistoryWARPAdditiveJoin
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Loom
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

universe uSemantics uClauseInput uClauseQuery uClauseReply uClauseOutcome

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : Nat} {Op : Type}
variable
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n F}
    {headerCells : HistoryAdmissionContext → BindingIx → F}
    {C : Submodule F (BoundReceiptIx n → F)}
    {S : BindingCommitment Digest F (BoundReceiptIx n) Op}

local notation "HistoryHead" => VerifiedHistoryHead
  (n := n) (F := F) (Op := Op) manifest registry clauseEvidence family
  headerCells C S

/-- The executable coordinate alphabet the deployed checker actually runs on. -/
abbrev ReceiptCoordinate (n : Nat) := Fin (CoordinateCount (BoundReceiptIx n))

/-- The head's retained link word at round `j`, read in the deployed
coordinate order.  This is the object a submitted transcript is being *read
as*; a transcript never mentions it, which is the point. -/
def honestWord (head : HistoryHead) (j : Fin head.foldRounds) :
    ReceiptCoordinate n → F :=
  reindexWord (head.foldLinkWord j)

/-- The honest word is in the deployed reed--Solomon code, because the head's
fold trace already put it in the semantic code. -/
theorem honestWord_mem (head : HistoryHead) (domain : BoundReceiptIx n ↪ F)
    (degree : Nat) (codeExact : C = reedSolomonCode domain degree)
    (j : Fin head.foldRounds) :
    honestWord head j ∈ reedSolomonCode (reindexDomain domain) degree :=
  reindexWord_mem_reedSolomonCode domain degree (head.foldLinkWord j)
    (by simpa only [← codeExact] using historyLinkWord_mem head j)

/-- The carrier-generic synthesis step, stated once at the reindexed boundary
so nothing downstream has to unify `Fintype.card (BoundReceiptIx n)` inside a
larger goal.  This is the exact sibling of `reindexedBcsWord_committed`, with
its binding premise replaced by literal column agreement -- the whole content
of this module in one line. -/
theorem reindexedBcsWord_of_colsExact
    (domain : BoundReceiptIx n ↪ F) (degree openedCount : Nat)
    (degreeLeOpened : degree ≤ openedCount)
    (queries : Fin openedCount → ReceiptCoordinate n)
    (queriesDistinct : Function.Injective (reindexDomain domain ∘ queries))
    (word : BoundReceiptIx n → F)
    (wordInCode : word ∈ reedSolomonCode domain degree)
    (message : BcsMsg Digest F Op openedCount)
    (colsExact : ∀ i, message.cols i = reindexWord word (queries i)) :
    bcsWord (reindexDomain domain) degree queries message = reindexWord word :=
  bcsWord_of_colsExact (reindexDomain domain) degreeLeOpened queriesDistinct
    (reindexWord_mem_reedSolomonCode domain degree word wordInCode) colsExact

/-! ## The transcript: what the verifier accepted, and nothing more -/

/-- Roots, submitted columns, and submitted opening proofs, checked by an
executable `OpeningScheme`.  There is deliberately no root attribution field
and no binding: this is the adversary's message tape as the verifier saw it. -/
structure RawHistoryBcsTranscript
    (E : OpeningScheme Digest F (ReceiptCoordinate n) Op)
    (head : HistoryHead)
    (domain : BoundReceiptIx n ↪ F) (degree openedCount : Nat) where
  /-- The semantic code is the reed--Solomon code of the deployed domain. -/
  codeExact : C = reedSolomonCode domain degree
  /-- Enough columns to erasure-recover a codeword. -/
  degreeLeOpened : degree ≤ openedCount
  /-- The queried coordinates. -/
  queries : Fin openedCount → ReceiptCoordinate n
  /-- Distinct evaluation points, as erasure recovery requires. -/
  queriesDistinct : Function.Injective (reindexDomain domain ∘ queries)
  /-- One submitted message per retained fold round. -/
  messages : Fin head.foldRounds → BcsMsg Digest F Op openedCount
  /-- Every submitted column was ACCEPTED against its own submitted root.
  Acceptance is all this says; it does not say the column is correct. -/
  columnsAccepted : ∀ j, ColsOpen E queries (messages j)

namespace RawHistoryBcsTranscript

/-! ### Branch 1 -- root attribution, which may simply fail -/

/-- Each submitted root really is the executable commitment of the head's
retained link word for that round.  Carried separately because an adversary
that fails this has not broken the PCS: it has submitted a root for some other
word.  Charging that to oracle/transport rather than PCS is a deployment
decision this module records and does not prove. -/
structure RootPreimage
    {E : OpeningScheme Digest F (ReceiptCoordinate n) Op}
    {head : HistoryHead}
    {domain : BoundReceiptIx n ↪ F} {degree openedCount : Nat}
    (transcript : RawHistoryBcsTranscript E head domain degree openedCount) :
    Prop where
  rootExact : ∀ j : Fin head.foldRounds,
    (transcript.messages j).root = E.commit (honestWord head j)

/-! ### Branch 2 -- the retained equivocation -/

/-- A submitted column that disagrees with the honest word at a named round.
Its content is `Loom.ColumnEquivocation`: two accepted openings of one root at
one coordinate with different values -- the exact `BindingFailure` shape the
landed Merkle reduction consumes.  This is the object the binding carrier
cannot hold. -/
def Equivocation
    {E : OpeningScheme Digest F (ReceiptCoordinate n) Op}
    {head : HistoryHead}
    {domain : BoundReceiptIx n ↪ F} {degree openedCount : Nat}
    (transcript : RawHistoryBcsTranscript E head domain degree openedCount) :
    Prop :=
  ∃ j : Fin head.foldRounds,
    ColumnEquivocation E transcript.queries (transcript.messages j)
      (honestWord head j)

/-! ### Branch 3 -- fully pinned columns -/

/-- Every submitted column at round `j` is literally the honest word's symbol.
A fact about the submitted tape, not an assumption about the scheme. -/
def ColumnsExact
    {E : OpeningScheme Digest F (ReceiptCoordinate n) Op}
    {head : HistoryHead}
    {domain : BoundReceiptIx n ↪ F} {degree openedCount : Nat}
    (transcript : RawHistoryBcsTranscript E head domain degree openedCount)
    (j : Fin head.foldRounds) : Prop :=
  ∀ i, (transcript.messages j).cols i = honestWord head j (transcript.queries i)

/-- **Erasure recovery alone.**  Pinned columns synthesize the head's retained
link word with no commitment scheme, no root, and no binding premise in the
proof -- `reindexedBcsWord_of_colsExact` is the whole content. -/
theorem bcsWord_eq_historyLink_of_columnsExact
    {E : OpeningScheme Digest F (ReceiptCoordinate n) Op}
    {head : HistoryHead}
    {domain : BoundReceiptIx n ↪ F} {degree openedCount : Nat}
    (transcript : RawHistoryBcsTranscript E head domain degree openedCount)
    (j : Fin head.foldRounds) (pinned : transcript.ColumnsExact j) :
    bcsWord (reindexDomain domain) degree transcript.queries
        (transcript.messages j) =
      honestWord head j :=
  reindexedBcsWord_of_colsExact domain degree openedCount
    transcript.degreeLeOpened transcript.queries transcript.queriesDistinct
    (head.foldLinkWord j)
    (by simpa only [← transcript.codeExact] using historyLinkWord_mem head j)
    (transcript.messages j) pinned

/-! ## The split -/

/-- **Per round, given attribution: pinned or retained.**  No property of `E`
is used; the disjunction is where a deployment pays for collision resistance
instead of assuming it. -/
theorem columnsExact_or_equivocation
    {E : OpeningScheme Digest F (ReceiptCoordinate n) Op}
    {head : HistoryHead}
    {domain : BoundReceiptIx n ↪ F} {degree openedCount : Nat}
    (transcript : RawHistoryBcsTranscript E head domain degree openedCount)
    (attribution : transcript.RootPreimage) (j : Fin head.foldRounds) :
    transcript.ColumnsExact j ∨
      ColumnEquivocation E transcript.queries (transcript.messages j)
        (honestWord head j) := by
  by_cases pinned : transcript.ColumnsExact j
  · exact Or.inl pinned
  · obtain ⟨i, mismatch⟩ := not_forall.mp pinned
    exact Or.inr ⟨i, transcript.columnsAccepted j i,
      by rw [attribution.rootExact j]; exact E.verifyOpen_commit _ _, mismatch⟩

/-- **The whole transcript, given attribution: exact or retained.**  With no
equivocation anywhere, the submitted roots and columns read as exactly the
head's unshifted word/challenge transcript -- the identity
`HistoryBcsOpenings.bcsRounds_exact` bought with binding, bought here with a
named, retained, extractable failure event instead. -/
theorem bcsRounds_exact_of_noEquivocation
    {E : OpeningScheme Digest F (ReceiptCoordinate n) Op}
    {head : HistoryHead}
    {domain : BoundReceiptIx n ↪ F} {degree openedCount : Nat}
    (transcript : RawHistoryBcsTranscript E head domain degree openedCount)
    (attribution : transcript.RootPreimage)
    (collisionFree : ¬transcript.Equivocation) :
    bcsRounds (reindexDomain domain) degree transcript.queries
        (List.ofFn fun j : Fin head.foldRounds =>
          (transcript.messages j, head.foldChallenges j)) =
      List.ofFn fun j : Fin head.foldRounds =>
        (reindexWord (head.foldLinkWord j), head.foldChallenges j) := by
  rw [Minidregg.Loom.bcsRounds_ofFn]
  apply congrArg List.ofFn
  funext j
  rcases transcript.columnsExact_or_equivocation attribution j with pinned | equivocation
  · have exactWord := transcript.bcsWord_eq_historyLink_of_columnsExact j pinned
    simp only [honestWord] at exactWord
    rw [exactWord]
  · exact absurd ⟨j, equivocation⟩ collisionFree

/-- **The three-way split, assembled.**  Exactly the classification the resume
order asks for, with each branch a constructed object rather than a case that
was deleted earlier. -/
theorem attribution_split
    {E : OpeningScheme Digest F (ReceiptCoordinate n) Op}
    {head : HistoryHead}
    {domain : BoundReceiptIx n ↪ F} {degree openedCount : Nat}
    (transcript : RawHistoryBcsTranscript E head domain degree openedCount) :
    ¬transcript.RootPreimage ∨
      transcript.Equivocation ∨
      bcsRounds (reindexDomain domain) degree transcript.queries
          (List.ofFn fun j : Fin head.foldRounds =>
            (transcript.messages j, head.foldChallenges j)) =
        List.ofFn fun j : Fin head.foldRounds =>
          (reindexWord (head.foldLinkWord j), head.foldChallenges j) := by
  by_cases attribution : transcript.RootPreimage
  · by_cases equivocation : transcript.Equivocation
    · exact Or.inr (Or.inl equivocation)
    · exact Or.inr (Or.inr
        (transcript.bcsRounds_exact_of_noEquivocation attribution equivocation))
  · exact Or.inl attribution

end RawHistoryBcsTranscript

/-! ## Why the binding carrier could not host this

The two theorems below are the load-bearing audit of the whole module.  The
first says the retained branch is *refuted* -- not unused -- the moment the
executable scheme is replaced by a position-binding one.  The second says the
raw carrier is strictly more primitive: hand it binding and the old carrier
falls out with the same messages. -/

/-- At a `BindingCommitment` the equivocation branch is empty.  This is the
exact step `no_retained_opening_mismatch` observed, now located at its cause:
not the history construction, but the *type of the scheme the columns were
checked against*. -/
theorem equivocation_impossible_of_binding
    {head : HistoryHead}
    {domain : BoundReceiptIx n ↪ F} {degree openedCount : Nat}
    (B : BindingCommitment Digest F (ReceiptCoordinate n) Op)
    (transcript : RawHistoryBcsTranscript B.toOpeningScheme head
      domain degree openedCount) :
    ¬transcript.Equivocation := by
  rintro ⟨j, equivocation⟩
  exact not_columnEquivocation B equivocation

/-- **The raw carrier subsumes the binding one.**  Instantiated at the
reindexed semantic commitment, a raw transcript with root attribution *is* a
`HistoryBcsOpenings`, message for message.  So nothing lands beside the old
structure: it is now a projection of this one. -/
def toHistoryBcsOpenings
    {head : HistoryHead}
    {domain : BoundReceiptIx n ↪ F} {degree openedCount : Nat}
    (transcript : RawHistoryBcsTranscript
      (reindexCommitment (S := S)).toOpeningScheme head domain degree openedCount)
    (attribution : transcript.RootPreimage) :
    HistoryBcsOpenings (S := S) head domain degree openedCount where
  codeExact := transcript.codeExact
  degreeLeOpened := transcript.degreeLeOpened
  queries := transcript.queries
  queriesDistinct := transcript.queriesDistinct
  messages := transcript.messages
  rootExact := fun j => by
    simpa only [honestWord, reindexCommitment_commit] using attribution.rootExact j
  columnsOpen := transcript.columnsAccepted

/-! ## Premise inhabitation

The structure is not vacuous: for any retained head and any admissible query
plan there is an honest transcript over the reindexed semantic commitment,
with attribution and every column pinned. -/

/-- The honest transcript: commit each retained link word, open it at the
queried coordinates, submit exactly those symbols. -/
def honestTranscript
    (head : HistoryHead)
    (domain : BoundReceiptIx n ↪ F) (degree openedCount : Nat)
    (codeExact : C = reedSolomonCode domain degree)
    (degreeLeOpened : degree ≤ openedCount)
    (queries : Fin openedCount → ReceiptCoordinate n)
    (queriesDistinct : Function.Injective (reindexDomain domain ∘ queries)) :
    RawHistoryBcsTranscript
      (reindexCommitment (S := S)).toOpeningScheme head domain degree openedCount where
  codeExact := codeExact
  degreeLeOpened := degreeLeOpened
  queries := queries
  queriesDistinct := queriesDistinct
  messages := fun j =>
    { root := (reindexCommitment (S := S)).commit (reindexWord (head.foldLinkWord j))
      cols := fun i => reindexWord (head.foldLinkWord j) (queries i)
      ops := fun i => (reindexCommitment (S := S)).openAt
        (reindexWord (head.foldLinkWord j)) (queries i) }
  columnsAccepted := fun _ i =>
    (reindexCommitment (S := S)).verifyOpen_commit _ (queries i)

/-- **Satisfiable, attribution side.** -/
theorem honestTranscript_attribution
    (head : HistoryHead)
    (domain : BoundReceiptIx n ↪ F) (degree openedCount : Nat)
    (codeExact : C = reedSolomonCode domain degree)
    (degreeLeOpened : degree ≤ openedCount)
    (queries : Fin openedCount → ReceiptCoordinate n)
    (queriesDistinct : Function.Injective (reindexDomain domain ∘ queries)) :
    (honestTranscript head domain degree openedCount codeExact
      degreeLeOpened queries queriesDistinct).RootPreimage :=
  ⟨fun _ => rfl⟩

/-! ### And the retained branch is inhabited, not merely unrefuted

`equivocation_impossible_of_binding` shows the branch is empty at every
`BindingCommitment`.  On its own that is exactly the kind of result that could
mean the disjunct is dead everywhere.  The witnesses below rule that out: at
an executable scheme with no binding field there is a transcript that carries
root attribution, has every column accepted, and still submits the wrong
symbol -- so `columnsExact_or_equivocation` really does branch. -/

/-- The equivocator at the history alphabet: one root, everything accepted.
A genuine `OpeningScheme` -- completeness is trivial -- with the binding field
absent rather than assumed false. -/
def equivocalScheme (root : Digest) (op : Op) :
    OpeningScheme Digest F (ReceiptCoordinate n) Op where
  commit := fun _ => root
  openAt := fun _ _ => op
  verifyOpen := fun _ _ _ _ => True
  verifyOpen_commit := fun _ _ => trivial

/-- It is not position-binding, and that is a refutation rather than a gap:
one root opens at one coordinate to two different field elements. -/
theorem equivocalScheme_not_binding (root : Digest) (op : Op)
    (i : ReceiptCoordinate n) :
    ¬(equivocalScheme (F := F) (n := n) root op).PositionBinding := by
  intro binding
  exact zero_ne_one (binding root i 0 1 op op trivial trivial)

/-- A transcript over the equivocator submitting every symbol off by one. -/
def equivocalTranscript
    (head : HistoryHead)
    (domain : BoundReceiptIx n ↪ F) (degree openedCount : Nat)
    (codeExact : C = reedSolomonCode domain degree)
    (degreeLeOpened : degree ≤ openedCount)
    (queries : Fin openedCount → ReceiptCoordinate n)
    (queriesDistinct : Function.Injective (reindexDomain domain ∘ queries))
    (root : Digest) (op : Op) :
    RawHistoryBcsTranscript (equivocalScheme root op) head domain degree
      openedCount where
  codeExact := codeExact
  degreeLeOpened := degreeLeOpened
  queries := queries
  queriesDistinct := queriesDistinct
  messages := fun j =>
    { root := root
      cols := fun i => honestWord head j (queries i) + 1
      ops := fun _ => op }
  columnsAccepted := fun _ _ => trivial

/-- **Satisfiable, attribution side, at the equivocator**: the submitted root
IS the scheme's commitment of the honest word.  Both premises of
`columnsExact_or_equivocation` therefore hold. -/
theorem equivocalTranscript_rootPreimage
    (head : HistoryHead)
    (domain : BoundReceiptIx n ↪ F) (degree openedCount : Nat)
    (codeExact : C = reedSolomonCode domain degree)
    (degreeLeOpened : degree ≤ openedCount)
    (queries : Fin openedCount → ReceiptCoordinate n)
    (queriesDistinct : Function.Injective (reindexDomain domain ∘ queries))
    (root : Digest) (op : Op) :
    (equivocalTranscript head domain degree openedCount codeExact
      degreeLeOpened queries queriesDistinct root op).RootPreimage :=
  ⟨fun _ => rfl⟩

/-- **Teeth: the retained equivocation is a built object.**  Given one fold
round and one query, the same transcript exhibits `Equivocation` -- an
accepted column, an accepted honest opening at the identical root and
coordinate, and unequal values.  This is the disjunct `HistoryBcsOpenings`
proves cannot exist. -/
theorem equivocalTranscript_equivocation
    (head : HistoryHead)
    (domain : BoundReceiptIx n ↪ F) (degree openedCount : Nat)
    (codeExact : C = reedSolomonCode domain degree)
    (degreeLeOpened : degree ≤ openedCount)
    (queries : Fin openedCount → ReceiptCoordinate n)
    (queriesDistinct : Function.Injective (reindexDomain domain ∘ queries))
    (root : Digest) (op : Op)
    (hasRound : 0 < head.foldRounds) (hasQuery : 0 < openedCount) :
    (equivocalTranscript head domain degree openedCount codeExact
      degreeLeOpened queries queriesDistinct root op).Equivocation :=
  ⟨⟨0, hasRound⟩, ⟨0, hasQuery⟩, trivial, trivial, by
    simp [equivocalTranscript]⟩

/-- And it is not pinned: the same round fails `ColumnsExact`, so
`columnsExact_or_equivocation` selects its second disjunct here. -/
theorem equivocalTranscript_not_columnsExact
    (head : HistoryHead)
    (domain : BoundReceiptIx n ↪ F) (degree openedCount : Nat)
    (codeExact : C = reedSolomonCode domain degree)
    (degreeLeOpened : degree ≤ openedCount)
    (queries : Fin openedCount → ReceiptCoordinate n)
    (queriesDistinct : Function.Injective (reindexDomain domain ∘ queries))
    (root : Digest) (op : Op)
    (hasRound : 0 < head.foldRounds) (hasQuery : 0 < openedCount) :
    ¬(equivocalTranscript head domain degree openedCount codeExact
      degreeLeOpened queries queriesDistinct root op).ColumnsExact
        ⟨0, hasRound⟩ := by
  intro pinned
  have mismatch := pinned ⟨0, hasQuery⟩
  simp only [equivocalTranscript] at mismatch
  simp at mismatch

/-- **Satisfiable, pinned side.** -/
theorem honestTranscript_columnsExact
    (head : HistoryHead)
    (domain : BoundReceiptIx n ↪ F) (degree openedCount : Nat)
    (codeExact : C = reedSolomonCode domain degree)
    (degreeLeOpened : degree ≤ openedCount)
    (queries : Fin openedCount → ReceiptCoordinate n)
    (queriesDistinct : Function.Injective (reindexDomain domain ∘ queries))
    (j : Fin head.foldRounds) :
    (honestTranscript head domain degree openedCount codeExact
      degreeLeOpened queries queriesDistinct).ColumnsExact j :=
  fun _ => rfl

/-- info: 'Minidregg.Assurance.RawHistoryBcsOpenings.RawHistoryBcsTranscript.bcsWord_eq_historyLink_of_columnsExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RawHistoryBcsTranscript.bcsWord_eq_historyLink_of_columnsExact
/-- info: 'Minidregg.Assurance.RawHistoryBcsOpenings.RawHistoryBcsTranscript.columnsExact_or_equivocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RawHistoryBcsTranscript.columnsExact_or_equivocation
/-- info: 'Minidregg.Assurance.RawHistoryBcsOpenings.RawHistoryBcsTranscript.bcsRounds_exact_of_noEquivocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RawHistoryBcsTranscript.bcsRounds_exact_of_noEquivocation
/-- info: 'Minidregg.Assurance.RawHistoryBcsOpenings.RawHistoryBcsTranscript.attribution_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RawHistoryBcsTranscript.attribution_split
/-- info: 'Minidregg.Assurance.RawHistoryBcsOpenings.equivocation_impossible_of_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms equivocation_impossible_of_binding
/-- info: 'Minidregg.Assurance.RawHistoryBcsOpenings.equivocalScheme_not_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms equivocalScheme_not_binding
/-- info: 'Minidregg.Assurance.RawHistoryBcsOpenings.equivocalTranscript_rootPreimage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms equivocalTranscript_rootPreimage
/-- info: 'Minidregg.Assurance.RawHistoryBcsOpenings.equivocalTranscript_equivocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms equivocalTranscript_equivocation
/-- info: 'Minidregg.Assurance.RawHistoryBcsOpenings.equivocalTranscript_not_columnsExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms equivocalTranscript_not_columnsExact
/-- info: 'Minidregg.Assurance.RawHistoryBcsOpenings.honestTranscript_attribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honestTranscript_attribution
/-- info: 'Minidregg.Assurance.RawHistoryBcsOpenings.honestTranscript_columnsExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honestTranscript_columnsExact

end

end Minidregg.Assurance.RawHistoryBcsOpenings
