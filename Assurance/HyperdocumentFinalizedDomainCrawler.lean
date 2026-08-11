/-
# Assurance.HyperdocumentFinalizedDomainCrawler -- exact finite-domain crawling

This module bridges the four-slot logical index page and a finite,
authoritatively declared finalized search domain.  A domain commits to every
page and to the ordered vector of page roots through an explicit commitment
scheme.  A prefix cursor is exact: below `nextPage` both the canonical page and
its root are present, while at and above it both are absent.

The crawler accepts pages in order, recognizes exact replay, and fails closed
on a stale finality checkpoint, stale cursor, missing page, root mismatch, or a
conflicting duplicate.  A one-page finalized successor supports incremental
deletion and rebinding without weakening the exact-domain invariant.  Its
checkpoint must extend the prior manifest root, so a same-height fork is not a
lawful incremental update.

The central result is deliberately finite: for a complete crawler state,
returned backlinks are equivalent to backlinks in the exact pages of the
declared finalized domain.  No result extends that domain to an unbounded
history or web, proves physical/network availability, proves external
finality, or proves collision resistance for an eventual concrete scheme.
-/
import Kernel.HyperdocumentIndexSync

namespace Minidregg.Assurance.HyperdocumentFinalizedDomainCrawler

open Minidregg.Kernel.HyperdocumentIndexSync
open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

local instance snapshotDecidableEq (capacity : Nat) :
    DecidableEq (Snapshot capacity) := Classical.decEq _

local instance pageCacheDecidableEq (pageCount : Nat) :
    DecidableEq (Fin pageCount -> Option (Snapshot 4)) := Classical.decEq _

local instance rootCacheDecidableEq (pageCount : Nat) :
    DecidableEq (Fin pageCount -> Option Digest) := Classical.decEq _

/-! ## Page and manifest commitments -/

/-- The authoritative commitment operations are explicit inputs.  A concrete
deployment may instantiate these with the canonical page materializer and
cSHAKE, but this protocol does not manufacture collision resistance from the
function types. -/
structure CommitmentScheme (pageCount : Nat) where
  pageRoot : Snapshot 4 -> Digest
  manifestRoot : (Fin pageCount -> Digest) -> Digest

/-- Pair-scoped binding is exactly the cryptographic premise needed to turn a
root equality into equality of two logical pages. -/
structure PagePairBinding {pageCount : Nat}
    (scheme : CommitmentScheme pageCount)
    (left right : Snapshot 4) : Prop where
  eq_of_root_eq : scheme.pageRoot left = scheme.pageRoot right -> left = right

/-- A finalized finite-domain checkpoint binds a history namespace, an exact
epoch, an inclusive finalized sequence ceiling, the parent manifest root, and
the current ordered page manifest root. -/
structure FinalizedCheckpoint where
  historyDomain : Digest
  epoch : Nat
  finalizedThrough : Nat
  parentManifestRoot : Option Digest
  manifestRoot : Digest
  deriving DecidableEq, Repr

/-- An incremental finalized checkpoint stays in one history namespace,
advances exactly one epoch, never lowers the finalized sequence ceiling, and
names the exact previous manifest as its parent. -/
def FinalizedCheckpoint.Follows
    (before after : FinalizedCheckpoint) : Prop :=
  after.historyDomain = before.historyDomain /\
    after.epoch = before.epoch + 1 /\
    before.finalizedThrough <= after.finalizedThrough /\
    after.parentManifestRoot = some before.manifestRoot

instance (before after : FinalizedCheckpoint) :
    Decidable (before.Follows after) := by
  unfold FinalizedCheckpoint.Follows
  infer_instance

/-- A same-domain next-epoch checkpoint that does not name the prior manifest
is an explicit finalized-history fork for this incremental protocol. -/
def FinalizedCheckpoint.IsFork
    (before after : FinalizedCheckpoint) : Prop :=
  after.historyDomain = before.historyDomain /\
    after.epoch = before.epoch + 1 /\
  after.parentManifestRoot ≠ some before.manifestRoot

instance (before after : FinalizedCheckpoint) :
    Decidable (before.IsFork after) := by
  unfold FinalizedCheckpoint.IsFork
  infer_instance

/-- A finite authoritative domain.  External finality is proof-relevant input,
not inferred from a sequence number or digest.  Every page is fresh, belongs
to the named history namespace, and is at or below the finalized ceiling. -/
structure DeclaredDomain (pageCount : Nat)
    (ExternallyFinal : FinalizedCheckpoint -> Prop) where
  scheme : CommitmentScheme pageCount
  checkpoint : FinalizedCheckpoint
  externallyFinal : ExternallyFinal checkpoint
  pages : Fin pageCount -> Snapshot 4
  pageRoots : Fin pageCount -> Digest
  pageRootExact : forall page, pageRoots page = scheme.pageRoot (pages page)
  manifestRootExact : checkpoint.manifestRoot = scheme.manifestRoot pageRoots
  pageFresh : forall page, (pages page).Fresh
  pageInFinalizedDomain : forall page,
    (pages page).sourceCheckpoint.historyDomain = checkpoint.historyDomain /\
      (pages page).sourceCheckpoint.sequence <= checkpoint.finalizedThrough

/-! ## Exact prefix cursor -/

/-- `nextPage` is the first page not durably present.  Cached pages and cached
roots are kept separately so omission and root drift remain observable. -/
structure CrawlState (pageCount : Nat) where
  checkpoint : FinalizedCheckpoint
  nextPage : Nat
  pages : Fin pageCount -> Option (Snapshot 4)
  roots : Fin pageCount -> Option Digest

/-- Exactness is two-sided: the covered prefix equals the authoritative domain
and the uncovered suffix contains neither a page nor a root. -/
def CrawlState.ExactPrefix
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (state : CrawlState pageCount)
    (domain : DeclaredDomain pageCount ExternallyFinal) : Prop :=
  state.checkpoint = domain.checkpoint /\
    state.nextPage <= pageCount /\
    forall page,
      if page.val < state.nextPage then
        state.pages page = some (domain.pages page) /\
          state.roots page = some (domain.pageRoots page)
      else
        state.pages page = none /\ state.roots page = none

def CrawlState.CompleteFor
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (state : CrawlState pageCount)
    (domain : DeclaredDomain pageCount ExternallyFinal) : Prop :=
  state.ExactPrefix domain /\ state.nextPage = pageCount

theorem complete_cache_exact
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (complete : state.CompleteFor domain) :
    state.pages = (fun page => some (domain.pages page)) /\
      state.roots = (fun page => some (domain.pageRoots page)) := by
  rcases complete with ⟨⟨_, _, prefixInvariant⟩, cursor⟩
  constructor <;> funext page
  · have covered : page.val < state.nextPage := by
      rw [cursor]
      exact page.isLt
    have pageExact := prefixInvariant page
    rw [if_pos covered] at pageExact
    exact pageExact.1
  · have covered : page.val < state.nextPage := by
      rw [cursor]
      exact page.isLt
    have pageExact := prefixInvariant page
    rw [if_pos covered] at pageExact
    exact pageExact.2

def emptyState
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal) : CrawlState pageCount :=
  { checkpoint := domain.checkpoint
    nextPage := 0
    pages := fun _ => none
    roots := fun _ => none }

theorem emptyState_exact
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal) :
    (emptyState domain).ExactPrefix domain := by
  refine ⟨rfl, Nat.zero_le _, ?_⟩
  intro page
  simp [emptyState]

/-- The exact next state after accepting one page at the cursor. -/
def CrawlState.install {pageCount : Nat}
    (state : CrawlState pageCount) (page : Fin pageCount)
    (payload : Snapshot 4) (root : Digest) : CrawlState pageCount :=
  { checkpoint := state.checkpoint
    nextPage := state.nextPage + 1
    pages := Function.update state.pages page (some payload)
    roots := Function.update state.roots page (some root) }

/-! ## Fail-closed sequential ingestion -/

structure PageEnvelope (pageCount : Nat) where
  checkpoint : FinalizedCheckpoint
  page : Fin pageCount
  payload : Option (Snapshot 4)
  claimedRoot : Digest

inductive RejectReason
  | staleFinality
  | reorg
  | staleCursor
  | missingPage
  | staleRoot
  | duplicateConflict
  | nonFinalizedExtension
  deriving DecidableEq, Repr

inductive IngestResult (pageCount : Nat)
  | applied (state : CrawlState pageCount)
  | replayed (state : CrawlState pageCount)
  | rejected (reason : RejectReason)

/-- Root-only ingestion.  Equality to the authoritative page is obtained below
from the explicit pair-scoped binding premise, never from digest equality
alone. -/
def ingest
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (envelope : PageEnvelope pageCount) :
    IngestResult pageCount :=
  if state.checkpoint ≠ domain.checkpoint then
    if state.checkpoint.historyDomain = domain.checkpoint.historyDomain /\
        state.checkpoint.epoch = domain.checkpoint.epoch then
      .rejected .reorg
    else
      .rejected .staleFinality
  else if envelope.checkpoint ≠ state.checkpoint then
    .rejected .staleFinality
  else if envelope.page.val < state.nextPage then
    match envelope.payload with
    | none => .rejected .missingPage
    | some payload =>
        if state.pages envelope.page = some payload /\
            state.roots envelope.page = some envelope.claimedRoot /\
            envelope.claimedRoot = domain.pageRoots envelope.page /\
            domain.scheme.pageRoot payload = envelope.claimedRoot then
          .replayed state
        else
          .rejected .duplicateConflict
  else if envelope.page.val ≠ state.nextPage then
    .rejected .staleCursor
  else
    match envelope.payload with
    | none => .rejected .missingPage
    | some payload =>
        if envelope.claimedRoot ≠ domain.pageRoots envelope.page then
          .rejected .staleRoot
        else if domain.scheme.pageRoot payload ≠ envelope.claimedRoot then
          .rejected .staleRoot
        else
          .applied (state.install envelope.page payload envelope.claimedRoot)

theorem page_eq_of_bound_root
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal) (page : Fin pageCount)
    (payload : Snapshot 4)
    (binding : PagePairBinding domain.scheme payload (domain.pages page))
    (rootExact : domain.scheme.pageRoot payload = domain.pageRoots page) :
    payload = domain.pages page := by
  apply binding.eq_of_root_eq
  simpa [domain.pageRootExact page] using rootExact

/-- Installing the exact page at the exact cursor grows the exact prefix by one.
The pair binding premise is precisely the collision-resistance obligation used
to turn the checked page root into page equality. -/
theorem install_preserves_exactPrefix
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (prefixInvariant : state.ExactPrefix domain)
    (page : Fin pageCount) (atCursor : page.val = state.nextPage)
    (payload : Snapshot 4)
    (binding : PagePairBinding domain.scheme payload (domain.pages page))
    (rootExact : domain.scheme.pageRoot payload = domain.pageRoots page) :
    (state.install page payload (domain.pageRoots page)).ExactPrefix domain := by
  have payloadExact : payload = domain.pages page :=
    page_eq_of_bound_root domain page payload binding rootExact
  subst payload
  rcases prefixInvariant with ⟨checkpoint, cursorBound, coveredProof⟩
  refine ⟨checkpoint, ?_, ?_⟩
  · have pageBound : page.val + 1 <= pageCount := Nat.succ_le_of_lt page.isLt
    simpa [CrawlState.install, atCursor] using pageBound
  · intro current
    simp only [CrawlState.install]
    by_cases currentAtPage : current = page
    · subst current
      simp [atCursor]
    · have valuesDifferent : current.val ≠ page.val := by
        intro equal
        apply currentAtPage
        exact Fin.ext equal
      by_cases covered : current.val < state.nextPage
      · have stillCovered : current.val < state.nextPage + 1 := by omega
        rw [if_pos stillCovered]
        have old := coveredProof current
        rw [if_pos covered] at old
        simpa [CrawlState.install, Function.update, currentAtPage] using old
      · have beyond : state.nextPage + 1 <= current.val := by
          have ge : state.nextPage <= current.val := Nat.le_of_not_gt covered
          have ne : current.val ≠ state.nextPage := by
            simpa [atCursor] using valuesDifferent
          omega
        rw [if_neg (Nat.not_lt_of_ge beyond)]
        have old := coveredProof current
        rw [if_neg covered] at old
        simpa [CrawlState.install, Function.update, currentAtPage] using old

theorem ingest_applies_at_exact_cursor
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (prefixInvariant : state.ExactPrefix domain)
    (page : Fin pageCount) (atCursor : page.val = state.nextPage)
    (payload : Snapshot 4) (claimed : Digest)
    (claimedExact : claimed = domain.pageRoots page)
    (rootExact : domain.scheme.pageRoot payload = claimed) :
    ingest domain state ⟨domain.checkpoint, page, some payload, claimed⟩ =
      .applied (state.install page payload claimed) := by
  rcases prefixInvariant with ⟨checkpoint, _, _⟩
  subst claimed
  simp [ingest, checkpoint, atCursor, rootExact]

theorem ingest_preserves_exact_at_cursor
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (prefixInvariant : state.ExactPrefix domain)
    (page : Fin pageCount) (atCursor : page.val = state.nextPage)
    (payload : Snapshot 4)
    (binding : PagePairBinding domain.scheme payload (domain.pages page))
    (rootExact : domain.scheme.pageRoot payload = domain.pageRoots page) :
    (state.install page payload (domain.pageRoots page)).ExactPrefix domain :=
  install_preserves_exactPrefix domain state prefixInvariant page atCursor payload binding
    rootExact

/-- An accepted page is an exact replay after the installed state is reopened;
the page is not inserted twice. -/
theorem ingest_retry_replayed
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (prefixInvariant : state.ExactPrefix domain)
    (page : Fin pageCount) (atCursor : page.val = state.nextPage)
    (payload : Snapshot 4)
    (rootExact : domain.scheme.pageRoot payload = domain.pageRoots page) :
    let next := state.install page payload (domain.pageRoots page)
    ingest domain next
      ⟨domain.checkpoint, page, some payload, domain.pageRoots page⟩ =
        .replayed next := by
  dsimp
  rcases prefixInvariant with ⟨checkpoint, _, _⟩
  have covered : page.val < state.nextPage + 1 := by omega
  simp [ingest, CrawlState.install, checkpoint, atCursor, rootExact]

theorem ingest_missing_page_rejected
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (prefixInvariant : state.ExactPrefix domain)
    (page : Fin pageCount) (atCursor : page.val = state.nextPage)
    (claimed : Digest) :
    ingest domain state ⟨domain.checkpoint, page, none, claimed⟩ =
      .rejected .missingPage := by
  rcases prefixInvariant with ⟨checkpoint, _, _⟩
  simp [ingest, checkpoint, atCursor]

theorem ingest_stale_cursor_rejected
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (prefixInvariant : state.ExactPrefix domain)
    (page : Fin pageCount) (ahead : state.nextPage < page.val)
    (payload : Snapshot 4) (claimed : Digest) :
    ingest domain state ⟨domain.checkpoint, page, some payload, claimed⟩ =
      .rejected .staleCursor := by
  rcases prefixInvariant with ⟨checkpoint, _, _⟩
  have notBehind : ¬ page.val < state.nextPage := by omega
  have notAt : page.val ≠ state.nextPage := by omega
  simp [ingest, checkpoint, notBehind, notAt]

theorem ingest_stale_root_rejected
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (prefixInvariant : state.ExactPrefix domain)
    (page : Fin pageCount) (atCursor : page.val = state.nextPage)
    (payload : Snapshot 4) (claimed : Digest)
    (stale : claimed ≠ domain.pageRoots page) :
    ingest domain state ⟨domain.checkpoint, page, some payload, claimed⟩ =
      .rejected .staleRoot := by
  rcases prefixInvariant with ⟨checkpoint, _, _⟩
  simp [ingest, checkpoint, atCursor, stale]

theorem ingest_stale_finality_rejected
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (prefixInvariant : state.ExactPrefix domain)
    (page : Fin pageCount)
    (staleCheckpoint : FinalizedCheckpoint)
    (stale : staleCheckpoint ≠ domain.checkpoint)
    (payload : Option (Snapshot 4)) (claimed : Digest) :
    ingest domain state ⟨staleCheckpoint, page, payload, claimed⟩ =
      .rejected .staleFinality := by
  rcases prefixInvariant with ⟨checkpoint, _, _⟩
  simp [ingest, checkpoint, stale]

/-! ## Logical durability and restart -/

/-- Only `durable` survives a crash.  This is a logical device model, not a
claim about a filesystem, database, or power-loss boundary. -/
structure Device (pageCount : Nat) where
  durable : CrawlState pageCount
  staged : Option (CrawlState pageCount)

def Device.stage {pageCount : Nat} (device : Device pageCount)
    (next : CrawlState pageCount) : Device pageCount :=
  { device with staged := some next }

def Device.sync {pageCount : Nat} (device : Device pageCount) :
    Device pageCount :=
  match device.staged with
  | none => device
  | some next => ⟨next, none⟩

def Device.crash {pageCount : Nat} (device : Device pageCount) :
    Device pageCount :=
  ⟨device.durable, none⟩

def Device.reopen {pageCount : Nat} (device : Device pageCount) :
    CrawlState pageCount :=
  device.durable

@[simp] theorem crash_before_sync_reopens_old {pageCount : Nat}
    (device : Device pageCount) (next : CrawlState pageCount) :
    (device.stage next).crash.reopen = device.durable := rfl

@[simp] theorem crash_after_sync_reopens_next {pageCount : Nat}
    (device : Device pageCount) (next : CrawlState pageCount) :
    (device.stage next).sync.crash.reopen = next := rfl

theorem sync_crash_reopen_retry_replayed
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (prefixInvariant : state.ExactPrefix domain)
    (page : Fin pageCount) (atCursor : page.val = state.nextPage)
    (payload : Snapshot 4)
    (rootExact : domain.scheme.pageRoot payload = domain.pageRoots page) :
    let next := state.install page payload (domain.pageRoots page)
    let device : Device pageCount := ⟨state, none⟩
    ingest domain ((device.stage next).sync.crash.reopen)
      ⟨domain.checkpoint, page, some payload, domain.pageRoots page⟩ =
        .replayed next := by
  dsimp
  exact ingest_retry_replayed domain state prefixInvariant page atCursor payload rootExact

/-! ## Exact finite-domain backlink theorem -/

/-- A returned backlink is a row actually found in a durably cached page. -/
def ReturnedBacklink {pageCount : Nat} (state : CrawlState pageCount)
    (target : LinkTarget) (row : IndexedRow) : Prop :=
  exists page : Fin pageCount, exists slot : Fin 4,
    exists stored : Snapshot 4,
    state.pages page = some stored /\
      backlinkAt stored.index target slot = some row

/-- A declared backlink is a row in the exact canonical page set committed by
the finalized domain. -/
def DeclaredBacklink
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (target : LinkTarget) (row : IndexedRow) : Prop :=
  exists page : Fin pageCount, exists slot : Fin 4,
    backlinkAt (domain.pages page).index target slot = some row

/-- At a complete exact cursor, results are neither more nor less than the
backlinks in the declared finalized finite domain. -/
theorem returned_iff_declared
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (complete : state.CompleteFor domain)
    (target : LinkTarget) (row : IndexedRow) :
    ReturnedBacklink state target row <-> DeclaredBacklink domain target row := by
  rcases complete with ⟨⟨_, _, prefixInvariant⟩, cursor⟩
  constructor
  · rintro ⟨page, slot, stored, cached, found⟩
    have pageCovered : page.val < state.nextPage := by
      rw [cursor]
      exact page.isLt
    have canonical := prefixInvariant page
    rw [if_pos pageCovered] at canonical
    have storedExact : stored = domain.pages page := by
      exact Option.some.inj (cached.symm.trans canonical.1)
    subst stored
    exact ⟨page, slot, found⟩
  · rintro ⟨page, slot, found⟩
    have pageCovered : page.val < state.nextPage := by
      rw [cursor]
      exact page.isLt
    have canonical := prefixInvariant page
    rw [if_pos pageCovered] at canonical
    exact ⟨page, slot, domain.pages page, canonical.1, found⟩

/-- Every live source row in a fresh declared page appears in the exact
declared backlink relation for its target. -/
theorem live_source_is_declared
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (page : Fin pageCount) (slot : Fin 4) (entry : SourceEntry)
    (source : (domain.pages page).corpus slot = some entry)
    (live : entry.record.tombstonedAt = none) :
    DeclaredBacklink domain entry.record.target
      { linkId := entry.linkId
        sourceDocument := entry.record.sourceDocument
        sourceRange := entry.record.source
        target := entry.record.target
        relation := entry.record.relation
        operation := entry.record.operation } := by
  refine ⟨page, slot, ?_⟩
  exact backlinkAt_complete (domain.pages page)
    (domain.pageFresh page) slot entry source live

/-- Soundness retains the exact target equality from the page-local query. -/
theorem declared_backlink_targets_exact
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (target : LinkTarget) (row : IndexedRow)
    (declared : DeclaredBacklink domain target row) : row.target = target := by
  rcases declared with ⟨page, slot, found⟩
  exact (backlinkAt_sound (domain.pages page).index target slot row
    found).2

/-! ## Finalized one-page updates, deletion, and rebinding -/

/-- A lawful incremental update changes exactly one page and its commitment;
all other authoritative pages and roots remain byte-for-byte scoped to the
same position. -/
structure SinglePageSuccessor
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (before after : DeclaredDomain pageCount ExternallyFinal)
    (changed : Fin pageCount) : Prop where
  follows : before.checkpoint.Follows after.checkpoint
  unchanged : forall page, page ≠ changed ->
    after.pages page = before.pages page /\
      after.pageRoots page = before.pageRoots page

/-- Install an already authenticated authoritative successor page into a
complete cache. -/
def CrawlState.installSuccessor
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (state : CrawlState pageCount)
    (after : DeclaredDomain pageCount ExternallyFinal)
    (changed : Fin pageCount) : CrawlState pageCount :=
  { checkpoint := after.checkpoint
    nextPage := pageCount
    pages := Function.update state.pages changed (some (after.pages changed))
    roots := Function.update state.roots changed
      (some (after.pageRoots changed)) }

theorem installSuccessor_complete
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (before after : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (complete : state.CompleteFor before)
    (changed : Fin pageCount)
    (successor : SinglePageSuccessor before after changed) :
    (state.installSuccessor after changed).CompleteFor after := by
  rcases complete with ⟨⟨_, _, prefixInvariant⟩, cursor⟩
  refine ⟨⟨rfl, Nat.le_refl _, ?_⟩, rfl⟩
  intro page
  simp only [CrawlState.installSuccessor]
  rw [if_pos page.isLt]
  by_cases same : page = changed
  · subst page
    simp
  · have oldCovered : page.val < state.nextPage := by
      rw [cursor]
      exact page.isLt
    have old := prefixInvariant page
    rw [if_pos oldCovered] at old
    have unchanged := successor.unchanged page same
    simpa [CrawlState.installSuccessor, Function.update, same, unchanged.1,
      unchanged.2] using old

/-- Consequently every complete finalized successor exposes exactly its new
declared backlink relation, including canonical deletion and rebinding. -/
theorem finalized_successor_results_exact
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (before after : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (complete : state.CompleteFor before)
    (changed : Fin pageCount)
    (successor : SinglePageSuccessor before after changed)
    (target : LinkTarget) (row : IndexedRow) :
    ReturnedBacklink (state.installSuccessor after changed) target row <->
      DeclaredBacklink after target row := by
  exact returned_iff_declared after (state.installSuccessor after changed)
    (installSuccessor_complete before after state complete changed successor)
    target row

/-- Tombstoning a source entry removes its row at that exact page/slot for
every target.  This is deletion handling in the canonical rebuild, not a host
index convention. -/
theorem tombstoned_slot_returns_none
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (page : Fin pageCount) (slot : Fin 4) (entry : SourceEntry)
    (source : (domain.pages page).corpus slot = some entry)
    (operation : OperationId)
    (deleted : entry.record.tombstonedAt = some operation)
    (target : LinkTarget) :
    backlinkAt (domain.pages page).index target slot = none := by
  rcases domain.pageFresh page with ⟨_, _, _, rows⟩
  rw [rows]
  simp [backlinkAt, rebuild, source, SourceEntry.row?, deleted]

/-- A live rebound source appears under its new target. -/
theorem rebound_slot_complete
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (page : Fin pageCount) (slot : Fin 4) (entry : SourceEntry)
    (source : (domain.pages page).corpus slot = some entry)
    (live : entry.record.tombstonedAt = none) :
    backlinkAt (domain.pages page).index entry.record.target slot =
      some
        { linkId := entry.linkId
          sourceDocument := entry.record.sourceDocument
          sourceRange := entry.record.source
          target := entry.record.target
          relation := entry.record.relation
          operation := entry.record.operation } :=
  backlinkAt_complete (domain.pages page) (domain.pageFresh page)
    slot entry source live

/-- The same rebound row cannot remain visible under a distinct old target. -/
theorem rebound_old_target_absent
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (domain : DeclaredDomain pageCount ExternallyFinal)
    (page : Fin pageCount) (slot : Fin 4) (entry : SourceEntry)
    (source : (domain.pages page).corpus slot = some entry)
    (live : entry.record.tombstonedAt = none)
    (oldTarget : LinkTarget) (rebound : oldTarget ≠ entry.record.target) :
    backlinkAt (domain.pages page).index oldTarget slot = none := by
  rcases domain.pageFresh page with ⟨_, _, _, rows⟩
  have targetNe : entry.record.target ≠ oldTarget := Ne.symm rebound
  rw [rows]
  simp [backlinkAt, rebuild, source, SourceEntry.row?, live, targetNe]

/-! ## Incremental delta controller and adversarial teeth -/

structure DeltaEnvelope (pageCount : Nat) where
  before : FinalizedCheckpoint
  after : FinalizedCheckpoint
  changed : Fin pageCount
  beforeRoot : Digest
  afterRoot : Digest
  payload : Option (Snapshot 4)

inductive DeltaResult (pageCount : Nat)
  | applied (state : CrawlState pageCount)
  | replayed (state : CrawlState pageCount)
  | rejected (reason : RejectReason)

/-- A finalized one-page delta is accepted only at the exact predecessor,
against both committed roots, with a present page whose canonical root is the
declared successor root.  Exact retry at the successor is replayed. -/
def applyFinalizedDelta
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (before after : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (delta : DeltaEnvelope pageCount) :
    DeltaResult pageCount :=
  if state.checkpoint = after.checkpoint then
    match delta.payload with
    | none => .rejected .missingPage
    | some payload =>
        if delta.before = before.checkpoint /\
            delta.after = after.checkpoint /\
            delta.beforeRoot = before.pageRoots delta.changed /\
            delta.afterRoot = after.pageRoots delta.changed /\
            state.pages delta.changed = some payload /\
            state.roots delta.changed = some delta.afterRoot /\
            after.scheme.pageRoot payload = delta.afterRoot then
          .replayed state
        else
          .rejected .duplicateConflict
  else if state.checkpoint ≠ before.checkpoint then
    .rejected .staleFinality
  else if before.checkpoint.IsFork after.checkpoint then
    .rejected .reorg
  else if ¬ before.checkpoint.Follows after.checkpoint then
    .rejected .nonFinalizedExtension
  else if delta.before ≠ before.checkpoint \/
      delta.after ≠ after.checkpoint then
    .rejected .staleFinality
  else if delta.beforeRoot ≠ before.pageRoots delta.changed \/
      delta.afterRoot ≠ after.pageRoots delta.changed then
    .rejected .staleRoot
  else if state.nextPage ≠ pageCount then
    .rejected .staleCursor
  else if state.pages ≠ (fun page => some (before.pages page)) then
    .rejected .staleRoot
  else if state.roots ≠ (fun page => some (before.pageRoots page)) then
    .rejected .staleRoot
  else if state.roots delta.changed ≠ some delta.beforeRoot then
    .rejected .staleRoot
  else
    match delta.payload with
    | none => .rejected .missingPage
    | some payload =>
        if after.scheme.pageRoot payload ≠ delta.afterRoot then
          .rejected .staleRoot
        else
          .applied
            { checkpoint := after.checkpoint
              nextPage := pageCount
              pages := Function.update state.pages delta.changed (some payload)
              roots := Function.update state.roots delta.changed
                (some delta.afterRoot) }

theorem finalized_fork_rejected
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (before after : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (atBefore : state.checkpoint = before.checkpoint)
    (notAfter : state.checkpoint ≠ after.checkpoint)
    (fork : before.checkpoint.IsFork after.checkpoint)
    (delta : DeltaEnvelope pageCount) :
    applyFinalizedDelta before after state delta = .rejected .reorg := by
  have beforeNeAfter : before.checkpoint ≠ after.checkpoint := by
    intro equal
    apply notAfter
    rw [atBefore, equal]
  simp [applyFinalizedDelta, atBefore, beforeNeAfter, fork]

theorem nonfinalized_extension_rejected
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (before after : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (atBefore : state.checkpoint = before.checkpoint)
    (notAfter : state.checkpoint ≠ after.checkpoint)
    (notFork : ¬ before.checkpoint.IsFork after.checkpoint)
    (notFollows : ¬ before.checkpoint.Follows after.checkpoint)
    (delta : DeltaEnvelope pageCount) :
    applyFinalizedDelta before after state delta =
      .rejected .nonFinalizedExtension := by
  have beforeNeAfter : before.checkpoint ≠ after.checkpoint := by
    intro equal
    apply notAfter
    rw [atBefore, equal]
  simp [applyFinalizedDelta, atBefore, beforeNeAfter, notFork, notFollows]

theorem finalized_delta_stale_root_rejected
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (before after : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (atBefore : state.checkpoint = before.checkpoint)
    (notAfter : state.checkpoint ≠ after.checkpoint)
    (notFork : ¬ before.checkpoint.IsFork after.checkpoint)
    (follows : before.checkpoint.Follows after.checkpoint)
    (changed : Fin pageCount) (staleAfterRoot : Digest)
    (stale : staleAfterRoot ≠ after.pageRoots changed)
    (payload : Option (Snapshot 4)) :
    applyFinalizedDelta before after state
      ⟨before.checkpoint, after.checkpoint, changed,
        before.pageRoots changed, staleAfterRoot, payload⟩ =
      .rejected .staleRoot := by
  have beforeNeAfter : before.checkpoint ≠ after.checkpoint := by
    intro equal
    apply notAfter
    rw [atBefore, equal]
  simp [applyFinalizedDelta, atBefore, beforeNeAfter, notFork, follows, stale]

theorem conflicting_replayed_delta_rejected
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (before after : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (atAfter : state.checkpoint = after.checkpoint)
    (changed : Fin pageCount) (conflictingRoot : Digest)
    (conflict : conflictingRoot ≠ after.pageRoots changed)
    (payload : Snapshot 4) :
    applyFinalizedDelta before after state
      ⟨before.checkpoint, after.checkpoint, changed,
        before.pageRoots changed, conflictingRoot, some payload⟩ =
      .rejected .duplicateConflict := by
  simp [applyFinalizedDelta, atAfter, conflict]

theorem finalized_delta_missing_page_rejected
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (before after : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (atBefore : state.checkpoint = before.checkpoint)
    (notAfter : state.checkpoint ≠ after.checkpoint)
    (notFork : ¬ before.checkpoint.IsFork after.checkpoint)
    (follows : before.checkpoint.Follows after.checkpoint)
    (complete : state.CompleteFor before)
    (changed : Fin pageCount) :
    applyFinalizedDelta before after state
      ⟨before.checkpoint, after.checkpoint, changed,
        before.pageRoots changed, after.pageRoots changed, none⟩ =
      .rejected .missingPage := by
  have beforeNeAfter : before.checkpoint ≠ after.checkpoint := by
    intro equal
    apply notAfter
    rw [atBefore, equal]
  have cache := complete_cache_exact before state complete
  simp [applyFinalizedDelta, atBefore, beforeNeAfter, notFork, follows,
    complete.2, cache.1, cache.2]

theorem finalized_delta_applies
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (before after : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (atBefore : state.checkpoint = before.checkpoint)
    (notAfter : state.checkpoint ≠ after.checkpoint)
    (notFork : ¬ before.checkpoint.IsFork after.checkpoint)
    (follows : before.checkpoint.Follows after.checkpoint)
    (complete : state.CompleteFor before)
    (changed : Fin pageCount) :
    applyFinalizedDelta before after state
      ⟨before.checkpoint, after.checkpoint, changed,
        before.pageRoots changed, after.pageRoots changed,
        some (after.pages changed)⟩ =
      .applied (state.installSuccessor after changed) := by
  have beforeNeAfter : before.checkpoint ≠ after.checkpoint := by
    intro equal
    apply notAfter
    rw [atBefore, equal]
  have cache := complete_cache_exact before state complete
  simp [applyFinalizedDelta, atBefore, beforeNeAfter, notFork, follows,
    complete.2, cache.1, cache.2, after.pageRootExact changed,
    CrawlState.installSuccessor]

theorem finalized_delta_retry_replayed
    {pageCount : Nat} {ExternallyFinal : FinalizedCheckpoint -> Prop}
    (before after : DeclaredDomain pageCount ExternallyFinal)
    (state : CrawlState pageCount) (changed : Fin pageCount) :
    let next := state.installSuccessor after changed
    applyFinalizedDelta before after next
      ⟨before.checkpoint, after.checkpoint, changed,
        before.pageRoots changed, after.pageRoots changed,
        some (after.pages changed)⟩ = .replayed next := by
  dsimp
  simp [applyFinalizedDelta, CrawlState.installSuccessor,
    after.pageRootExact changed]

/-! ## Closed non-vacuous one-page crawl -/

namespace Witness

def ExternalFinal (_ : FinalizedCheckpoint) : Prop := True

def historyDomain : Digest := ⟨9001⟩
def sourceDocument : DocumentId := ⟨⟨9002⟩⟩
def targetDocument : DocumentId := ⟨⟨9003⟩⟩
def linkId : LinkId := ⟨⟨9004⟩⟩
def operation : OperationId := ⟨⟨9005⟩⟩

def author : PrincipalRef where
  subject := ⟨9006⟩
  capabilityKind := .object
  capabilityId := ⟨9007⟩

def record : LinkRecord where
  sourceDocument := sourceDocument
  source := none
  target := .document targetDocument
  relation := ⟨9008⟩
  author := author
  operation := operation
  tombstonedAt := none

def entry : SourceEntry := ⟨linkId, record⟩

def pageCheckpoint : CausalCheckpoint where
  historyDomain := historyDomain
  document := sourceDocument
  head := none
  sequence := 1

def corpus : Corpus 4 := fun slot =>
  if slot = 0 then some entry else none

def page : Snapshot 4 where
  sourceCheckpoint := pageCheckpoint
  indexCheckpoint := pageCheckpoint
  corpus := corpus
  index := rebuild corpus
  cursor := ⟨pageCheckpoint, 4⟩

theorem page_fresh : page.Fresh := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def scheme : CommitmentScheme 1 where
  pageRoot snapshot := ⟨snapshot.sourceCheckpoint.sequence⟩
  manifestRoot roots := roots 0

def checkpoint : FinalizedCheckpoint where
  historyDomain := historyDomain
  epoch := 1
  finalizedThrough := 1
  parentManifestRoot := none
  manifestRoot := ⟨1⟩

def domain : DeclaredDomain 1 ExternalFinal where
  scheme := scheme
  checkpoint := checkpoint
  externallyFinal := trivial
  pages := fun _ => page
  pageRoots := fun _ => ⟨1⟩
  pageRootExact := by intro pageIndex; rfl
  manifestRootExact := rfl
  pageFresh := by intro pageIndex; exact page_fresh
  pageInFinalizedDomain := by intro pageIndex; exact ⟨rfl, Nat.le_refl 1⟩

def initial : CrawlState 1 := emptyState domain
def complete : CrawlState 1 := initial.install 0 page ⟨1⟩

def pageBinding : PagePairBinding scheme page page where
  eq_of_root_eq := fun _ => rfl

theorem initial_exact : initial.ExactPrefix domain := emptyState_exact domain

theorem complete_exact : complete.ExactPrefix domain := by
  exact install_preserves_exactPrefix domain initial initial_exact 0 rfl page
    pageBinding rfl

theorem complete_cursor : complete.nextPage = 1 := rfl

theorem complete_for_domain : complete.CompleteFor domain :=
  ⟨complete_exact, complete_cursor⟩

theorem source_at_zero : (domain.pages 0).corpus 0 = some entry := by
  simp [domain, page, corpus]

def row : IndexedRow where
  linkId := linkId
  sourceDocument := sourceDocument
  sourceRange := none
  target := .document targetDocument
  relation := ⟨9008⟩
  operation := operation

/-- The closed crawler actually returns one live backlink from its committed,
complete, finalized one-page domain. -/
theorem live_backlink_returned :
    ReturnedBacklink complete (.document targetDocument) row := by
  apply (returned_iff_declared domain complete complete_for_domain
    (.document targetDocument) row).2
  simpa [row, entry, record] using
    (live_source_is_declared domain 0 0 entry source_at_zero rfl)

end Witness

/-! ## Explicit trust and deployment ceiling -/

/-- Required before the exact finite result may be advertised as an unbounded,
available, cryptographically bound network service.  This module deliberately
constructs no inhabitant. -/
structure ExternalCompletion
    (GlobalUnboundedCoverage PhysicalAvailability NetworkLiveness
      CshakeCollisionResistance : Prop) : Prop where
  globalUnboundedCoverage : GlobalUnboundedCoverage
  physicalAvailability : PhysicalAvailability
  networkLiveness : NetworkLiveness
  cshakeCollisionResistance : CshakeCollisionResistance

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.HyperdocumentFinalizedDomainCrawler.returned_iff_declared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms returned_iff_declared
/-- info: 'Minidregg.Assurance.HyperdocumentFinalizedDomainCrawler.installSuccessor_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms installSuccessor_complete
/-- info: 'Minidregg.Assurance.HyperdocumentFinalizedDomainCrawler.finalized_fork_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finalized_fork_rejected

end

end Minidregg.Assurance.HyperdocumentFinalizedDomainCrawler
