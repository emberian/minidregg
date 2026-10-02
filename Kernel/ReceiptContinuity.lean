/-
Client-retained receipt continuity, independently checked from public commitments.
A suffix contains only accepted-record digests, not commands or private payloads.
Its endpoints are opened through the system slot of the exact world roots the
client retained/read. This establishes append-only commitment relative to a
trusted first endpoint. It does not independently execute new records, establish
freshness against all witnesses, or survive loss of every retained client anchor.
-/
import Compiler.NativeHostCodec
import Theory.AssertAxioms

namespace Minidregg.Kernel.ReceiptContinuity

open Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.WorldRoot

set_option autoImplicit false

def algorithm : String := "minidregg-continuity-v1"
def maxSuffix : Nat := 4096

structure Identity where
  domain : Digest
  semantics : Digest
  expectedSeed : Digest
  deriving DecidableEq, Repr

structure Point where
  height : Nat
  worldRoot : Digest
  deriving DecidableEq, Repr

structure Query where
  identity : Identity
  /-- `none` is explicit authenticated-endpoint bootstrap, never continuity. -/
  anchor : Option Point
  target : Point
  deriving DecidableEq, Repr

structure Extension where
  identity : Identity
  startPoint : Point
  endPoint : Point
  startChain : Digest
  endChain : Digest
  fromSiblings : List Digest
  toSiblings : List Digest
  suffix : List Digest
  complete : Bool
  deriving DecidableEq, Repr

def Query.start (query : Query) : Point := query.anchor.getD query.target

def chainAfterDigests (start : Digest) (suffix : List Digest) : Digest :=
  suffix.foldl chainDigest start

/-- The public digest suffix is the same chain operation as durable replay. -/
theorem chainAfterDigests_records (start : Digest)
    (records : List DurableReceiver.IntentRecord) :
    chainAfterDigests start (records.map DurableCheckpointCodec.recordDigest) =
      DurableCheckpointCodec.chainAfter start records := by
  simp only [chainAfterDigests, DurableCheckpointCodec.chainAfter, List.foldl_map]
  rfl

/-- Membership (not absence) of the committed `(height, chain)` system slot.
An opening is bounded to exactly the deployed tree's 256 siblings. -/
def opens (point : Point) (chain : Digest) (siblings : List Digest) : Bool :=
  deployed.verify point.worldRoot .system
    (some (DurableCheckpointCodec.systemLeaf point.height chain)) ⟨none, siblings⟩

/-- Under the authenticated-map hash-separation carrier, an accepted opening
is the actual system slot of the world named by the receipt. This is the
cryptographic assumption; increasing heights are not a substitute for it. -/
theorem opens_sound (point : Point) (chain : Digest) (siblings : List Digest)
    (world : Minidregg.Theory.AuthMap.Map Key Digest)
    (root : point.worldRoot = deployed.root world)
    (binding : deployed.PathBinding world .system
      (some (DurableCheckpointCodec.systemLeaf point.height chain)) ⟨none, siblings⟩)
    (checked : opens point chain siblings = true) :
    some (DurableCheckpointCodec.systemLeaf point.height chain) =
      Minidregg.Theory.AuthMap.lookup deployed.ix world .system := by
  apply deployed.verify_sound world .system _ ⟨none, siblings⟩ binding
  simpa only [opens, root] using checked

/-- All client-verifiable continuity conditions. New roots cannot be accepted
merely because their heights increase, and a same-height fork is never an advance.
Historical queries orient their proof from the older receipt to the retained head. -/
def Valid (query : Query) (extension : Extension) : Prop :=
  extension.identity = query.identity ∧
  extension.startPoint = query.start ∧
  query.start.height ≤ query.target.height ∧
  extension.endPoint.height = min (query.start.height + maxSuffix) query.target.height ∧
  extension.suffix.length = extension.endPoint.height - extension.startPoint.height ∧
  extension.suffix.length ≤ maxSuffix ∧
  (extension.complete = decide (extension.endPoint.height = query.target.height)) ∧
  (extension.endPoint.height = query.target.height → extension.endPoint.worldRoot = query.target.worldRoot) ∧
  (extension.startPoint.height = extension.endPoint.height → extension.startPoint = extension.endPoint) ∧
  chainAfterDigests extension.startChain extension.suffix = extension.endChain ∧
  opens extension.startPoint extension.startChain extension.fromSiblings = true ∧
  opens extension.endPoint extension.endChain extension.toSiblings = true

instance (query : Query) (extension : Extension) : Decidable (Valid query extension) := by
  unfold Valid; infer_instance

def verify (query : Query) (extension : Extension) : Except String Point :=
  if Valid query extension then .ok extension.endPoint
  else .error "receipt continuity refused: identity, height, root, suffix or system opening differs"

theorem verify_ok_iff (query : Query) (extension : Extension) :
    verify query extension = .ok extension.endPoint ↔ Valid query extension := by
  simp [verify]

/-- Every accepted extension verifies openings against BOTH exact endpoints and
recomputes the durable chain. Neither endpoint chain is an unauthenticated claim. -/
theorem accepted_binds_chain (query : Query) (extension : Extension)
    (accepted : verify query extension = .ok extension.endPoint) :
    extension.startPoint = query.start ∧
      chainAfterDigests extension.startChain extension.suffix = extension.endChain ∧
      opens extension.startPoint extension.startChain extension.fromSiblings = true ∧
      opens extension.endPoint extension.endChain extension.toSiblings = true := by
  have valid := (verify_ok_iff query extension).mp accepted
  exact ⟨valid.2.1, valid.2.2.2.2.2.2.2.2.2.1,
    valid.2.2.2.2.2.2.2.2.2.2⟩

theorem lower_target_refused (query : Query) (extension : Extension)
    (lower : query.target.height < query.start.height) :
    verify query extension = .error
      "receipt continuity refused: identity, height, root, suffix or system opening differs" := by
  unfold verify
  rw [if_neg]
  intro valid
  have := valid.2.2.1
  omega

theorem same_height_conflict_refused (query : Query) (extension : Extension)
    (height : query.start.height = query.target.height)
    (conflict : query.start.worldRoot ≠ query.target.worldRoot) :
    verify query extension = .error
      "receipt continuity refused: identity, height, root, suffix or system opening differs" := by
  unfold verify
  rw [if_neg]
  intro valid
  have endpoint : extension.endPoint.height = query.target.height := by
    rw [valid.2.2.2.1, height]
    omega
  have same : extension.startPoint = extension.endPoint :=
    valid.2.2.2.2.2.2.2.2.1 (by rw [valid.2.1, height, endpoint])
  have target := valid.2.2.2.2.2.2.2.1 endpoint
  apply conflict
  rw [← valid.2.1, same, target]

#assert_axioms chainAfterDigests_records
#assert_axioms opens_sound
#assert_axioms verify_ok_iff
#assert_axioms accepted_binds_chain
#assert_axioms lower_target_refused
#assert_axioms same_height_conflict_refused

end Minidregg.Kernel.ReceiptContinuity
