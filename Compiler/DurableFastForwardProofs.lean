import Compiler.DurableFastForwardSpec

/-!
# The fast-forward open: proofs toward `Spec` (HOT-PATH §2(h))

The snapshot clause of `Spec.exact`, from the resume theorems the open already rests on.
-/

namespace Minidregg.Compiler.DurableFastForwardSpec

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DurableCheckpoint
open Minidregg.Compiler.DurableCheckpointCodec (MacKey)

set_option autoImplicit false

variable {rootBytes : List UInt8 → Digest}

/-- **The executed head state over the records is the resumed snapshot**: whatever height a
resume starts from (a checkpoint, or genesis), the snapshot it reaches is the snapshot of its own
head state (`State.ofSnapshot`, the executed part) over every record (journal, history and
consumed set from the records, the non-executing part). -/
theorem headState_snapshot {image : Image} {height : Nat} {state : State}
    {snapshot : DataSnapshot rootBytes} (resumed : resume rootBytes image height state = some snapshot) :
    (State.ofSnapshot image snapshot).snapshot rootBytes image.accepted = snapshot := by
  have rebased := DurableEngine.resume_rebase resumed
  unfold resume at rebased
  rw [if_pos (ofSnapshot_admissible _ _), List.drop_length, List.take_length] at rebased
  simpa [DurableReceiver.replay] using rebased

/-- **An honest checkpoint resumes to the genesis replay**: a checkpoint state whose snapshot over
the prefix is the replay of the prefix (`Body4.Honest.state`), admissible for the whole image,
resumes over the suffix to the replay of the whole log. -/
theorem resume_honest {seed : Seed} {pre suf : List IntentRecord} {state : State}
    (seedValid : (seed.cells.map Prod.fst).Nodup)
    (admissible : state.Admissible (Image.ofAccepted seed (pre ++ suf)))
    (honest : replaySnapshot rootBytes (Image.ofAccepted seed pre) = some (state.snapshot rootBytes pre)) :
    resume rootBytes (Image.ofAccepted seed (pre ++ suf)) pre.length state = replaySnapshot rootBytes (Image.ofAccepted seed (pre ++ suf)) := by
  have prefixReplay : replay rootBytes (seed.snapshot rootBytes) pre = some (state.snapshot rootBytes pre) := by
    unfold replaySnapshot at honest
    rw [resume_genesis] at honest
    unfold Image.restore at honest
    simpa [if_pos seedValid] using honest
  unfold replaySnapshot
  rw [resume_genesis]
  apply resume_sound rootBytes (Image.ofAccepted seed (pre ++ suf)) pre.length state (state.snapshot rootBytes pre) seedValid
    admissible
  · simpa [List.take_left'] using prefixReplay
  · simp

/-- **The fold splits at any height**: folding `pre ++ suf` from a World at `height` is folding
`pre`, then folding `suf` from the World reached at `height + pre.length`. This is what lets the open
fold only the suffix from a checkpoint's World. -/
theorem foldRecords_append (w : HostRefinesWorld.DWorld) (height : Nat) (pre suf : List IntentRecord) :
    DurableReceiverIO.foldRecords rootBytes w height (pre ++ suf) =
      (DurableReceiverIO.foldRecords rootBytes w height pre).bind fun w' =>
        DurableReceiverIO.foldRecords rootBytes w' (height + pre.length) suf := by
  induction pre generalizing w height with
  | nil => simp [DurableReceiverIO.foldRecords, Except.bind]
  | cons record rest ih =>
      simp only [List.cons_append, DurableReceiverIO.foldRecords, List.length_cons]
      split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · rw [ih]; simp [Nat.add_assoc, Nat.add_comm 1]

#assert_axioms foldRecords_append
/-- **The World clause of `exact`**: when a checkpoint's World is the genesis fold's World at the
prefix, the replay's World over the whole log is the fold of the suffix alone from it. -/
theorem worldAt_fastForward {seed : Seed} {pre suf : List IntentRecord}
    {genesis base : HostRefinesWorld.DWorld}
    (fromSeed : TurnLog.genesisOfSeed seed = .ok genesis)
    (atPrefix : DurableReceiverIO.foldRecords rootBytes genesis 0 pre = .ok base) :
    worldAt rootBytes (Image.ofAccepted seed (pre ++ suf)) =
      (DurableReceiverIO.foldRecords rootBytes base pre.length suf).toOption := by
  unfold worldAt
  simp only [Image.ofAccepted_seed, Image.accepted_ofAccepted, fromSeed, foldRecords_append, atPrefix, Nat.zero_add]
  rfl

#assert_axioms worldAt_fastForward
/-- **The semantics refusal, by name** (`Spec.macRefusals`, first half, for the deployed open): a
decodable checkpoint under this key whose body names another fold is `.foreignSemantics`, whatever
its root and MAC. -/
theorem openSealed_foreign_semantics (key : MacKey) (sealed : DurableCheckpointCodec.Sealed)
    (keyOk : sealed.body.keyId = key.id)
    (other : sealed.body.semantics ≠ DurableCheckpointCodec.foldSemantics) :
    DurableCheckpointCodec.openSealed key rootBytes (DurableCheckpointCodec.checkpointFrame.encode sealed) =
      .error .foreignSemantics := by
  unfold DurableCheckpointCodec.openSealed
  simp [DurableCheckpointCodec.Framed.decode_encode, keyOk, other]
  rfl

#assert_axioms openSealed_foreign_semantics
#assert_axioms headState_snapshot
#assert_axioms resume_honest

end Minidregg.Compiler.DurableFastForwardSpec

/-! ## The tags split at a checkpoint -/

namespace Minidregg.Compiler.DurableLogTags

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.DurableCheckpointCodec
open Minidregg.Compiler.DurableHistory (trailerCarried)

set_option autoImplicit false

section Generic

variable {D T : Type} [DecidableEq T]

/-- `firstBadTag` never reads the chain value before its first entry. -/
theorem firstBadTag_head (tag : Nat → D → T) (height : Nat) (first other : D) (chains : List D)
    (tags : List T) : firstBadTag tag height (first :: chains) tags = firstBadTag tag height (other :: chains) tags := by
  cases chains <;> cases tags <;> rfl

/-- **The first bad tag over a concatenation**: the first part's, else the second part's from the
height and chain value where the first part ends. -/
theorem firstBadTag_append (tag : Nat → D → T) :
    ∀ (height : Nat) (first : D) (xs ys : List D) (ts us : List T), xs.length = ts.length →
      firstBadTag tag height (first :: (xs ++ ys)) (ts ++ us) =
        match firstBadTag tag height (first :: xs) ts with
        | some bad => some bad
        | none => firstBadTag tag (height + ts.length) ((first :: xs).getLast (by simp) :: ys) us
  | height, first, [], ys, [], us, _ => by simp [firstBadTag]
  | height, first, [], ys, _ :: _, us, len => by simp at len
  | height, first, _ :: _, ys, [], us, len => by simp at len
  | height, first, x :: xs, ys, t :: ts, us, len => by
      have rest := firstBadTag_append tag (height + 1) x xs ys ts us (by simpa using len)
      simp only [List.cons_append, firstBadTag]
      split
      · rw [rest, List.getLast_cons_cons, List.length_cons,
          show height + (ts.length + 1) = height + 1 + ts.length by omega]
      · rfl

end Generic

theorem rootedChains_append (s : Digest) (restA restB : List Digest) (ta tb : List (List UInt8))
    (len : restA.length = ta.length) :
    rootedChains (s :: (restA ++ restB)) (ta ++ tb) =
      (s, defaultCarried) :: ((restA.zipWith (fun chain tag => (chain, (trailerCarried tag).getD defaultCarried)) ta) ++
        (restB.zipWith (fun chain tag => (chain, (trailerCarried tag).getD defaultCarried)) tb)) := by
  simp only [rootedChains, List.zipWith_append len]

/-- **The tags split at a checkpoint**: every tag verifies from the start chain IFF the tags below
the split verify from it and the tags after verify from the chain where the first part ends, at
its height.
(HOT-PATH §2(h): the open verifies the prefix's tags in its gate and the suffix's in its executing
part; `OwnEntries` verifies them all at once.) -/
theorem verifyTags_append (key : MacKey) (height : Nat) (start : Digest) (a b : List (List UInt8))
    (ta tb : List (List UInt8)) (len : ta.length = a.length) :
    verifyTags key height (chainPrefixesStored start (a ++ b)) (ta ++ tb) = .ok () ↔
      verifyTags key height (chainPrefixesStored start a) ta = .ok () ∧
      verifyTags key (height + a.length)
        (chainPrefixesStored ((chainPrefixesStored start a).getLastD start) b) tb = .ok () := by
  have okIff : ∀ height chains tags, verifyTags key height chains tags = .ok () ↔
      firstBadTag (rootedTag key) height (rootedChains chains tags) tags = none := by
    intro height chains tags
    unfold verifyTags verifyTagsWith
    split <;> simp_all
  have split : ∀ (start : Digest) (bytes : List (List UInt8)),
      bytes.scanl chainStepStored start = start :: (bytes.scanl chainStepStored start).tail ∧
        (bytes.scanl chainStepStored start).tail.length = bytes.length := by
    intro start bytes
    constructor
    · cases bytes <;> simp [List.scanl_cons, List.scanl_nil]
    · rw [List.length_tail, List.length_scanl]; simp
  obtain ⟨headA, lenA⟩ := split start a
  obtain ⟨headB, _⟩ := split (List.foldl chainStepStored start a) b
  have last : (chainPrefixesStored start a).getLastD start = List.foldl chainStepStored start a := by
    rw [List.getLastD_eq_getLast?]; unfold chainPrefixesStored; rw [List.getLast?_scanl]; rfl
  rw [okIff, okIff, okIff, last]
  unfold chainPrefixesStored
  rw [List.scanl_append, headA, headB, List.cons_append, List.tail_cons,
    rootedChains_append start _ _ ta tb (by rw [lenA, len])]
  rw [firstBadTag_append (rootedTag key) height _ _ _ ta tb (by simp [lenA, len])]
  simp only [rootedChains]
  cases found : firstBadTag (rootedTag key) height ((start, defaultCarried) :: List.zipWith
      (fun chain tag => (chain, (trailerCarried tag).getD defaultCarried))
      (List.scanl chainStepStored start a).tail ta) ta with
  | some bad => simp
  | none =>
      simp only [true_and]
      rw [firstBadTag_head (rootedTag key) _ _ (List.foldl chainStepStored start a, defaultCarried), len]

#assert_axioms firstBadTag_append
#assert_axioms verifyTags_append

end Minidregg.Compiler.DurableLogTags
