module

public import Compiler.DurableIndex
public import Theory.Sp800185Cshake256Midstate
public import Std.Data.HashMap
public import Std.Data.HashSet

@[expose] public section

namespace Minidregg.Compiler.DurableIndex

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.AuthTrie (NodeIn Collision CollisionAmong TreeNode ClimbNode WF entries tree)
open Minidregg.Theory.KeyedModel (Model)

set_option autoImplicit false

/-! ## The first differing bit, in one pass -/

def firstDiffer (stop : Nat) : Nat → List Bool → List Bool → Nat
  | i, a :: as, b :: bs => if a = b then firstDiffer stop (i + 1) as bs else i
  | _, _, _ => stop

theorem firstDiffer_spec (n : Nat) (a b : List Bool) (la : a.length = n) (lb : b.length = n) :
    ∀ m d, d + m = n →
      ((List.range' d m).filter fun i => decide (a[i]? ≠ b[i]?)).head?.getD n =
        firstDiffer n d (a.drop d) (b.drop d) := by
  intro m
  induction m with
  | zero =>
      intro d total
      have : d = n := by omega
      subst this
      rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
      rfl
  | succ m ih =>
      intro d total
      have da : d < a.length := by omega
      have db : d < b.length := by omega
      rw [List.drop_eq_getElem_cons da, List.drop_eq_getElem_cons db, firstDiffer, List.range'_succ,
        List.filter_cons]
      by_cases same : a[d] = b[d]
      · rw [if_pos same, if_neg (by simp [List.getElem?_eq_getElem da, List.getElem?_eq_getElem db, same])]
        exact ih (d + 1) (by omega)
      · rw [if_neg same, if_pos (by simp [List.getElem?_eq_getElem da, List.getElem?_eq_getElem db, same])]
        rfl

theorem differ_eq (depth : Nat) (a b : List Bool) (la : a.length = 520) (lb : b.length = 520) :
    ((List.range 520).filter fun i => decide (i ≥ depth ∧ a[i]? ≠ b[i]?)).head?.getD 520 =
      firstDiffer 520 depth (a.drop depth) (b.drop depth) := by
  by_cases inside : depth ≤ 520
  · have parts : List.range 520 = List.range' 0 depth ++ List.range' depth (520 - depth) := by
      have joined := List.range'_append_1 (s := 0) (m := depth) (n := 520 - depth)
      rw [Nat.zero_add] at joined
      rw [List.range_eq_range', joined]
      congr 1
      omega
    rw [parts, List.filter_append]
    have none : ((List.range' 0 depth).filter fun i => decide (i ≥ depth ∧ a[i]? ≠ b[i]?)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro i member
      have := (List.mem_range'_1.mp member).2
      simp
      intro; omega
    have rest : ((List.range' depth (520 - depth)).filter fun i => decide (i ≥ depth ∧ a[i]? ≠ b[i]?)) =
        (List.range' depth (520 - depth)).filter fun i => decide (a[i]? ≠ b[i]?) := by
      apply List.filter_congr
      intro i member
      have := (List.mem_range'_1.mp member).1
      simp [this]
    rw [none, List.nil_append, rest]
    exact firstDiffer_spec 520 a b la lb (520 - depth) depth (by omega)
  · rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
    have none : ((List.range 520).filter fun i => decide (i ≥ depth ∧ a[i]? ≠ b[i]?)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro i member
      have := List.mem_range.mp member
      simp
      intro; omega
    rw [none]
    rfl

/-! ## One key: the bits once, the terminal's digest once, siblings read only under an empty subtree -/

def splitFast (depth : Nat) (k : IndexKey) (v : List UInt8) (other : IndexKey) (otherValue : List UInt8)
    (bits : List Bool) (theirs : Digest) : Sub × List (List Bool × Row) :=
  let otherBits := bitsOf other
  let differ := firstDiffer 520 depth (bits.drop depth) (otherBits.drop depth)
  let mine := dig (.leaf k v)
  let atDiffer : Row := if bits[differ]?.getD false then .branch theirs mine else .branch mine theirs
  split.up depth bits (differ - depth) atDiffer.digest
    [(bits.take differ, atDiffer), (bits.take (differ + 1), .leaf k v),
      (otherBits.take (differ + 1), .leaf other otherValue)]

theorem splitFast_eq (depth : Nat) (k : IndexKey) (v : List UInt8) (other : IndexKey) (otherValue : List UInt8) :
    splitFast depth k v other otherValue (bitsOf k) (dig (.leaf other otherValue)) =
      split depth k v other otherValue := by
  unfold split splitFast
  dsimp only
  rw [differ_eq depth _ _ (bitsOf_length k) (bitsOf_length other)]

def combineLazy (rows : List Bool → Option Row) (at_ : List Bool) (bit : Bool) (below : Sub)
    (sibling : Digest) : Sub × Option Row :=
  match below with
  | .empty => combine bit .empty (siblingSub rows at_ sibling)
  | .leaf k v =>
      if sibling = emptyDigest then (.leaf k v, some (.leaf k v)) else
      let row : Row := if bit then .branch sibling (dig (.leaf k v)) else .branch (dig (.leaf k v)) sibling
      (.node row.digest, some row)
  | .node d =>
      let row : Row := if bit then .branch sibling d else .branch d sibling
      (.node row.digest, some row)

theorem siblingSub_digest (rows : List Bool → Option Row) (at_ : List Bool) (sibling : Digest) :
    (siblingSub rows at_ sibling).digest = sibling := by
  unfold siblingSub
  split
  · next isEmpty => rw [isEmpty]; rfl
  · split
    · split
      · next same => exact same
      · rfl
    · rfl

theorem combineLazy_eq (rows : List Bool → Option Row) (at_ : List Bool) (bit : Bool) (below : Sub)
    (sibling : Digest) :
    combineLazy rows at_ bit below sibling = combine bit below (siblingSub rows at_ sibling) := by
  have digest := siblingSub_digest rows at_ sibling
  cases below with
  | empty => rfl
  | leaf k v =>
      simp only [combineLazy]
      by_cases isEmpty : sibling = emptyDigest
      · simp [isEmpty, siblingSub, combine]
      · rw [if_neg isEmpty]
        cases sub : siblingSub rows at_ sibling with
        | empty =>
            exfalso
            rw [sub] at digest
            exact isEmpty digest.symm
        | leaf k' v' => rw [sub] at digest; simp [combine, ← digest, Sub.digest]
        | node d => rw [sub] at digest; simp [combine, ← digest, Sub.digest]
  | node d =>
      simp only [combineLazy]
      cases sub : siblingSub rows at_ sibling with
      | empty => rw [sub] at digest; simp [combine, ← digest, Sub.digest]
      | leaf k' v' => rw [sub] at digest; simp [combine, ← digest, Sub.digest]
      | node d' => rw [sub] at digest; simp [combine, ← digest, Sub.digest]

def rebuildLazy (rows : List Bool → Option Row) (bits : List Bool) :
    List Digest → Nat → Sub → List (List Bool × Row) → Sub × List (List Bool × Row)
  | [], _, below, written => (below, written)
  | sibling :: rest, level, below, written =>
      let (under, done) := rebuildLazy rows bits rest (level + 1) below written
      let bit := bits[level]?.getD false
      let (here, row?) := combineLazy rows (bits.take level ++ [!bit]) bit under sibling
      (here, match row? with
        | some row => (bits.take level, row) :: done
        | none => done)

theorem rebuildLazy_eq (rows : List Bool → Option Row) (bits : List Bool) (siblings : List Digest)
    (level : Nat) (below : Sub) (written : List (List Bool × Row)) :
    rebuildLazy rows bits siblings level below written =
      rebuild bits (((List.range' level siblings.length).zip siblings).map fun (lv, sibling) =>
        siblingSub rows (bits.take lv ++ [!(bits[lv]?.getD false)]) sibling) level below written := by
  induction siblings generalizing level with
  | nil => rfl
  | cons sibling rest ih =>
      rw [rebuildLazy, ih, List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons, rebuild]
      simp only [combineLazy_eq]
      congr 1

def setCore (rows : List Bool → Option Row) (root : Digest) (k : IndexKey) (value : Option (List UInt8))
    (bits : List Bool) (opening : Opening) (terminalDigest : Digest) :
    Except String (Digest × List (List Bool × Row)) :=
  let depth := opening.siblings.length
  let bottom : Option (Sub × List (List Bool × Row)) :=
    match opening.terminal, value with
    | .empty, none => none
    | .empty, some v => some (.leaf k v, [(bits.take depth, .leaf k v)])
    | .leaf other _, none =>
        if other = k then some (.empty, []) else none
    | .leaf other otherValue, some v =>
        if other = k then
          if otherValue = v then none else some (.leaf k v, [(bits.take depth, .leaf k v)])
        else some (splitFast depth k v other otherValue bits terminalDigest)
  match bottom with
  | none => .ok (root, [])
  | some (sub, written) =>
      let (top, rowsWritten) := rebuildLazy rows bits opening.siblings 0 sub written
      .ok (top.digest, rowsWritten)

def setFast (rows : List Bool → Option Row) (root : Digest) (k : IndexKey) (value : Option (List UInt8)) :
    Except String (Digest × List (List Bool × Row)) :=
  let bits := bitsOf k
  let opening := walk rows bits 521 [] root []
  let terminalDigest := dig opening.terminal.input
  if verifyBits root k bits (opening.claims k) opening terminalDigest = true then
    setCore rows root k value bits opening terminalDigest
  else .error "index opening does not reach the authenticated index root"

theorem setCore_eq (rows : List Bool → Option Row) (root : Digest) (k : IndexKey) (value : Option (List UInt8))
    (ok : verify root k ((openingOf rows root k).claims k) (openingOf rows root k) = true) :
    set rows root k value =
      setCore rows root k value (bitsOf k) (openingOf rows root k) (dig (openingOf rows root k).terminal.input) := by
  unfold set setCore
  simp only [ok, if_true, rebuildLazy_eq, List.range_eq_range']
  clear ok
  generalize openingOf rows root k = opening
  obtain ⟨siblings, terminal⟩ := opening
  cases terminal with
  | empty => cases value <;> rfl
  | leaf other otherValue =>
      cases value with
      | none => rfl
      | some v =>
          simp only [Theory.AuthTrie.Terminal.input, splitFast_eq]
          rfl

@[csimp] theorem set_eq_fast : @set = @setFast := by
  funext rows root k value
  unfold setFast
  simp only [verifyBits_eq]
  by_cases ok : verify root k ((openingOf rows root k).claims k) (openingOf rows root k) = true
  · rw [setCore_eq rows root k value ok]
    simp only [openingOf] at ok ⊢
    rw [if_pos ok]
  · have refused : set rows root k value = .error "index opening does not reach the authenticated index root" := by
      unfold set
      simp only [ok]
      rfl
    rw [refused]
    simp only [openingOf] at ok
    rw [if_neg ok]

/-! ## A record's keys: the rows written so far in one map, each prefix written once -/

abbrev Held := Std.HashMap (List Bool) Row
abbrev Seen := Std.HashSet (List Bool)

def layered (store : List Bool → Option Row) (held : Held) : List Bool → Option Row :=
  fun p => match held[p]? with
    | some row => some row
    | none => store p

def hold (held : Held) (rows : List (List Bool × Row)) : Held :=
  rows.foldr (fun row acc => acc.insert row.1 row.2) held

def see (seen : Seen) (rows : List (List Bool × Row)) : Seen :=
  rows.foldl (fun acc row => acc.insert row.1) seen

theorem layered_empty (store : List Bool → Option Row) : layered store (∅ : Held) = store := by
  funext p
  simp [layered]

theorem layered_hold (store : List Bool → Option Row) (held : Held) (rows : List (List Bool × Row)) :
    layered store (hold held rows) = overlay (layered store held) rows := by
  funext p
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      unfold layered overlay at ih ⊢
      rw [hold, List.foldr_cons, Std.HashMap.getElem?_insert, List.find?_cons]
      by_cases same : row.1 = p
      · simp [same]
      · simp only [beq_iff_eq, same, if_false, decide_false]
        exact ih

theorem see_contains (seen : Seen) (rows : List (List Bool × Row)) (p : List Bool) :
    (see seen rows).contains p = (seen.contains p || rows.any fun row => decide (row.1 = p)) := by
  induction rows generalizing seen with
  | nil => simp [see]
  | cons row rest ih =>
      rw [see, List.foldl_cons]
      have step := ih (seen.insert row.1)
      rw [see] at step
      rw [step, Std.HashSet.contains_insert, List.any_cons]
      by_cases same : row.1 = p
      · simp [same]
      · rw [beq_eq_false_iff_ne.mpr same, decide_eq_false same, Bool.false_or, Bool.false_or]

def Step (α : Type) := (List Bool → Option Row) → Digest → α → Except String (Digest × List (List Bool × Row))

def foldSpec {α : Type} (step : Step α) : (List Bool → Option Row) → Digest → List α →
    Except String (Digest × List (List Bool × Row))
  | _, root, [] => .ok (root, [])
  | store, root, item :: rest =>
      match step store root item with
      | .error message => .error message
      | .ok (root', rows) =>
          match foldSpec step (overlay store rows) root' rest with
          | .error message => .error message
          | .ok (finalRoot, later) =>
              .ok (finalRoot, later ++ rows.filter fun row => !later.any (·.1 = row.1))

def foldMap {α : Type} (step : Step α) (store : List Bool → Option Row) : Held → Digest → List α →
    Except String (Digest × List (List Bool × Row) × Seen)
  | _, root, [] => .ok (root, [], ∅)
  | held, root, item :: rest =>
      match step (layered store held) root item with
      | .error message => .error message
      | .ok (root', rows) =>
          match foldMap step store (hold held rows) root' rest with
          | .error message => .error message
          | .ok (finalRoot, later, seen) =>
              .ok (finalRoot, later ++ rows.filter (fun row => !seen.contains row.1), see seen rows)

def Agrees (slow : Except String (Digest × List (List Bool × Row)))
    (fast : Except String (Digest × List (List Bool × Row) × Seen)) : Prop :=
  match slow, fast with
  | .ok (root, rows), .ok (root', rows', seen) =>
      root = root' ∧ rows = rows' ∧ ∀ p, seen.contains p = rows.any fun row => decide (row.1 = p)
  | .error a, .error b => a = b
  | _, _ => False

theorem foldMap_agrees {α : Type} (step : Step α) (store : List Bool → Option Row) (held : Held) (root : Digest)
    (items : List α) :
    Agrees (foldSpec step (layered store held) root items) (foldMap step store held root items) := by
  induction items generalizing held root with
  | nil => exact ⟨rfl, rfl, fun p => by simp⟩
  | cons item rest ih =>
      rw [foldSpec, foldMap]
      cases stepped : step (layered store held) root item with
      | error message => rfl
      | ok pair =>
          obtain ⟨root', rows⟩ := pair
          have below := ih (hold held rows) root'
          rw [layered_hold] at below
          simp only
          cases slow : foldSpec step (overlay (layered store held) rows) root' rest with
          | error message =>
              cases fast : foldMap step store (hold held rows) root' rest with
              | error message' =>
                  rw [slow, fast] at below
                  exact below
              | ok triple => rw [slow, fast] at below; exact below.elim
          | ok pair' =>
              obtain ⟨finalRoot, later⟩ := pair'
              cases fast : foldMap step store (hold held rows) root' rest with
              | error message' => rw [slow, fast] at below; exact below.elim
              | ok triple =>
                  obtain ⟨finalRoot', later', seen⟩ := triple
                  rw [slow, fast] at below
                  obtain ⟨sameRoot, sameRows, inv⟩ := below
                  subst sameRoot
                  subst sameRows
                  have filtered : (rows.filter fun row => !later.any (·.1 = row.1)) =
                      rows.filter fun row => !seen.contains row.1 := by
                    apply List.filter_congr
                    intro row _
                    rw [inv]
                  refine ⟨rfl, by rw [filtered], fun p => ?_⟩
                  rw [see_contains, filtered, List.any_append, List.any_filter, inv]
                  by_cases known : (later.any fun row => decide (row.1 = p)) = true
                  · simp [known]
                  · have known := Bool.eq_false_iff.mpr known
                    have unseen : seen.contains p = false := by rw [inv]; exact known
                    rw [known, Bool.false_or, Bool.false_or]
                    apply List.any_congr rfl
                    intro row
                    by_cases same : row.1 = p
                    · rw [same, unseen]; rfl
                    · rw [decide_eq_false same, Bool.and_false]

def project (fast : Except String (Digest × List (List Bool × Row) × Seen)) :
    Except String (Digest × List (List Bool × Row)) :=
  match fast with
  | .ok (root, rows, _) => .ok (root, rows)
  | .error message => .error message

theorem Agrees.project_eq {slow : Except String (Digest × List (List Bool × Row))}
    {fast : Except String (Digest × List (List Bool × Row) × Seen)} (agrees : Agrees slow fast) :
    slow = project fast := by
  cases slow with
  | error a =>
      cases fast with
      | error b => exact congrArg Except.error agrees
      | ok triple => exact agrees.elim
  | ok pair =>
      cases fast with
      | error b => exact agrees.elim
      | ok triple =>
          obtain ⟨root, rows⟩ := pair
          obtain ⟨root', rows', seen⟩ := triple
          obtain ⟨sameRoot, sameRows, _⟩ := agrees
          rw [sameRoot, sameRows]
          rfl

def setStep : Step (IndexKey × Option (List UInt8)) := fun rows root change => set rows root change.1 change.2

theorem setAll_eq_foldSpec (store : List Bool → Option Row) (root : Digest)
    (changes : List (IndexKey × Option (List UInt8))) :
    setAll store root changes = foldSpec setStep store root changes := by
  induction changes generalizing store root with
  | nil => rfl
  | cons change rest ih =>
      obtain ⟨k, value⟩ := change
      rw [setAll, foldSpec]
      simp only [setStep]
      cases set store root k value with
      | error message => rfl
      | ok pair =>
          obtain ⟨root', rows⟩ := pair
          simp only [bind, Except.bind]
          rw [ih]
          cases foldSpec setStep (overlay store rows) root' rest with
          | error message => rfl
          | ok pair' => rfl

def setAllFast (store : List Bool → Option Row) (root : Digest)
    (changes : List (IndexKey × Option (List UInt8))) : Except String (Digest × List (List Bool × Row)) :=
  project (foldMap setStep store ∅ root changes)

@[csimp] theorem setAll_eq_fast : @setAll = @setAllFast := by
  funext store root changes
  have agrees := foldMap_agrees setStep store ∅ root changes
  rw [layered_empty] at agrees
  rw [setAll_eq_foldSpec]
  exact agrees.project_eq

namespace IndexRows

open Kernel.DurableDataIntent

def insertStep (height : Nat) : Step IndexKey := fun rows root k =>
  let bits := bitsOf k
  let opening := walk rows bits 521 [] root []
  let terminalDigest := dig opening.terminal.input
  if verifyBits root k bits (opening.claims k) opening terminalDigest = true then
    if (opening.claims k).isSome then
      .error "the index already holds a key this record inserts (it disagrees with the executor)"
    else setCore rows root k (some (heightValue height)) bits opening terminalDigest
  else .error "index opening does not reach the authenticated index root"

def insertStepSpec (height : Nat) : Step IndexKey := fun rows root k =>
  match lookupRows rows root k with
  | .error message => .error message
  | .ok answer =>
      if answer.value.isSome then
        .error "the index already holds a key this record inserts (it disagrees with the executor)"
      else set rows root k (some (heightValue height))

theorem insertStep_eq (height : Nat) : insertStepSpec height = insertStep height := by
  funext rows root k
  unfold insertStepSpec insertStep lookupRows
  have opened : walk rows (bitsOf k) 521 [] root [] = openingOf rows root k := rfl
  simp only [opened, verifyBits_eq]
  by_cases ok : verify root k ((openingOf rows root k).claims k) (openingOf rows root k) = true
  · rw [setCore_eq rows root k _ ok, dif_pos ok, if_pos ok]
  · rw [dif_neg ok, if_neg ok]

theorem insert_eq_foldSpec (height : Nat) (store : List Bool → Option Row) (root : Digest)
    (ks : List IndexKey) :
    insert height store root ks = foldSpec (insertStepSpec height) store root ks := by
  induction ks generalizing store root with
  | nil => rfl
  | cons k rest ih =>
      rw [insert, foldSpec]
      simp only [insertStepSpec]
      cases lookupRows store root k with
      | error message => rfl
      | ok answer =>
          simp only [bind, Except.bind]
          cases present : answer.value.isSome with
          | true => rfl
          | false =>
            simp only [Bool.false_eq_true, if_false]
            cases set store root k (some (heightValue height)) with
            | error message => rfl
            | ok pair =>
                obtain ⟨root', rows⟩ := pair
                simp only [ih]
                cases foldSpec (insertStepSpec height) (overlay store rows) root' rest with
                | error message => rfl
                | ok pair' => rfl

def insertFast (height : Nat) (store : List Bool → Option Row) (root : Digest) (ks : List IndexKey) :
    Except String (Digest × List (List Bool × Row)) :=
  project (foldMap (insertStep height) store ∅ root ks)

@[csimp] theorem insert_eq_fast : @insert = @insertFast := by
  funext height store root ks
  have agrees := foldMap_agrees (insertStepSpec height) store ∅ root ks
  rw [layered_empty] at agrees
  rw [insert_eq_foldSpec, insertFast, ← insertStep_eq]
  exact agrees.project_eq

def applyFast (store : List Bool → Option Row) (root : Digest) (height : Nat)
    (transactionId : TransactionId) (nullifiers : List StableNullifier)
    (cells : List Kernel.DurableDataIntent.CellId) (seqs : List Digest256) :
    Except String (Digest × List (List Bool × Row)) :=
  match foldMap (insertStep height) store ∅ root (keys transactionId nullifiers) with
  | .error message => .error message
  | .ok (inserted, early, _) =>
      let held := hold ∅ early
      match foldMap setStep store held inserted (cellChanges height cells) with
      | .error message => .error message
      | .ok (middle, mid, seenMid) =>
          let held' := hold held mid
          match seqCounts (layered store held') middle (Theory.JournalSequences.distinct seqs) with
          | .error message => .error message
          | .ok counts =>
              match foldMap setStep store held' middle (seqChanges height counts) with
              | .error message => .error message
              | .ok (final, late, seenLate) =>
                  .ok (final, late ++ (mid ++ early.filter fun row => !seenMid.contains row.1).filter
                    fun row => !seenLate.contains row.1)

@[csimp] theorem apply_eq_fast : @apply = @applyFast := by
  funext store root height transactionId nullifiers cells seqs
  unfold apply applyFast
  have first := foldMap_agrees (insertStepSpec height) store ∅ root (keys transactionId nullifiers)
  rw [layered_empty, ← insert_eq_foldSpec, insertStep_eq] at first
  cases slow : insert height store root (keys transactionId nullifiers) with
  | error message =>
      cases fast : foldMap (insertStep height) store ∅ root (keys transactionId nullifiers) with
      | error message' => rw [slow, fast] at first; exact congrArg Except.error first
      | ok triple => rw [slow, fast] at first; exact first.elim
  | ok pair =>
      obtain ⟨inserted, early⟩ := pair
      cases fast : foldMap (insertStep height) store ∅ root (keys transactionId nullifiers) with
      | error message' => rw [slow, fast] at first; exact first.elim
      | ok triple =>
          obtain ⟨inserted', early', seenEarly⟩ := triple
          rw [slow, fast] at first
          obtain ⟨sameRoot, sameRows, _⟩ := first
          subst sameRoot
          subst sameRows
          simp only [bind, Except.bind]
          have second := foldMap_agrees setStep store (hold ∅ early) inserted (cellChanges height cells)
          rw [layered_hold, layered_empty, ← setAll_eq_foldSpec] at second
          cases slow2 : setAll (overlay store early) inserted (cellChanges height cells) with
          | error message =>
              cases fast2 : foldMap setStep store (hold ∅ early) inserted (cellChanges height cells) with
              | error message' => rw [slow2, fast2] at second; exact congrArg Except.error second
              | ok triple => rw [slow2, fast2] at second; exact second.elim
          | ok pair2 =>
              obtain ⟨middle, mid⟩ := pair2
              cases fast2 : foldMap setStep store (hold ∅ early) inserted (cellChanges height cells) with
              | error message' => rw [slow2, fast2] at second; exact second.elim
              | ok triple2 =>
                  obtain ⟨middle', mid', seenMid⟩ := triple2
                  rw [slow2, fast2] at second
                  obtain ⟨sameRoot, sameRows, invMid⟩ := second
                  subst sameRoot
                  subst sameRows
                  simp only
                  have stores : layered store (hold (hold ∅ early) mid) = overlay (overlay store early) mid := by
                    rw [layered_hold, layered_hold, layered_empty]
                  rw [stores]
                  cases seqCounts (overlay (overlay store early) mid) middle
                      (Theory.JournalSequences.distinct seqs) with
                  | error message => rfl
                  | ok counts =>
                      simp only
                      have third := foldMap_agrees setStep store (hold (hold ∅ early) mid) middle
                        (seqChanges height counts)
                      rw [stores, ← setAll_eq_foldSpec] at third
                      cases slow3 : setAll (overlay (overlay store early) mid) middle (seqChanges height counts) with
                      | error message =>
                          cases fast3 : foldMap setStep store (hold (hold ∅ early) mid) middle
                              (seqChanges height counts) with
                          | error message' => rw [slow3, fast3] at third; exact congrArg Except.error third
                          | ok triple => rw [slow3, fast3] at third; exact third.elim
                      | ok pair3 =>
                          obtain ⟨final, late⟩ := pair3
                          cases fast3 : foldMap setStep store (hold (hold ∅ early) mid) middle
                              (seqChanges height counts) with
                          | error message' => rw [slow3, fast3] at third; exact third.elim
                          | ok triple3 =>
                              obtain ⟨final', late', seenLate⟩ := triple3
                              rw [slow3, fast3] at third
                              obtain ⟨sameRoot, sameRows, invLate⟩ := third
                              subst sameRoot
                              subst sameRows
                              simp only [pure, Except.pure]
                              have inner : (early.filter fun row => !mid.any (·.1 = row.1)) =
                                  early.filter fun row => !seenMid.contains row.1 := by
                                apply List.filter_congr
                                intro row _
                                rw [invMid]
                              have outer : ∀ rows : List (List Bool × Row),
                                  (rows.filter fun row => !late.any (·.1 = row.1)) =
                                    rows.filter fun row => !seenLate.contains row.1 := by
                                intro rows
                                apply List.filter_congr
                                intro row _
                                rw [invLate]
                              rw [inner, outer]

end IndexRows

end Minidregg.Compiler.DurableIndex
