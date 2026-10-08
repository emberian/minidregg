/-
# Kernel.ContentRunEdit — `insertRun` refines `Theory.StableRanges.Edit.insert` (K-RUNS-RANGES)

`ContentResource.Action.insertRun` puts existing atoms of a document into the
committed slot order of one existing run, at the cut a stable point names (or at
the end).  A transclusion range lives in one run, so this is what lets a line
appended after the run was made be named by a range.

The specification is `Theory.StableRanges`: `Edit.insert` moves no endpoint
(`transportEndpoint`, `RangeTrace.step_insert_current`) and only the exact order
changes.  What is proved here:

* `insertRun_order` — the splice cut is the Theory's own `cut?` of the anchor's
  decoded endpoint over the run's slot locations (`none`: the end), and the new
  run order is that splice;
* `insertRun_live_order` — over the live order the Theory projects against, the
  edit is a splice of the inserted live atoms;
* `resolveRange_refines_projectRange` — the kernel's `resolveRange`, read live,
  is exactly the Theory's `projectRange` of the same range over the live order,
  for a range whose endpoints are live atoms of the run;
* `insertRun_transports_range` — after an accepted `insertRun`, the kernel's
  reading of an unchanged stored range is the Theory's projection of the range
  *transported through* `Edit.insert` over the post-edit live order;
* `insertRun_preserves_point` — every stored point of the document still names
  its slot, so ranges stored in links, marks and other cells stay valid;
* `insertRun_frame` — the edit writes the run record and nothing else.

Not covered, by design of the kernel's read-time resolution: an endpoint whose
atom is dead under a `prefer*` policy is resolved on the committed run order at
read time, not at death time as `DeathContext` has it, so an insertion can
change what such an endpoint resolves to (`01a0f611-ea87`).
-/
import Kernel.ContentResource
import Kernel.ContentResourceAudit
import Theory.StableRanges
import Theory.AssertAxioms

namespace Minidregg.Kernel.ContentResource

open Minidregg.Theory
open Minidregg.Theory.Hyperdocument

set_option autoImplicit false

abbrev RunLocation := StableRanges.Location RunId AtomId

/-! ## The abstraction: a run as the Theory's locations -/

/-- The run's committed slot order, as locations. -/
def slotLocations (runId : RunId) (run : RunRecord) : List RunLocation :=
  run.atoms.map fun atom => ⟨runId, atom⟩

/-- The run's live order: the "exact current order" the Theory projects against. -/
def liveOrder (store : ContentStore) (document : DocumentId) (runId : RunId) (run : RunRecord) :
    List RunLocation :=
  (run.atoms.filter (slotLive store document)).map fun atom => ⟨runId, atom⟩

/-- The kernel's range reading, over live atoms only. -/
def liveSlots (store : ContentStore) (document : DocumentId) (range : Hyperdocument.StableRange) :
    Option (List AtomId) :=
  match resolveRange store document range with
  | .slots atoms => some (atoms.filter (slotLive store document))
  | _ => none

/-! ## List lemmas -/

theorem position_map (runId : RunId) (target : AtomId) (atoms : List AtomId) :
    StableRanges.position? (⟨runId, target⟩ : RunLocation)
      (atoms.map fun atom => (⟨runId, atom⟩ : RunLocation)) = atoms.findIdx? (· == target) := by
  induction atoms with
  | nil => rfl
  | cons head rest ih =>
      by_cases same : head = target
      · subst same; simp [StableRanges.position?, List.findIdx?_cons]
      · have : ¬ ((⟨runId, head⟩ : RunLocation) = ⟨runId, target⟩) := by
          intro eq; cases eq; exact same rfl
        simp [StableRanges.position?, List.findIdx?_cons, this, same, ih]

theorem filter_findIdx {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) (target : α) :
    ∀ (l : List α) (i : Nat), l.findIdx? (· == target) = some i → p target = true →
      (l.filter p).findIdx? (· == target) = some ((l.take i).filter p).length
  | [], i, h, _ => by simp [List.findIdx?_nil] at h
  | head :: rest, i, h, live => by
      by_cases same : head = target
      · subst same
        simp [List.findIdx?_cons] at h
        subst h
        simp [live, List.findIdx?_cons]
      · simp [List.findIdx?_cons, same] at h
        obtain ⟨j, hj, rfl⟩ := h
        have ih := filter_findIdx p target rest j hj live
        by_cases ph : p head = true
        · simp [ph, List.findIdx?_cons, same, ih]
        · simp [ph, ih]

theorem filter_slice {α : Type} (p : α → Bool) (l : List α) (s u : Nat) :
    ((l.drop s).take u).filter p =
      (((l.filter p).drop ((l.take s).filter p).length).take
        (((l.take (s + u)).filter p).length - ((l.take s).filter p).length)) := by
  have split : l.take (s + u) = l.take s ++ (l.drop s).take u := List.take_add (l := l) (i := s) (j := u)
  have whole : l.filter p = (l.take s).filter p ++ (l.drop s).filter p := by
    conv_lhs => rw [← List.take_append_drop s l]
    rw [List.filter_append]
  have rest : (l.drop s).filter p =
      ((l.drop s).take u).filter p ++ ((l.drop s).drop u).filter p := by
    conv_lhs => rw [← List.take_append_drop u (l.drop s)]
    rw [List.filter_append]
  rw [split, List.filter_append, whole, rest]
  simp only [List.length_append, Nat.add_sub_cancel_left]
  rw [List.drop_left' rfl, List.take_left' rfl]


theorem count_cut {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) (target : α) (l : List α) (i : Nat)
    (found : l.findIdx? (· == target) = some i) (live : p target = true) (bias : AnchorBias) :
    ((l.take (cutAt bias i)).filter p).length =
      ((l.take i).filter p).length + (match bias with | .before => 0 | .after => 1) := by
  cases bias
  · rfl
  · obtain ⟨bound, hit, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
    have atTarget : l[i] = target := by simpa using hit
    show ((l.take (i + 1)).filter p).length = _
    rw [List.take_add_one, List.getElem?_eq_getElem bound, atTarget]
    simp [List.filter_append, live]

theorem resolvePoint_live (order : List AtomId) (alive : List Bool) (point : StablePoint)
    (atom : AtomId) (i : Nat) (neighbor : point.neighbor = some atom)
    (found : order.findIdx? (· == atom) = some i) (live : alive.getD i false = true) :
    resolvePoint order alive point = .cut (cutAt point.bias i) := by
  have alive' : alive[i]?.getD false = true := by simpa [List.getD_eq_getElem?_getD] using live
  simp [resolvePoint, neighbor, found, alive']

theorem slotLive_getD (store : ContentStore) (document : DocumentId) (atoms : List AtomId)
    (atom : AtomId) (i : Nat) (found : atoms.findIdx? (· == atom) = some i)
    (live : slotLive store document atom = true) :
    (atoms.map (slotLive store document)).getD i false = true := by
  obtain ⟨bound, hit, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
  have atTarget : atoms[i] = atom := by simpa using hit
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound, atTarget, live]

theorem resolveRange_refines_projectRange
    (store : ContentStore) (document : DocumentId) (runId : RunId) (run : RunRecord)
    (found : Hyperdocument.lookup store .runs runId = some run) (owned : run.document = document)
    (a b : AtomId) (bs bf : AnchorBias) (ds df : EndpointDeathPolicy) (i j : Nat)
    (atA : run.atoms.findIdx? (· == a) = some i) (atB : run.atoms.findIdx? (· == b) = some j)
    (liveA : slotLive store document a = true) (liveB : slotLive store document b = true)
    (ordered : cutAt bs i ≤ cutAt bf j)
    (range : StableRanges.StableRange RunId AtomId)
    (decoded : StableRanges.HyperdocumentAdapter.decodeRange?
      ⟨⟨runId, some a, bs, ds⟩, ⟨runId, some b, bf, df⟩⟩ = some range) :
    liveSlots store document ⟨⟨runId, some a, bs, ds⟩, ⟨runId, some b, bf, df⟩⟩ =
      (StableRanges.projectRange (liveOrder store document runId run)
          (StableRanges.RangeTrace.init range)).map fun projected => projected.atoms.map (·.atom) := by
  have decodedExact : StableRanges.HyperdocumentAdapter.decodeRange?
      ⟨⟨runId, some a, bs, ds⟩, ⟨runId, some b, bf, df⟩⟩ =
      some ⟨⟨⟨runId, a⟩, StableRanges.HyperdocumentAdapter.sideOfBias bs, ds⟩,
        ⟨⟨runId, b⟩, StableRanges.HyperdocumentAdapter.sideOfBias bf, df⟩⟩ := rfl
  rw [decodedExact] at decoded
  cases decoded
  have startPoint := resolvePoint_live run.atoms (run.atoms.map (slotLive store document))
    ⟨runId, some a, bs, ds⟩ a i rfl atA (slotLive_getD store document _ a i atA liveA)
  have stopPoint := resolvePoint_live run.atoms (run.atoms.map (slotLive store document))
    ⟨runId, some b, bf, df⟩ b j rfl atB (slotLive_getD store document _ b j atB liveB)
  have kernel : liveSlots store document ⟨⟨runId, some a, bs, ds⟩, ⟨runId, some b, bf, df⟩⟩ =
      some (((run.atoms.drop (cutAt bs i)).take (cutAt bf j - cutAt bs i)).filter
        (slotLive store document)) := by
    simp only [liveSlots, resolveRange, found, owned, startPoint, stopPoint]
    simp [ordered]
  rw [kernel]
  have countA := count_cut (slotLive store document) a run.atoms i atA liveA bs
  have countB := count_cut (slotLive store document) b run.atoms j atB liveB bf
  have positionA : StableRanges.position? (⟨runId, a⟩ : RunLocation) (liveOrder store document runId run) =
      some ((run.atoms.take i).filter (slotLive store document)).length := by
    unfold liveOrder
    rw [position_map, filter_findIdx (slotLive store document) a run.atoms i atA liveA]
  have positionB : StableRanges.position? (⟨runId, b⟩ : RunLocation) (liveOrder store document runId run) =
      some ((run.atoms.take j).filter (slotLive store document)).length := by
    unfold liveOrder
    rw [position_map, filter_findIdx (slotLive store document) b run.atoms j atB liveB]
  have slice := filter_slice (slotLive store document) run.atoms (cutAt bs i) (cutAt bf j - cutAt bs i)
  rw [Nat.add_sub_cancel' ordered] at slice
  have hle : ((run.atoms.take (cutAt bs i)).filter (slotLive store document)).length ≤
      ((run.atoms.take (cutAt bf j)).filter (slotLive store document)).length := by
    obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le ordered
    rw [hu, List.take_add, List.filter_append, List.length_append]
    omega
  have startCut : StableRanges.cut? (liveOrder store document runId run)
      ⟨⟨runId, a⟩, StableRanges.HyperdocumentAdapter.sideOfBias bs, ds⟩ =
      some ((run.atoms.take (cutAt bs i)).filter (slotLive store document)).length := by
    unfold StableRanges.cut?
    rw [positionA, countA]
    cases bs <;> rfl
  have stopCut : StableRanges.cut? (liveOrder store document runId run)
      ⟨⟨runId, b⟩, StableRanges.HyperdocumentAdapter.sideOfBias bf, df⟩ =
      some ((run.atoms.take (cutAt bf j)).filter (slotLive store document)).length := by
    unfold StableRanges.cut?
    rw [positionB, countB]
    cases bf <;> rfl
  simp only [StableRanges.projectRange, StableRanges.RangeTrace.init, StableRanges.EndpointTrace.init,
    StableRanges.EndpointTransport.current?, startCut, stopCut, if_pos hle, Option.map_some]
  congr 1
  rw [slice]
  unfold liveOrder
  simp [List.map_drop, List.map_take, Function.comp_def]


/-! ## The edit, against the Theory -/

theorem insertRun_frame {document : DocumentId} {progress next : Progress} {runId : RunId}
    {anchor : Option StablePoint} {atoms : List AtomId}
    (accepted : insertRunStep document progress runId anchor atoms = .ok next) :
    ∀ address : Hyperdocument.Address, address.1 ≠ .runs → next.1 address = progress.1 address := by
  obtain ⟨before, cut, _, _, _, _, _, rfl⟩ := insertRunStep_ok accepted
  intro address other
  exact Store.Store.set_ne _ _ _ address (fun same => other (congrArg Sigma.fst same))

theorem insertRun_slotLive {document : DocumentId} {progress next : Progress} {runId : RunId}
    {anchor : Option StablePoint} {atoms : List AtomId}
    (accepted : insertRunStep document progress runId anchor atoms = .ok next) (atom : AtomId) :
    slotLive next.1 document atom = slotLive progress.1 document atom := by
  have same := insertRun_frame accepted ⟨.atoms, atom⟩ (by simp)
  unfold slotLive Hyperdocument.lookup
  rw [same]

theorem insertRun_into_empty_refused {document : DocumentId} {progress : Progress} {runId : RunId}
    {anchor : Option StablePoint} {atoms : List AtomId} {before : RunRecord}
    (found : Hyperdocument.lookup progress.1 .runs runId = some before) (empty : before.atoms = []) :
    ∃ reason, insertRunStep document progress runId anchor atoms = .error reason := by
  cases accepted : insertRunStep document progress runId anchor atoms with
  | error reason => exact ⟨reason, rfl⟩
  | ok next =>
      obtain ⟨found', cut, found'', _, _, _, checked, _⟩ := insertRunStep_ok accepted
      have same : before = found' := Option.some.inj (found.symm.trans found'')
      subst same
      simp [insertRunCheck, empty] at checked

/-- Over the run's slot locations the insertion cut is the Theory's own `cut?` of
the anchor's decoded endpoint (`none`: the end), and the new slot order is that
splice. -/
theorem insertRun_order {document : DocumentId} {progress next : Progress} {runId : RunId}
    {anchor : Option StablePoint} {atoms : List AtomId}
    (accepted : insertRunStep document progress runId anchor atoms = .ok next) :
    ∃ before after cut,
      Hyperdocument.lookup progress.1 .runs runId = some before ∧
      Hyperdocument.lookup next.1 .runs runId = some after ∧
      after.atoms = before.atoms.take cut ++ atoms ++ before.atoms.drop cut ∧
      cut ≤ before.atoms.length ∧
      (match anchor with
        | none => cut = before.atoms.length
        | some point => ∃ endpoint,
            StableRanges.HyperdocumentAdapter.decodePoint? point = some endpoint ∧
            StableRanges.cut? (slotLocations runId before) endpoint = some cut) := by
  obtain ⟨before, cut, found, _, _, inserted, _, rfl⟩ := insertRunStep_ok accepted
  refine ⟨before, { before with atoms := before.atoms.take cut ++ atoms ++ before.atoms.drop cut },
    cut, found, ?_, rfl, ?_, ?_⟩
  · unfold Hyperdocument.lookup; exact Store.Store.set_eq _ _ _
  · cases anchor with
    | none => simp [insertionCut] at inserted; omega
    | some point =>
        simp only [insertionCut] at inserted
        split at inserted
        · split at inserted
          · cases inserted
          · rename_i atom neighbor
            obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp inserted
            obtain ⟨bound, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
            cases point.bias <;> simp [cutAt] <;> omega
        · cases inserted
  · cases anchor with
    | none => simp [insertionCut] at inserted; omega
    | some point =>
        simp only [insertionCut] at inserted
        split at inserted
        · rename_i sameRun
          split at inserted
          · cases inserted
          · rename_i atom neighbor
            obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp inserted
            refine ⟨⟨⟨point.run, atom⟩, StableRanges.HyperdocumentAdapter.sideOfBias point.bias, point.death⟩,
              ?_, ?_⟩
            · cases point with
              | mk run neighbor' bias death => simp at neighbor; subst neighbor; rfl
            · unfold StableRanges.cut? slotLocations
              rw [sameRun, position_map, hi]
              cases point.bias <;> rfl
        · cases inserted


/-- Over the live order the Theory projects against, the edit is a splice of the
inserted live atoms, at the live count of the slots before the cut. -/
theorem insertRun_live_order {document : DocumentId} {progress next : Progress} {runId : RunId}
    {anchor : Option StablePoint} {atoms : List AtomId}
    (accepted : insertRunStep document progress runId anchor atoms = .ok next)
    {before after : RunRecord} {cut : Nat}
    (afterAtoms : after.atoms = before.atoms.take cut ++ atoms ++ before.atoms.drop cut) :
    liveOrder next.1 document runId after =
      (liveOrder progress.1 document runId before).take
          ((before.atoms.take cut).filter (slotLive progress.1 document)).length ++
        (atoms.filter (slotLive progress.1 document)).map (fun atom => (⟨runId, atom⟩ : RunLocation)) ++
        (liveOrder progress.1 document runId before).drop
          ((before.atoms.take cut).filter (slotLive progress.1 document)).length := by
  have alive : slotLive next.1 document = slotLive progress.1 document :=
    funext (insertRun_slotLive accepted)
  unfold liveOrder
  rw [alive, afterAtoms]
  have whole : before.atoms.filter (slotLive progress.1 document) =
      (before.atoms.take cut).filter (slotLive progress.1 document) ++
        (before.atoms.drop cut).filter (slotLive progress.1 document) := by
    conv_lhs => rw [← List.take_append_drop cut before.atoms]
    rw [List.filter_append]
  rw [whole, ← List.map_take, ← List.map_drop, List.take_left' rfl, List.drop_left' rfl]
  simp [List.filter_append, List.map_append]

/-- Every stored point that names its slot still does: ranges stored in links,
marks and other records of this document stay valid. -/
theorem insertRun_preserves_point {document : DocumentId} {progress next : Progress} {runId : RunId}
    {anchor : Option StablePoint} {atoms : List AtomId}
    (accepted : insertRunStep document progress runId anchor atoms = .ok next)
    (point : StablePoint)
    (present : HyperdocumentOperations.storedPointPresentInDocument progress.1 document point) :
    HyperdocumentOperations.storedPointPresentInDocument next.1 document point := by
  obtain ⟨before, cut, found, _, _, _, checked, rfl⟩ := insertRunStep_ok accepted
  obtain ⟨run, runFound, runOwned, shape⟩ := present
  have atomSame : ∀ atom, Hyperdocument.lookup
      (progress.1.set ⟨.runs, runId⟩ (some { before with
        atoms := before.atoms.take cut ++ atoms ++ before.atoms.drop cut })) .atoms atom =
      Hyperdocument.lookup progress.1 .atoms atom := by
    intro atom
    unfold Hyperdocument.lookup
    exact Store.Store.set_ne _ _ _ _ (fun same => by cases same)
  by_cases sameRun : point.run = runId
  · have runIs : run = before := by
      have : Hyperdocument.lookup progress.1 .runs point.run = some before := by
        rw [sameRun]; exact found
      exact Option.some.inj (runFound.symm.trans this)
    subst runIs
    refine ⟨{ run with atoms := run.atoms.take cut ++ atoms ++ run.atoms.drop cut }, ?_, runOwned, ?_⟩
    · unfold Hyperdocument.lookup
      rw [sameRun]; exact Store.Store.set_eq _ _ _
    · cases neighbor : point.neighbor with
      | none =>
          rw [neighbor] at shape
          simp [insertRunCheck, shape] at checked
      | some atom =>
          rw [neighbor] at shape
          obtain ⟨member, record, recordFound, recordOwned⟩ := shape
          refine ⟨?_, record, by rw [atomSame]; exact recordFound, recordOwned⟩
          have := List.take_append_drop cut run.atoms
          simp only [List.mem_append]
          have inBoth : atom ∈ run.atoms.take cut ∨ atom ∈ run.atoms.drop cut := by
            rw [← List.mem_append, this]; exact member
          tauto
  · refine ⟨run, ?_, runOwned, ?_⟩
    · unfold Hyperdocument.lookup
      rw [Store.Store.set_ne _ _ _ _ (fun same => sameRun (by cases same; rfl))]
      exact runFound
    · cases neighbor : point.neighbor with
      | none => rw [neighbor] at shape; exact shape
      | some atom =>
          rw [neighbor] at shape
          obtain ⟨member, record, recordFound, recordOwned⟩ := shape
          exact ⟨member, record, by rw [atomSame]; exact recordFound, recordOwned⟩

/-- After an accepted `insertRun`, the kernel's reading of an unchanged stored
range is the Theory's projection of the range *transported through*
`Edit.insert` over the post-edit live order.  The endpoints are live atoms of the
run, as the kernel reads it after the edit. -/
theorem insertRun_transports_range {document : DocumentId} {progress next : Progress}
    {runId : RunId} {anchor : Option StablePoint} {atoms : List AtomId}
    (accepted : insertRunStep document progress runId anchor atoms = .ok next)
    {after : RunRecord}
    (found : Hyperdocument.lookup next.1 .runs runId = some after) (owned : after.document = document)
    (a b : AtomId) (bs bf : AnchorBias) (ds df : EndpointDeathPolicy) (i j : Nat)
    (atA : after.atoms.findIdx? (· == a) = some i) (atB : after.atoms.findIdx? (· == b) = some j)
    (liveA : slotLive progress.1 document a = true) (liveB : slotLive progress.1 document b = true)
    (ordered : cutAt bs i ≤ cutAt bf j)
    (range : StableRanges.StableRange RunId AtomId)
    (decoded : StableRanges.HyperdocumentAdapter.decodeRange?
      ⟨⟨runId, some a, bs, ds⟩, ⟨runId, some b, bf, df⟩⟩ = some range) :
    liveSlots next.1 document ⟨⟨runId, some a, bs, ds⟩, ⟨runId, some b, bf, df⟩⟩ =
      (StableRanges.projectRange (liveOrder next.1 document runId after)
          ((StableRanges.RangeTrace.init range).step
            (.insert runId atoms (anchor.bind StableRanges.HyperdocumentAdapter.decodePoint?)))).map
        fun projected => projected.atoms.map (·.atom) := by
  have refined := resolveRange_refines_projectRange next.1 document runId after found owned a b bs bf ds df
    i j atA atB (by rw [insertRun_slotLive accepted]; exact liveA)
    (by rw [insertRun_slotLive accepted]; exact liveB) ordered range decoded
  rw [refined]
  have current := StableRanges.RangeTrace.step_insert_current (StableRanges.RangeTrace.init range)
    runId atoms (anchor.bind StableRanges.HyperdocumentAdapter.decodePoint?)
  simp only [StableRanges.projectRange, current.1, current.2]
  generalize (StableRanges.RangeTrace.init range).start.current.current? = first
  generalize (StableRanges.RangeTrace.init range).stop.current.current? = last
  rcases first with _ | first <;> rcases last with _ | last <;> try simp
  all_goals
    rcases StableRanges.cut? (liveOrder next.1 document runId after) first with _ | startCut <;> try simp
  all_goals
    rcases StableRanges.cut? (liveOrder next.1 document runId after) last with _ | stopCut <;> try simp


/-! ## Poles on a real run: five lines, then two appended -/

namespace RunEditAudit

open Minidregg.Kernel.ContentResource.Audit

/-- Lines 6 and 7 are created and appended to the run the source was written with. -/
def appendTwo : Command :=
  ⟨[.createAtom (lineAtom 6) .text [6], .createAtom (lineAtom 7) .text [7],
    .insertRun sourceRun none [lineAtom 6, lineAtom 7]]⟩
def appended : ContentStore := postOf (run author nextOperation document ctx source0 appendTwo)

/-- Line 6 created and slotted after line 3, inside the range lines 2..4. -/
def insertInside : Command :=
  ⟨[.createAtom (lineAtom 6) .text [6],
    .insertRun sourceRun (some ⟨sourceRun, some (lineAtom 3), .after, .keepTombstone⟩) [lineAtom 6]]⟩
def insertedInside : ContentStore := postOf (run author nextOperation document ctx source0 insertInside)

/-- A range whose endpoints are the two appended lines (after the run was made). -/
def lines5to7 : Hyperdocument.StableRange :=
  ⟨⟨sourceRun, some (lineAtom 5), .before, .keepTombstone⟩,
    ⟨sourceRun, some (lineAtom 7), .after, .keepTombstone⟩⟩
def opening5to7 : RangeOpening :=
  ⟨100, lines5to7, [(lineAtom 5, operation), (lineAtom 6, nextOperation), (lineAtom 7, nextOperation)], 0⟩

/-- A line appended by a later command can be named by a range, and the ranges
made before it keep reading what they read. -/
theorem appended_lines_are_range_addressable :
    refusalOf (run author nextOperation document ctx source0 appendTwo) = none ∧
    Hyperdocument.lookup appended .runs sourceRun =
      some ⟨document, (List.range 7).map (fun n => lineAtom (n + 1)), author, operation, none⟩ ∧
    renderLive appended (opening .keepTombstone) = .live [[2], [3], [4]] false ∧
    renderLive appended opening5to7 = .live [[5], [6], [7]] false ∧
    openingHolds appended ⟨100, lines5to7, .live, opening5to7.pins⟩ = true := by
  decide

/-- An insertion inside a range shows in the live rendering (`revised`) and
moves no endpoint; the snapshot's pins no longer cover the range's live atoms. -/
theorem insert_inside_a_range_is_live :
    refusalOf (run author nextOperation document ctx source0 insertInside) = none ∧
    Hyperdocument.lookup insertedInside .runs sourceRun =
      some ⟨document, [lineAtom 1, lineAtom 2, lineAtom 3, lineAtom 6, lineAtom 4, lineAtom 5],
        author, operation, none⟩ ∧
    renderLive insertedInside (opening .keepTombstone) = .live [[2], [3], [6], [4]] true := by
  decide

/-- Refused `invalidRun`: an unknown run, an atom already in the run, an atom of
no document line, an anchor in another run or at an absent atom, and an empty run. -/
theorem bad_insertions_refused :
    refusalOf (run author nextOperation document ctx appended
      ⟨[.insertRun ⟨⟨999⟩⟩ none [lineAtom 6]]⟩) = some .invalidRun ∧
    refusalOf (run author nextOperation document ctx appended
      ⟨[.insertRun sourceRun none [lineAtom 6]]⟩) = some .invalidRun ∧
    refusalOf (run author nextOperation document ctx source0
      ⟨[.insertRun sourceRun none [lineAtom 9]]⟩) = some .invalidRun ∧
    refusalOf (run author nextOperation document ctx source0
      ⟨[.createAtom (lineAtom 6) .text [6],
        .insertRun sourceRun (some ⟨⟨⟨999⟩⟩, some (lineAtom 3), .after, .keepTombstone⟩) [lineAtom 6]]⟩) =
      some .invalidRun ∧
    refusalOf (run author nextOperation document ctx source0
      ⟨[.createAtom (lineAtom 6) .text [6],
        .insertRun sourceRun (some ⟨sourceRun, some (lineAtom 9), .after, .keepTombstone⟩) [lineAtom 6]]⟩) =
      some .invalidRun ∧
    refusalOf (run author nextOperation document ctx source0
      ⟨[.createAtom (lineAtom 6) .text [6], .createRun ⟨⟨311⟩⟩ [],
        .insertRun ⟨⟨311⟩⟩ none [lineAtom 6]]⟩) = some .invalidRun := by
  decide

end RunEditAudit

#assert_axioms position_map
#assert_axioms filter_findIdx
#assert_axioms filter_slice
#assert_axioms resolveRange_refines_projectRange
#assert_axioms insertRun_frame
#assert_axioms insertRun_into_empty_refused
#assert_axioms insertRun_order
#assert_axioms insertRun_live_order
#assert_axioms insertRun_preserves_point
#assert_axioms insertRun_transports_range
#assert_axioms RunEditAudit.appended_lines_are_range_addressable
#assert_axioms RunEditAudit.insert_inside_a_range_is_live
#assert_axioms RunEditAudit.bad_insertions_refused

end Minidregg.Kernel.ContentResource
