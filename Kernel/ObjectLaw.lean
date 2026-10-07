/- The enforced `law` fragment of a package: its syntax, its own meaning over the
declared state, and its compilation to the kernel's `Pred`.

A `.obend` package may declare, at top level, `law NAME: EXPR`: an admission law over the
declared state of every object created from the package. The kernel judges every write of that
state by it (`ObjectRecord.effectiveLaw`). This module fixes what such a law MEANS and proves
the kernel judges exactly that.

* `LawExpr` is the fragment: comparisons of a reference with an integer, of two references
  (with an optional constant offset), membership in a finite set, `monotone`/`writeOnce` of a
  field, and the Boolean closure (`not`, `and`, `or`, `implies`). A reference is `new.FIELD`
  (a top-level field of the declared state: v1 restricts FIELD to one plain name, nested paths
  are refused at elaboration) or one of the request facts `subject`, `caller`, `height`, `turn`.
* `LawExpr.denote facts old new` is its meaning, read off the declared-state DATA: a field
  reads the first scalar (natural or boolean) field of that name of the top-level record, a
  request reference reads `Facts`. It does not mention `Pred`.
* `compile : LawExpr → Pred` is what the kernel installs.

`compile_sound`: on the views the kernel judges (`ObjectRecord.views`), the compiled predicate
evaluates to the denotation, for every law whose field names are plain. The proof rests on
`State.get` of a view reading exactly the first scalar field of that name
(`views_read_field`): the request block never names `state/…`, and a nested or variant slot
of a field carries a `.` or `@` after its field name, which a plain name cannot contain. -/
import Kernel.ObjectRecord

namespace Minidregg.Kernel.ObjectLaw
open Minidregg.Kernel.ObjectRecord
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Pred (Pred State Slot eval)
set_option autoImplicit false

/-! ## The fragment -/

/-- A reference a law reads. `field name` is `new.name` (a top-level field of the declared
state); the others are the request facts. -/
inductive LawRef where
  | field (name : String)
  | subject
  | caller
  | height
  | turn
  deriving DecidableEq, Repr

/-- The enforced fragment. `old.` appears only through `monotone` and `writeOnce`. -/
inductive LawExpr where
  | eqC (ref : LawRef) (value : Int)
  | leC (ref : LawRef) (value : Int)
  | inC (ref : LawRef) (values : List Int)
  | eqR (left right : LawRef)
  | leR (left right : LawRef)
  | leROff (left right : LawRef) (offset : Int)
  | monotone (field : String)
  | writeOnce (field : String)
  | not (body : LawExpr)
  | and (left right : LawExpr)
  | or (left right : LawExpr)
  | implies (premise conclusion : LawExpr)
  deriving DecidableEq, Repr

def LawRef.plain : LawRef → Bool
  | .field name => plainName name
  | _ => true

/-- Every field a law names is a law field name. -/
def LawExpr.fieldsPlain : LawExpr → Bool
  | .eqC ref _ | .leC ref _ | .inC ref _ => ref.plain
  | .eqR left right | .leR left right | .leROff left right _ => left.plain && right.plain
  | .monotone field | .writeOnce field => plainName field
  | .not body => body.fieldsPlain
  | .and left right | .or left right | .implies left right => left.fieldsPlain && right.fieldsPlain

/-! ## Its meaning, over the declared-state data -/

/-- The scalar a value projects to, if it is a scalar: a natural is itself, a boolean 0 or 1. -/
def scalarOf : Data → Option Int
  | .natural value => some (Int.ofNat value)
  | .boolean value => some (if value then 1 else 0)
  | _ => none

/-- The first scalar field called `name` of a record's fields. -/
def firstScalarField (name : String) : List (String × Data) → Option Int
  | [] => none
  | (field, value) :: rest =>
      if field = name then
        match scalarOf value with
        | some scalar => some scalar
        | none => firstScalarField name rest
      else firstScalarField name rest

/-- The field `name` of a declared state: only a record has fields. -/
def fieldOf (name : String) : Data → Option Int
  | .record fields => firstScalarField name fields
  | _ => none

/-- What a reference reads on the new state of a write under `facts`. -/
def LawRef.read (facts : Facts) (new : Data) : LawRef → Option Int
  | .field name => fieldOf name new
  | .subject => facts.subject.map (fun subject => Int.ofNat subject.value)
  | .caller => facts.caller.map Int.ofNat
  | .height => some (Int.ofNat facts.height)
  | .turn => some (Int.ofNat facts.turn)

/-- **The meaning of a law**: does the write from `old` (absent at a first write) to `new`,
under `facts`, satisfy it? A comparison with an absent reading is false; `monotone` needs both
readings; `writeOnce` holds when the old reading is absent or 0, else the new one must equal it. -/
def LawExpr.denote (facts : Facts) (old : Option Data) (new : Data) : LawExpr → Bool
  | .eqC ref value => decide (ref.read facts new = some value)
  | .leC ref value =>
      match ref.read facts new with
      | some x => decide (x ≤ value)
      | none => false
  | .inC ref values =>
      match ref.read facts new with
      | some x => values.contains x
      | none => false
  | .eqR left right =>
      match left.read facts new, right.read facts new with
      | some x, some y => decide (x = y)
      | _, _ => false
  | .leR left right =>
      match left.read facts new, right.read facts new with
      | some x, some y => decide (x ≤ y)
      | _, _ => false
  | .leROff left right offset =>
      match left.read facts new, right.read facts new with
      | some x, some y => decide (x ≤ y + offset)
      | _, _ => false
  | .monotone field =>
      match old.bind (fieldOf field), fieldOf field new with
      | some before, some after => decide (before ≤ after)
      | _, _ => false
  | .writeOnce field =>
      match old.bind (fieldOf field) with
      | none => true
      | some before => before == 0 || decide (fieldOf field new = some before)
  | .not body => !body.denote facts old new
  | .and left right => left.denote facts old new && right.denote facts old new
  | .or left right => left.denote facts old new || right.denote facts old new
  | .implies premise conclusion => !premise.denote facts old new || conclusion.denote facts old new

/-! ## Compilation to the kernel's predicate -/

/-- The view slot a reference reads (`ObjectRecord.stateSlots`, `Facts.slots`). -/
def LawRef.slot : LawRef → Slot
  | .field name => "state/" ++ name
  | .subject => "request/subject"
  | .caller => "request/caller"
  | .height => "request/height"
  | .turn => "request/turn"

/-- The predicate the kernel installs for a law. -/
def compile : LawExpr → Pred
  | .eqC ref value => .eq ref.slot value
  | .leC ref value => .le ref.slot value
  | .inC ref values => .memberOf ref.slot values
  | .eqR left right => .eqSlots left.slot right.slot
  | .leR left right => .leSlots left.slot right.slot
  | .leROff left right offset => .leSlotsOff left.slot right.slot offset
  | .monotone field => .monotone ("state/" ++ field)
  | .writeOnce field => .writeOnce ("state/" ++ field)
  | .not body => .not (compile body)
  | .and left right => Pred.all [compile left, compile right]
  | .or left right => Pred.any [compile left, compile right]
  | .implies premise conclusion => Pred.any [.not (compile premise), compile conclusion]

/-! ## Reading a view -/

theorem get_append (front back : List (Slot × Int)) (key : Slot) :
    State.get ⟨front ++ back⟩ key = (State.get ⟨front⟩ key).or (State.get ⟨back⟩ key) := by
  simp only [State.get, List.find?_append]
  cases List.find? (fun p => p.1 == key) front <;> simp

theorem get_none (slots : List (Slot × Int)) (key : Slot) (absent : ∀ p ∈ slots, p.1 ≠ key) :
    State.get ⟨slots⟩ key = none := by
  simp only [State.get, Option.map_eq_none_iff, List.find?_eq_none, beq_iff_eq]
  exact absent

/-- `key` extends `path` past a separator: `path`, then `.` or `@`, then more. -/
def Extends (path key : String) : Prop :=
  ∃ c rest, key.toList = path.toList ++ c :: rest ∧ (c = '.' ∨ c = '@')

theorem extends_of_child (path label key sep : String) (sepIs : sep = "." ∨ sep = "@")
    (child : key = path ++ sep ++ label ∨ Extends (path ++ sep ++ label) key) : Extends path key := by
  obtain ⟨c, sepList, cIs⟩ : ∃ c, sep.toList = [c] ∧ (c = '.' ∨ c = '@') := by
    rcases sepIs with rfl | rfl
    · exact ⟨'.', by decide, .inl rfl⟩
    · exact ⟨'@', by decide, .inr rfl⟩
  rcases child with rfl | ⟨d, rest, keyList, _⟩
  · exact ⟨c, label.toList, by simp [String.toList_append, sepList], cIs⟩
  · exact ⟨c, label.toList ++ d :: rest, by simp [keyList, String.toList_append, sepList], cIs⟩

mutual
/-- Every slot of a value at `path` is `path` itself (exactly when the value is a scalar,
holding that scalar) or extends `path` past a `.` or `@`. -/
theorem slotsOf_keys : (path : String) → (value : Data) → (slots : List (Slot × Int)) →
    slotsOf path value = some slots →
    ∀ p ∈ slots, (p.1 = path ∧ scalarOf value = some p.2) ∨ Extends path p.1
  | path, .natural v, slots, projected => by
      simp only [slotsOf, Option.some.injEq] at projected
      subst projected
      intro p mem
      simp only [List.mem_singleton] at mem
      subst mem
      exact .inl ⟨rfl, rfl⟩
  | path, .boolean v, slots, projected => by
      simp only [slotsOf, Option.some.injEq] at projected
      subst projected
      intro p mem
      simp only [List.mem_singleton] at mem
      subst mem
      exact .inl ⟨rfl, rfl⟩
  | path, .label _, slots, projected => by
      simp only [slotsOf, Option.some.injEq] at projected
      subst projected
      intro p mem
      simp at mem
  | path, .record fields, slots, projected => by
      intro p mem
      exact .inr (fieldSlots_keys path fields slots (by simpa only [slotsOf] using projected) p mem)
  | path, .variant label payload, slots, projected => by
      simp only [slotsOf] at projected
      split at projected
      · cases inner : slotsOf (path ++ "." ++ label) payload with
        | none => simp [inner] at projected
        | some innerSlots =>
          simp only [inner, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at projected
          subst projected
          intro p mem
          simp only [List.mem_cons] at mem
          rcases mem with rfl | mem
          · exact .inr (extends_of_child path label _ "@" (.inr rfl) (.inl rfl))
          · refine .inr (extends_of_child path label p.1 "." (.inl rfl) ?_)
            rcases slotsOf_keys (path ++ "." ++ label) payload innerSlots inner p mem with ⟨same, _⟩ | ext
            · exact .inl same
            · exact .inr ext
      · cases projected
/-- Every slot of a record's fields at `path` extends `path` past a `.` or `@`. -/
theorem fieldSlots_keys : (path : String) → (fields : List (String × Data)) →
    (slots : List (Slot × Int)) → fieldSlots path fields = some slots →
    ∀ p ∈ slots, Extends path p.1
  | path, [], slots, projected => by
      simp only [fieldSlots, Option.some.injEq] at projected
      subst projected
      intro p mem
      simp at mem
  | path, (name, value) :: rest, slots, projected => by
      simp only [fieldSlots] at projected
      split at projected
      · cases here : slotsOf (path ++ "." ++ name) value with
        | none => simp [here] at projected
        | some hereSlots =>
          cases later : fieldSlots path rest with
          | none => simp [here, later] at projected
          | some laterSlots =>
            simp only [here, later, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq] at projected
            subst projected
            intro p mem
            rcases List.mem_append.mp mem with mem | mem
            · refine extends_of_child path name p.1 "." (.inl rfl) ?_
              rcases slotsOf_keys _ value hereSlots here p mem with ⟨same, _⟩ | ext
              · exact .inl same
              · exact .inr ext
            · exact fieldSlots_keys path rest laterSlots later p mem
      · cases projected
end

theorem not_contains_of_plainName (name : String) (plain : plainName name = true) :
    '.' ∉ name.toList ∧ '@' ∉ name.toList := by
  simp only [plainName, Bool.and_eq_true, List.all_eq_true] at plain
  refine ⟨fun mem => ?_, fun mem => ?_⟩ <;> have := plain.2 _ mem <;> simp at this

/-- A slot extending `state/n` is never `state/name` for a name without `.` or `@`. -/
theorem extends_ne_field (n name key : String) (noDot : '.' ∉ name.toList) (noAt : '@' ∉ name.toList)
    (ext : Extends ("state/" ++ n) key) : key ≠ "state/" ++ name := by
  rintro rfl
  obtain ⟨c, rest, keyList, cIs⟩ := ext
  rw [String.toList_append, String.toList_append, List.append_assoc] at keyList
  have tail := List.append_cancel_left keyList
  have mem : c ∈ name.toList := by rw [tail]; simp
  rcases cIs with rfl | rfl
  · exact noDot mem
  · exact noAt mem

theorem field_key_inj (n name : String) (same : "state/" ++ n = "state/" ++ name) : n = name := by
  have lists := congrArg String.toList same
  rw [String.toList_append, String.toList_append] at lists
  exact String.toList_inj.mp (List.append_cancel_left lists)

/-- The top-level fields' slots read `state/name` as the first scalar field `name`. -/
theorem fieldSlotsTop_get (name : String) (noDot : '.' ∉ name.toList) (noAt : '@' ∉ name.toList) :
    (fields : List (String × Data)) → (slots : List (Slot × Int)) →
    stateSlots.fieldSlotsTop fields = some slots →
    State.get ⟨slots⟩ ("state/" ++ name) = firstScalarField name fields
  | [], slots, projected => by
      simp only [stateSlots.fieldSlotsTop, Option.some.injEq] at projected
      subst projected
      rfl
  | (n, value) :: rest, slots, projected => by
      simp only [stateSlots.fieldSlotsTop] at projected
      split at projected
      · cases here : slotsOf ("state/" ++ n) value with
        | none => simp [here] at projected
        | some hereSlots =>
          cases later : stateSlots.fieldSlotsTop rest with
          | none => simp [here, later] at projected
          | some laterSlots =>
            simp only [here, later, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq] at projected
            subst projected
            rw [get_append, fieldSlotsTop_get name noDot noAt rest laterSlots later]
            have keys := slotsOf_keys _ value hereSlots here
            by_cases same : n = name
            · subst same
              cases scalar : scalarOf value with
              | some x =>
                  cases value with
                  | natural v =>
                      simp only [slotsOf, Option.some.injEq] at here
                      simp only [scalarOf, Option.some.injEq] at scalar
                      subst here scalar
                      simp [State.get, firstScalarField, scalarOf]
                  | boolean v =>
                      simp only [slotsOf, Option.some.injEq] at here
                      simp only [scalarOf, Option.some.injEq] at scalar
                      subst here scalar
                      simp [State.get, firstScalarField, scalarOf]
                  | label _ => simp [scalarOf] at scalar
                  | record _ => simp [scalarOf] at scalar
                  | variant _ _ => simp [scalarOf] at scalar
              | none =>
                  have absent : State.get ⟨hereSlots⟩ ("state/" ++ n) = none :=
                    get_none _ _ (fun p mem => by
                      rcases keys p mem with ⟨_, holds⟩ | ext
                      · rw [scalar] at holds; cases holds
                      · exact extends_ne_field n n p.1 noDot noAt ext)
                  simp [absent, firstScalarField, scalar]
            · have absent : State.get ⟨hereSlots⟩ ("state/" ++ name) = none :=
                get_none _ _ (fun p mem => by
                  rcases keys p mem with ⟨isPath, _⟩ | ext
                  · rw [isPath]; exact fun eq => same (field_key_inj n name eq)
                  · exact extends_ne_field n name p.1 noDot noAt ext)
              simp [absent, firstScalarField, same]
      · cases projected

theorem state_slash : ("state/" : String).toList = ("state" : String).toList ++ ['/'] := by decide

/-- **The state slots read `state/name` as the field `name`** (the first scalar field of
that name of the top-level record; nothing for a state that is not a record). -/
theorem stateSlots_get_field (value : Data) (slots : List (Slot × Int))
    (projected : stateSlots value = some slots) (name : String)
    (noDot : '.' ∉ name.toList) (noAt : '@' ∉ name.toList) :
    State.get ⟨slots⟩ ("state/" ++ name) = fieldOf name value := by
  have notRecord : (∀ fields, value ≠ .record fields) → slotsOf "state" value = some slots →
      State.get ⟨slots⟩ ("state/" ++ name) = none := by
    intro _ atState
    apply get_none
    intro p mem eq
    have lists := congrArg String.toList eq
    rw [String.toList_append, state_slash, List.append_assoc] at lists
    rcases slotsOf_keys "state" value slots atState p mem with ⟨isPath, _⟩ | ⟨c, rest, keyList, cIs⟩
    · rw [isPath] at lists
      simp at lists
    · rw [keyList] at lists
      have := List.append_cancel_left lists
      simp only [List.singleton_append, List.cons.injEq] at this
      rcases cIs with rfl | rfl <;> exact absurd this.1 (by decide)
  cases value with
  | record fields => exact fieldSlotsTop_get name noDot noAt fields slots projected
  | natural v => exact notRecord (fun _ h => by cases h) projected
  | boolean v => exact notRecord (fun _ h => by cases h) projected
  | label v => exact notRecord (fun _ h => by cases h) projected
  | variant l p => exact notRecord (fun _ h => by cases h) projected

/-- The slot names of the request block. -/
def factKeys : List String :=
  ["objective/artifact", "request/subject", "request/height", "request/target", "request/turn",
   "request/caller"]

theorem facts_keys (facts : Facts) : ∀ p ∈ facts.slots, p.1 ∈ factKeys := by
  intro p mem
  obtain ⟨key, v⟩ := p
  cases hs : facts.subject <;> cases hc : facts.caller <;>
    simp [Facts.slots, hs, hc, Minidregg.Pred.objectiveArtifactSlot] at mem <;>
    simp only [factKeys, List.mem_cons, List.mem_nil_iff, or_false] <;>
    rcases mem with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem factKeys_not_state : ∀ key ∈ factKeys, key.toList.head? ≠ some 's' := by decide

theorem head_ne_state (key : String) (head : key.toList.head? ≠ some 's') (rest : List Char) :
    key.toList ≠ ("state" : String).toList ++ rest := by
  intro eq
  apply head
  rw [eq]
  rfl

/-- The request block never holds a `state/…` slot. -/
theorem facts_get_field (facts : Facts) (name : String) :
    State.get ⟨facts.slots⟩ ("state/" ++ name) = none := by
  apply get_none
  intro p mem eq
  have head := factKeys_not_state p.1 (facts_keys facts p mem)
  apply head_ne_state p.1 head ('/' :: name.toList)
  rw [eq, String.toList_append, state_slash, List.append_assoc]
  rfl

/-- Every slot of a declared state lies under `state`. -/
theorem stateSlots_keys (value : Data) (slots : List (Slot × Int)) (projected : stateSlots value = some slots) :
    ∀ p ∈ slots, ∃ rest, p.1.toList = ("state" : String).toList ++ rest := by
  have under : ∀ (path : String) (key : String), (∃ r, path.toList = ("state" : String).toList ++ r) →
      (key = path ∨ Extends path key) → ∃ rest, key.toList = ("state" : String).toList ++ rest := by
    rintro path key ⟨r, pathList⟩ (rfl | ⟨c, more, keyList, _⟩)
    · exact ⟨r, pathList⟩
    · exact ⟨r ++ c :: more, by rw [keyList, pathList, List.append_assoc]⟩
  cases value with
  | record fields =>
      simp only [stateSlots] at projected
      clear under
      induction fields generalizing slots with
      | nil =>
          simp only [stateSlots.fieldSlotsTop, Option.some.injEq] at projected
          subst projected; intro p mem; simp at mem
      | cons field rest ih =>
          obtain ⟨n, value⟩ := field
          simp only [stateSlots.fieldSlotsTop] at projected
          split at projected
          · cases here : slotsOf ("state/" ++ n) value with
            | none => simp [here] at projected
            | some hereSlots =>
              cases later : stateSlots.fieldSlotsTop rest with
              | none => simp [here, later] at projected
              | some laterSlots =>
                simp only [here, later, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                  Option.some.injEq] at projected
                subst projected
                intro p mem
                rcases List.mem_append.mp mem with mem | mem
                · have pathList : ("state/" ++ n).toList = ("state" : String).toList ++ ('/' :: n.toList) := by
                    rw [String.toList_append, state_slash, List.append_assoc]; rfl
                  rcases slotsOf_keys _ value hereSlots here p mem with ⟨isPath, _⟩ | ⟨c, more, keyList, _⟩
                  · exact ⟨_, by rw [isPath, pathList]⟩
                  · exact ⟨('/' :: n.toList) ++ c :: more, by rw [keyList, pathList, List.append_assoc]⟩
                · exact ih laterSlots later p mem
          · cases projected
  | natural v | boolean v | label v =>
      intro p mem
      exact under "state" p.1 ⟨[], by simp⟩
        (by rcases slotsOf_keys "state" _ slots projected p mem with ⟨isPath, _⟩ | ext
            · exact .inl isPath
            · exact .inr ext)
  | variant l payload =>
      intro p mem
      exact under "state" p.1 ⟨[], by simp⟩
        (by rcases slotsOf_keys "state" _ slots projected p mem with ⟨isPath, _⟩ | ext
            · exact .inl isPath
            · exact .inr ext)

/-- A request slot is never a state slot. -/
theorem stateSlots_get_request (value : Data) (slots : List (Slot × Int))
    (projected : stateSlots value = some slots) (key : String) (head : key.toList.head? ≠ some 's') :
    State.get ⟨slots⟩ key = none := by
  apply get_none
  intro p mem eq
  obtain ⟨rest, keyList⟩ := stateSlots_keys value slots projected p mem
  rw [eq] at keyList
  exact head_ne_state key head rest keyList

/-! ## The views read the meaning -/

/-- **The new view reads every plain reference as `LawRef.read`.** -/
theorem new_view_reads (facts : Facts) (new : Data) (slots : List (Slot × Int))
    (projected : stateSlots new = some slots) (ref : LawRef) (plain : ref.plain = true) :
    State.get ⟨facts.slots ++ slots⟩ ref.slot = ref.read facts new := by
  rw [get_append]
  cases ref with
  | field name =>
      obtain ⟨noDot, noAt⟩ := not_contains_of_plainName name plain
      show (State.get ⟨facts.slots⟩ ("state/" ++ name)).or (State.get ⟨slots⟩ ("state/" ++ name)) =
        fieldOf name new
      rw [facts_get_field, stateSlots_get_field new slots projected name noDot noAt]
      rfl
  | subject =>
      cases hs : facts.subject with
      | none =>
          have : State.get ⟨facts.slots⟩ "request/subject" = none := by
            cases hc : facts.caller <;>
              simp [State.get, Facts.slots, hs, hc, Minidregg.Pred.objectiveArtifactSlot]
          simp only [LawRef.slot, LawRef.read, this, hs, Option.map_none, Option.none_or]
          exact stateSlots_get_request new slots projected _ (by decide)
      | some s =>
          simp [State.get, Facts.slots, hs, LawRef.slot, LawRef.read, Minidregg.Pred.objectiveArtifactSlot]
  | caller =>
      cases hc : facts.caller with
      | none =>
          have : State.get ⟨facts.slots⟩ "request/caller" = none := by
            cases hs : facts.subject <;>
              simp [State.get, Facts.slots, hs, hc, Minidregg.Pred.objectiveArtifactSlot]
          simp only [LawRef.slot, LawRef.read, this, hc, Option.map_none, Option.none_or]
          exact stateSlots_get_request new slots projected _ (by decide)
      | some c =>
          cases hs : facts.subject <;>
            simp [State.get, Facts.slots, hs, hc, LawRef.slot, LawRef.read,
              Minidregg.Pred.objectiveArtifactSlot]
  | height =>
      cases hs : facts.subject <;>
        simp [State.get, Facts.slots, hs, LawRef.slot, LawRef.read, Minidregg.Pred.objectiveArtifactSlot]
  | turn =>
      cases hs : facts.subject <;>
        simp [State.get, Facts.slots, hs, LawRef.slot, LawRef.read, Minidregg.Pred.objectiveArtifactSlot]

/-- The parts of a write's views: the request block, then the old and new state slots. -/
theorem views_parts (facts : Facts) (old : Option Data) (new : Data) (before after : State)
    (viewed : views facts old new = some (before, after)) :
    ∃ oldSlots newSlots, before = ⟨facts.slots ++ oldSlots⟩ ∧ after = ⟨facts.slots ++ newSlots⟩ ∧
      stateSlots new = some newSlots ∧
      (∀ value, old = some value → stateSlots value = some oldSlots) ∧ (old = none → oldSlots = []) := by
  unfold views at viewed
  cases old with
  | none =>
    cases h : stateSlots new with
    | none => simp [h] at viewed
    | some a =>
      simp [h] at viewed
      exact ⟨[], a, by simp [← viewed.1], by simp [← viewed.2], rfl, by simp, fun _ => rfl⟩
  | some value =>
    cases hv : stateSlots value with
    | none => simp [hv] at viewed
    | some b =>
      cases h : stateSlots new with
      | none => simp [hv, h] at viewed
      | some a =>
        simp [hv, h] at viewed
        exact ⟨b, a, viewed.1.symm, viewed.2.symm, rfl,
          by intro v eq; cases eq; exact hv, by intro eq; cases eq⟩

/-- **The old view reads a plain field as the old state's field** (nothing at a first write). -/
theorem old_view_reads_field (facts : Facts) (old : Option Data) (oldSlots : List (Slot × Int))
    (some_ : ∀ value, old = some value → stateSlots value = some oldSlots) (none_ : old = none → oldSlots = [])
    (name : String) (plain : plainName name = true) :
    State.get ⟨facts.slots ++ oldSlots⟩ ("state/" ++ name) = old.bind (fieldOf name) := by
  obtain ⟨noDot, noAt⟩ := not_contains_of_plainName name plain
  rw [get_append, facts_get_field]
  cases old with
  | none => rw [none_ rfl]; rfl
  | some value => rw [stateSlots_get_field value oldSlots (some_ value rfl) name noDot noAt]; rfl

/-- **`compile_sound`**: on the views the kernel judges a write by, the compiled law
evaluates to the law's own meaning, for every law whose fields are plain names. -/
theorem compile_sound (facts : Facts) (old : Option Data) (new : Data) (before after : State)
    (viewed : views facts old new = some (before, after)) :
    ∀ law : LawExpr, law.fieldsPlain = true → eval (compile law) before after = law.denote facts old new := by
  obtain ⟨oldSlots, newSlots, rfl, rfl, newProjected, oldSome, oldNone⟩ :=
    views_parts facts old new before after viewed
  have readNew := new_view_reads facts new newSlots newProjected
  have readNewField : ∀ name, plainName name = true →
      State.get ⟨facts.slots ++ newSlots⟩ ("state/" ++ name) = fieldOf name new :=
    fun name plain => readNew (.field name) plain
  have readOld := old_view_reads_field facts old oldSlots oldSome oldNone
  intro law plain
  induction law with
  | eqC ref value =>
      simp only [LawExpr.fieldsPlain] at plain
      simp only [compile, eval, Minidregg.Pred.evalWith, LawExpr.denote, readNew ref plain]
  | leC ref value =>
      simp only [LawExpr.fieldsPlain] at plain
      simp only [compile, eval, Minidregg.Pred.evalWith, LawExpr.denote, readNew ref plain]
      cases LawRef.read facts new ref <;> rfl
  | inC ref values =>
      simp only [LawExpr.fieldsPlain] at plain
      simp only [compile, eval, Minidregg.Pred.evalWith, LawExpr.denote, readNew ref plain]
      cases LawRef.read facts new ref <;> rfl
  | eqR left right =>
      simp only [LawExpr.fieldsPlain, Bool.and_eq_true] at plain
      simp only [compile, eval, Minidregg.Pred.evalWith, LawExpr.denote, readNew left plain.1,
        readNew right plain.2]
      cases LawRef.read facts new left <;> cases LawRef.read facts new right <;> rfl
  | leR left right =>
      simp only [LawExpr.fieldsPlain, Bool.and_eq_true] at plain
      simp only [compile, eval, Minidregg.Pred.evalWith, LawExpr.denote, readNew left plain.1,
        readNew right plain.2]
      cases LawRef.read facts new left <;> cases LawRef.read facts new right <;> rfl
  | leROff left right offset =>
      simp only [LawExpr.fieldsPlain, Bool.and_eq_true] at plain
      simp only [compile, eval, Minidregg.Pred.evalWith, LawExpr.denote, readNew left plain.1,
        readNew right plain.2]
      cases LawRef.read facts new left <;> cases LawRef.read facts new right <;> rfl
  | monotone field =>
      simp only [LawExpr.fieldsPlain] at plain
      simp only [compile, eval, Minidregg.Pred.evalWith, LawExpr.denote, readOld field plain,
        readNewField field plain]
      cases old.bind (fieldOf field) <;> cases fieldOf field new <;> rfl
  | writeOnce field =>
      simp only [LawExpr.fieldsPlain] at plain
      simp only [compile, eval, Minidregg.Pred.evalWith, LawExpr.denote, readOld field plain,
        readNewField field plain]
      cases old.bind (fieldOf field) <;> rfl
  | not body ih =>
      simp only [LawExpr.fieldsPlain] at plain
      rw [compile, Minidregg.Pred.eval_not, ih plain, LawExpr.denote]
  | and left right ihLeft ihRight =>
      simp only [LawExpr.fieldsPlain, Bool.and_eq_true] at plain
      rw [compile, Minidregg.Pred.eval_all, LawExpr.denote, ← ihLeft plain.1, ← ihRight plain.2]
      simp
  | or left right ihLeft ihRight =>
      simp only [LawExpr.fieldsPlain, Bool.and_eq_true] at plain
      rw [compile, Minidregg.Pred.eval_any, LawExpr.denote, ← ihLeft plain.1, ← ihRight plain.2]
      simp
  | implies premise conclusion ihPremise ihConclusion =>
      simp only [LawExpr.fieldsPlain, Bool.and_eq_true] at plain
      rw [compile, Minidregg.Pred.eval_any, LawExpr.denote, ← ihPremise plain.1,
        ← ihConclusion plain.2]
      simp [Minidregg.Pred.eval_not]

/-! ### The premise is inhabited, and the meaning decides

A tally whose law is `new.total <= 1000 and monotone(total)`: the views of a write exist, the
meaning admits 5 → 7 and refuses 7 → 5 and 5 → 1001. -/

def tallyLaw : LawExpr := .and (.leC (.field "total") 1000) (.monotone "total")

def tallyFacts : Facts := ⟨some ⟨40⟩, 5, 1, 2, none, some 7⟩

def tally (total : Nat) : Data := .record [("label", .label "t"), ("total", .natural total)]

theorem tally_views_inhabited :
    views tallyFacts (some (tally 5)) (tally 7) =
      some (⟨tallyFacts.slots ++ [("state/total", 5)]⟩, ⟨tallyFacts.slots ++ [("state/total", 7)]⟩) := by
  decide +kernel

theorem tally_meaning_decides :
    tallyLaw.fieldsPlain = true ∧
      tallyLaw.denote tallyFacts (some (tally 5)) (tally 7) = true ∧
      tallyLaw.denote tallyFacts (some (tally 7)) (tally 5) = false ∧
      tallyLaw.denote tallyFacts (some (tally 5)) (tally 1001) = false := by
  decide +kernel

#assert_axioms get_append
#assert_axioms get_none
#assert_axioms slotsOf_keys
#assert_axioms fieldSlots_keys
#assert_axioms fieldSlotsTop_get
#assert_axioms stateSlots_get_field
#assert_axioms facts_get_field
#assert_axioms stateSlots_keys
#assert_axioms new_view_reads
#assert_axioms old_view_reads_field
#assert_axioms views_parts
#assert_axioms compile_sound
#assert_axioms tally_views_inhabited
#assert_axioms tally_meaning_decides
end Minidregg.Kernel.ObjectLaw
