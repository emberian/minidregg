/- Declared state types: the bytes of a Core4 type, the kernel's typing of an
object's declared state, and the subtype relation an upgrade's drain consults.

**The type codec.** `Theory.ObjectiveBendTypes.Ty` as tokens (the token stream
data and checkpoints already use), with `Reuse` and `Quantity` as one-token tags.
`tyStream` is a prefix codec (`ty_roundTrip`); `decodeTyBytes` is strict: it
accepts exactly the bytes `tyBytes` produces (`decodeTyBytes_canonical`), so a
type's bytes are a function of the type and a record holding one has one
encoding.

**Declared-state typing (`typedAt`).** A declared state type is first-order
(`Ty.isData`: naturals, booleans, labels, closed records and closed sums of
them; no arrows, custody, specifications, prototypes, variables or
activities). A value is typed at it structurally:
* a natural, boolean or label at the same base type;
* a record at a row `field n m (… emptyRow)`: the record names `n` exactly
  once, its value there is typed at `m`, and the record without `n` is typed at
  the rest of the row; at `emptyRow` the record has no fields left. Records are
  CLOSED: a field the row does not name refuses, a field it names must be there;
* a variant `label payload` at `variant row`: the first case of `row` named
  `label` types the payload.
Every other pairing is `false`. This is the kernel's judgment of an object's
declared state (`ObjectRecord.admitWrite` refuses an ill-typed write before the
law sees it); the checker-based `ObjectiveActivity.typeData` still types what an
activity is shown at its program's own response type.

**Value subtyping (`stateSubtype`).** `stateSubtype a b` means every value typed
at `a` is typed at `b` (`typedAt_of_stateSubtype`), so an object whose old state
type is a subtype of the new one can admit births of the new package on the
unmigrated state. It is about values, not width: records are closed, so a record
row is a subtype only of a row naming exactly the same fields (each member a
subtype, in any order); a sum is a subtype of a sum with at least its cases
(each payload a subtype). It is defined on first-order types only and refuses
arrows, custody, computations, variables, specifications and prototypes. -/
import Kernel.ObjectiveActivityWire
import Theory.ObjectiveBendTypes
import Theory.AssertAxioms

namespace Minidregg.Kernel.ObjectStateType
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.ObjectiveBendCheckpoint (Token Tokens)
open Minidregg.Theory.ObjectiveBendTypes (Ty Reuse Quantity)
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Kernel.ObjectiveActivityWire (Bytes tokensStream)
set_option autoImplicit false

/-! ## The codec -/

def reuseTag : Reuse → Nat
  | .once => 0 | .reusable => 1

def reuseOfTag : Nat → Option Reuse
  | 0 => some .once | 1 => some .reusable | _ => none

theorem reuseOfTag_reuseTag (reuse : Reuse) : reuseOfTag (reuseTag reuse) = some reuse := by
  cases reuse <;> rfl

def quantityTag : Quantity → Nat
  | .erased => 0 | .affine => 1 | .linear => 2 | .unrestricted => 3

def quantityOfTag : Nat → Option Quantity
  | 0 => some .erased | 1 => some .affine | 2 => some .linear | 3 => some .unrestricted | _ => none

theorem quantityOfTag_quantityTag (quantity : Quantity) :
    quantityOfTag (quantityTag quantity) = some quantity := by
  cases quantity <;> rfl

/-- `Reuse` as a one-byte-tag stream (via the natural codec). -/
def reuseStream : StreamCodec Reuse where
  encode reuse := StreamCodec.nat.encode (reuseTag reuse)
  decodePrefix bytes := do
    let (tag, suffix) ← StreamCodec.nat.decodePrefix bytes
    let reuse ← reuseOfTag tag
    pure (reuse, suffix)
  decodePrefix_encode := by
    intro reuse suffix
    simp [StreamCodec.decodePrefix_encode, reuseOfTag_reuseTag]

def quantityStream : StreamCodec Quantity where
  encode quantity := StreamCodec.nat.encode (quantityTag quantity)
  decodePrefix bytes := do
    let (tag, suffix) ← StreamCodec.nat.decodePrefix bytes
    let quantity ← quantityOfTag tag
    pure (quantity, suffix)
  decodePrefix_encode := by
    intro quantity suffix
    simp [StreamCodec.decodePrefix_encode, quantityOfTag_quantityTag]

def encodeTy : Ty → Tokens
  | .natural => [.nat 0]
  | .label => [.nat 1]
  | .boolean => [.nat 2]
  | .variable index => [.nat 3, .nat index]
  | .arrow reuse quantity domain codomain =>
      .nat 4 :: .nat (reuseTag reuse) :: .nat (quantityTag quantity) :: (encodeTy domain ++ encodeTy codomain)
  | .emptyRow => [.nat 5]
  | .field name member tail => .nat 6 :: .text name :: (encodeTy member ++ encodeTy tail)
  | .specification metadata extension => .nat 7 :: (encodeTy metadata ++ encodeTy extension)
  | .prototype specification target => .nat 8 :: (encodeTy specification ++ encodeTy target)
  | .custody identity => [.nat 9, .nat identity]
  | .variant row => .nat 10 :: encodeTy row
  | .computation plan response result => .nat 11 :: (encodeTy plan ++ encodeTy response ++ encodeTy result)

def decodeTy : Nat → Tokens → Option (Ty × Tokens)
  | 0, _ => none
  | _ + 1, .nat 0 :: rest => some (.natural, rest)
  | _ + 1, .nat 1 :: rest => some (.label, rest)
  | _ + 1, .nat 2 :: rest => some (.boolean, rest)
  | _ + 1, .nat 3 :: .nat index :: rest => some (.variable index, rest)
  | fuel + 1, .nat 4 :: .nat reuse :: .nat quantity :: rest => do
      let reuse ← reuseOfTag reuse
      let quantity ← quantityOfTag quantity
      let (domain, rest) ← decodeTy fuel rest
      let (codomain, rest) ← decodeTy fuel rest
      pure (.arrow reuse quantity domain codomain, rest)
  | _ + 1, .nat 5 :: rest => some (.emptyRow, rest)
  | fuel + 1, .nat 6 :: .text name :: rest => do
      let (member, rest) ← decodeTy fuel rest
      let (tail, rest) ← decodeTy fuel rest
      pure (.field name member tail, rest)
  | fuel + 1, .nat 7 :: rest => do
      let (metadata, rest) ← decodeTy fuel rest
      let (extension, rest) ← decodeTy fuel rest
      pure (.specification metadata extension, rest)
  | fuel + 1, .nat 8 :: rest => do
      let (specification, rest) ← decodeTy fuel rest
      let (target, rest) ← decodeTy fuel rest
      pure (.prototype specification target, rest)
  | _ + 1, .nat 9 :: .nat identity :: rest => some (.custody identity, rest)
  | fuel + 1, .nat 10 :: rest => do
      let (row, rest) ← decodeTy fuel rest
      pure (.variant row, rest)
  | fuel + 1, .nat 11 :: rest => do
      let (plan, rest) ← decodeTy fuel rest
      let (response, rest) ← decodeTy fuel rest
      let (result, rest) ← decodeTy fuel rest
      pure (.computation plan response result, rest)
  | _ + 1, _ => none

theorem decodeTy_encodeTy (type : Ty) : ∀ (fuel : Nat) (rest : Tokens),
    (encodeTy type).length ≤ fuel → decodeTy fuel (encodeTy type ++ rest) = some (type, rest) := by
  induction type with
  | natural | label | boolean | emptyRow =>
      intro fuel rest h; cases fuel with
      | zero => simp [encodeTy] at h
      | succ fuel => simp [encodeTy, decodeTy]
  | «variable» index | custody identity =>
      intro fuel rest h; cases fuel with
      | zero => simp [encodeTy] at h
      | succ fuel => simp [encodeTy, decodeTy]
  | arrow reuse quantity domain codomain ihd ihc =>
      intro fuel rest h; cases fuel with
      | zero => simp [encodeTy] at h
      | succ fuel =>
          simp only [encodeTy, List.length_cons, List.length_append] at h
          simp [encodeTy, decodeTy, List.append_assoc, reuseOfTag_reuseTag, quantityOfTag_quantityTag,
            ihd fuel _ (by omega), ihc fuel rest (by omega)]
  | field name member tail ihm iht =>
      intro fuel rest h; cases fuel with
      | zero => simp [encodeTy] at h
      | succ fuel =>
          simp only [encodeTy, List.length_cons, List.length_append] at h
          simp [encodeTy, decodeTy, List.append_assoc, ihm fuel _ (by omega), iht fuel rest (by omega)]
  | specification metadata extension ihm ihe =>
      intro fuel rest h; cases fuel with
      | zero => simp [encodeTy] at h
      | succ fuel =>
          simp only [encodeTy, List.length_cons, List.length_append] at h
          simp [encodeTy, decodeTy, List.append_assoc, ihm fuel _ (by omega), ihe fuel rest (by omega)]
  | prototype specification target ihs iht =>
      intro fuel rest h; cases fuel with
      | zero => simp [encodeTy] at h
      | succ fuel =>
          simp only [encodeTy, List.length_cons, List.length_append] at h
          simp [encodeTy, decodeTy, List.append_assoc, ihs fuel _ (by omega), iht fuel rest (by omega)]
  | variant row ih =>
      intro fuel rest h; cases fuel with
      | zero => simp [encodeTy] at h
      | succ fuel =>
          simp only [encodeTy, List.length_cons] at h
          simp [encodeTy, decodeTy, ih fuel rest (by omega)]
  | computation plan response result ihp ihr ihs =>
      intro fuel rest h; cases fuel with
      | zero => simp [encodeTy] at h
      | succ fuel =>
          simp only [encodeTy, List.length_cons, List.length_append] at h
          simp [encodeTy, decodeTy, List.append_assoc, ihp fuel _ (by omega), ihr fuel _ (by omega),
            ihs fuel rest (by omega)]

/-- A type as one prefix stream: its token list. -/
def tyStream : StreamCodec Ty where
  encode type := tokensStream.encode (encodeTy type)
  decodePrefix bytes := do
    let (tokens, suffix) ← tokensStream.decodePrefix bytes
    let (type, rest) ← decodeTy (tokens.length + 1) tokens
    if rest.isEmpty then some (type, suffix) else none
  decodePrefix_encode := by
    intro type suffix
    have decoded := decodeTy_encodeTy type ((encodeTy type).length + 1) [] (by omega)
    rw [List.append_nil] at decoded
    simp [StreamCodec.decodePrefix_encode, decoded]

def tyBytes (type : Ty) : Bytes := tyStream.encode type

/-- Strict: the decoded type re-encodes to exactly these bytes. -/
def decodeTyBytes (bytes : Bytes) : Option Ty := do
  let (type, suffix) ← tyStream.decodePrefix bytes
  if suffix.isEmpty && tyBytes type == bytes then some type else none

theorem ty_roundTrip (type : Ty) : decodeTyBytes (tyBytes type) = some type := by
  have decoded := tyStream.decodePrefix_encode type []
  rw [List.append_nil] at decoded
  simp [decodeTyBytes, tyBytes, decoded]

theorem decodeTyBytes_canonical {bytes : Bytes} {type : Ty} (decoded : decodeTyBytes bytes = some type) :
    tyBytes type = bytes := by
  unfold decodeTyBytes at decoded
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at decoded
  obtain ⟨⟨type', suffix⟩, _, check⟩ := decoded
  split at check
  · rename_i ok
    cases Option.some.inj check
    simp only [Bool.and_eq_true, beq_iff_eq] at ok
    exact ok.2
  · cases check

/-! ## Declared-state typing -/

/-- The value a record holds at `name` (the first such field). -/
def lookupField (fields : List (String × Data)) (name : String) : Option Data :=
  (fields.find? (fun field => field.1 == name)).map Prod.snd

/-- The record without every field named `name`. -/
def withoutField (fields : List (String × Data)) (name : String) : List (String × Data) :=
  fields.filter (fun field => field.1 != name)

/-- How many fields are named `name`. -/
def countField (fields : List (String × Data)) (name : String) : Nat :=
  fields.countP (fun field => field.1 == name)

mutual
/-- **A value typed at a first-order declared type**, structurally (closed records,
closed sums; see the module docstring). -/
def typedAt : Ty → Data → Bool
  | .natural, .natural _ => true
  | .boolean, .boolean _ => true
  | .label, .label _ => true
  | .emptyRow, .record fields => fields.isEmpty
  | .field name member tail, .record fields =>
      countField fields name == 1 &&
        (match lookupField fields name with
          | some value => typedAt member value
          | none => false) &&
        typedAt tail (.record (withoutField fields name))
  | .variant row, .variant label payload => caseTyped row label payload
  | _, _ => false
/-- The first case of `row` named `label` types `payload`. -/
def caseTyped : Ty → String → Data → Bool
  | .field name member tail, label, payload =>
      if name == label then typedAt member payload else caseTyped tail label payload
  | _, _, _ => false
end

/-- The first field of a row named `name`, and the row without it. -/
def takeField : Ty → String → Option (Ty × Ty)
  | .field key member tail, name =>
      if key == name then some (member, tail)
      else (takeField tail name).map fun taken => (taken.1, .field key member taken.2)
  | _, _ => none

/-- The first case of a sum row named `name`. -/
def caseOf : Ty → String → Option Ty
  | .field key member tail, name => if key == name then some member else caseOf tail name
  | _, _ => none

mutual
/-- **Value subtyping** on first-order types (see the module docstring). -/
def stateSubtype : Ty → Ty → Bool
  | .natural, .natural => true
  | .boolean, .boolean => true
  | .label, .label => true
  | .emptyRow, .emptyRow => true
  | .field name member tail, other =>
      match takeField other name with
      | some (member', rest) => stateSubtype member member' && stateSubtype tail rest
      | none => false
  | .variant row, .variant row' => casesSub row row'
  | _, _ => false
/-- Every case of `row` is a case of `row'` (its first one of that name) with a
payload subtype. -/
def casesSub : Ty → Ty → Bool
  | .field name member tail, row' =>
      (match caseOf row' name with
        | some member' => stateSubtype member member'
        | none => false) && casesSub tail row'
  | .emptyRow, _ => true
  | _, _ => false
end

/-! ### Soundness of the subtype -/

theorem countField_without (fields : List (String × Data)) {key name : String} (distinct : key ≠ name) :
    countField (withoutField fields key) name = countField fields name := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
      unfold countField withoutField at *
      by_cases hk : field.1 = key
      · have hn : field.1 ≠ name := fun h => distinct (hk ▸ h)
        simp [hk, ih, distinct]
      · simp [List.countP_cons, hk, ih]

theorem lookupField_without (fields : List (String × Data)) {key name : String} (distinct : key ≠ name) :
    lookupField (withoutField fields key) name = lookupField fields name := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
      unfold lookupField withoutField at *
      by_cases hk : field.1 = key
      · have hn : field.1 ≠ name := fun h => distinct (hk ▸ h)
        rw [List.filter_cons_of_neg (by simp [hk]), ih, List.find?_cons_of_neg (by simp [hn])]
      · rw [List.filter_cons_of_pos (by simp [hk])]
        by_cases hn : field.1 = name
        · rw [List.find?_cons_of_pos (by simp [hn]), List.find?_cons_of_pos (by simp [hn])]
        · rw [List.find?_cons_of_neg (by simp [hn]), List.find?_cons_of_neg (by simp [hn]), ih]

theorem withoutField_comm (fields : List (String × Data)) (one two : String) :
    withoutField (withoutField fields one) two = withoutField (withoutField fields two) one := by
  simp only [withoutField, List.filter_filter]
  congr 1
  funext field
  exact Bool.and_comm _ _

/-- Typing a record at a row whose field `name` is taken: the field, then the rest. -/
theorem typedAt_takeField (row : Ty) (name : String) (member rest : Ty)
    (taken : takeField row name = some (member, rest)) (fields : List (String × Data)) :
    typedAt row (.record fields) =
      (countField fields name == 1 &&
        (match lookupField fields name with
          | some value => typedAt member value
          | none => false) &&
        typedAt rest (.record (withoutField fields name))) := by
  induction row generalizing member rest fields with
  | field key keyMember tail _ ihTail =>
      by_cases same : key = name
      · subst same
        simp only [takeField, beq_self_eq_true, if_true, Option.some.injEq, Prod.mk.injEq] at taken
        obtain ⟨hm, hr⟩ := taken
        subst hm; subst hr
        simp [typedAt]
      · have keyName : (key == name) = false := by simpa using same
        simp only [takeField, keyName, Bool.false_eq_true, if_false, Option.map_eq_some_iff] at taken
        obtain ⟨⟨member', rest'⟩, inner, pair⟩ := taken
        simp only [Prod.mk.injEq] at pair
        obtain ⟨hm, hr⟩ := pair
        subst hm; subst hr
        have ih := ihTail member' rest' inner (withoutField fields key)
        simp only [typedAt]
        rw [ih, countField_without fields same, lookupField_without fields same,
          countField_without fields (Ne.symm same), lookupField_without fields (Ne.symm same),
          withoutField_comm fields key name]
        simp only [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
  | _ => simp [takeField] at taken

theorem caseTyped_caseOf (row : Ty) (label : String) (member : Ty) (found : caseOf row label = some member)
    (payload : Data) : caseTyped row label payload = typedAt member payload := by
  induction row with
  | field key keyMember tail _ ihTail =>
      by_cases same : key = label
      · subst same
        simp only [caseOf, beq_self_eq_true, if_true, Option.some.injEq] at found
        subst found
        simp [caseTyped]
      · have keyLabel : (key == label) = false := by simpa using same
        simp only [caseOf, keyLabel, Bool.false_eq_true, if_false] at found
        simp [caseTyped, keyLabel, ihTail found]
  | _ => simp [caseOf] at found

/-- Both halves of soundness, by induction on the smaller type. -/
theorem subtype_sound (smaller : Ty) :
    (∀ (larger : Ty) (value : Data), stateSubtype smaller larger = true →
      typedAt smaller value = true → typedAt larger value = true) ∧
    (∀ (row' : Ty) (label : String) (payload : Data), casesSub smaller row' = true →
      caseTyped smaller label payload = true → caseTyped row' label payload = true) := by
  induction smaller with
  | natural =>
      refine ⟨fun larger value sub typed => ?_, fun _ _ _ sub _ => by simp [casesSub] at sub⟩
      cases larger <;> simp [stateSubtype] at sub
      exact typed
  | boolean =>
      refine ⟨fun larger value sub typed => ?_, fun _ _ _ sub _ => by simp [casesSub] at sub⟩
      cases larger <;> simp [stateSubtype] at sub
      exact typed
  | label =>
      refine ⟨fun larger value sub typed => ?_, fun _ _ _ sub _ => by simp [casesSub] at sub⟩
      cases larger <;> simp [stateSubtype] at sub
      exact typed
  | emptyRow =>
      refine ⟨fun larger value sub typed => ?_, fun _ _ _ _ typed => by simp [caseTyped] at typed⟩
      cases larger <;> simp [stateSubtype] at sub
      exact typed
  | field name member tail ihMember ihTail =>
      refine ⟨fun larger value sub typed => ?_, fun row' label payload sub typed => ?_⟩
      · simp only [stateSubtype] at sub
        split at sub
        · rename_i member' rest taken
          simp only [Bool.and_eq_true] at sub
          cases value with
          | record fields =>
              rw [typedAt_takeField larger name member' rest taken fields]
              simp only [typedAt, Bool.and_eq_true] at typed
              obtain ⟨⟨count, found⟩, restTyped⟩ := typed
              simp only [Bool.and_eq_true]
              refine ⟨⟨count, ?_⟩, ihTail.1 rest _ sub.2 restTyped⟩
              cases hl : lookupField fields name with
              | none => rw [hl] at found; cases found
              | some value => rw [hl] at found; exact ihMember.1 member' value sub.1 found
          | _ => simp [typedAt] at typed
        · cases sub
      · simp only [casesSub, Bool.and_eq_true] at sub
        obtain ⟨here, later⟩ := sub
        by_cases same : name = label
        · subst same
          simp only [caseTyped, beq_self_eq_true, if_true] at typed
          split at here
          · rename_i member' found
            rw [caseTyped_caseOf row' name member' found]
            exact ihMember.1 member' payload here typed
          · cases here
        · have nameLabel : (name == label) = false := by simpa using same
          simp only [caseTyped, nameLabel, Bool.false_eq_true, if_false] at typed
          exact ihTail.2 row' label payload later typed
  | variant row ihRow =>
      refine ⟨fun larger value sub typed => ?_, fun _ _ _ sub _ => by simp [casesSub] at sub⟩
      cases larger with
      | variant row' =>
          simp only [stateSubtype] at sub
          cases value with
          | variant label payload =>
              simp only [typedAt] at typed ⊢
              exact ihRow.2 row' label payload sub typed
          | _ => simp [typedAt] at typed
      | _ => simp [stateSubtype] at sub
  | _ =>
      refine ⟨fun larger value sub _ => ?_, fun _ _ _ sub _ => by simp [casesSub] at sub⟩
      cases larger <;> simp [stateSubtype] at sub

/-- **A subtype's values are the supertype's values.** -/
theorem typedAt_of_stateSubtype {smaller larger : Ty} (sub : stateSubtype smaller larger = true)
    {value : Data} (typed : typedAt smaller value = true) : typedAt larger value = true :=
  (subtype_sound smaller).1 larger value sub typed

/-! ### Teeth -/

/-- The Tally's declared state `{total : Nat}`. -/
def tallyState : Ty := .field "total" .natural .emptyRow

theorem tally_typed : typedAt tallyState (.record [("total", .natural 3)]) = true := by decide
theorem tally_extra_field_refused :
    typedAt tallyState (.record [("total", .natural 3), ("extra", .natural 0)]) = false := by decide
theorem tally_missing_field_refused : typedAt tallyState (.record []) = false := by decide
theorem tally_repeated_field_refused :
    typedAt tallyState (.record [("total", .natural 3), ("total", .natural 4)]) = false := by decide
/-- Adding a record field is NOT a value subtype (records are closed). -/
theorem added_field_not_subtype :
    stateSubtype tallyState (.field "total" .natural (.field "upgrades" .natural .emptyRow)) = false := by decide
/-- Reordering a closed record's fields is. -/
theorem reordered_subtype :
    stateSubtype (.field "a" .natural (.field "b" .boolean .emptyRow))
      (.field "b" .boolean (.field "a" .natural .emptyRow)) = true := by decide
/-- Adding a sum case is. -/
theorem added_case_subtype :
    stateSubtype (.variant (.field "on" (.field "level" .natural .emptyRow) .emptyRow))
      (.variant (.field "on" (.field "level" .natural .emptyRow) (.field "off" .emptyRow .emptyRow))) = true := by
  decide
/-- An arrow is never a state subtype. -/
theorem arrow_not_subtype :
    stateSubtype (.arrow .reusable .unrestricted .natural .natural)
      (.arrow .reusable .unrestricted .natural .natural) = false := by decide
theorem tallyState_roundTrip : decodeTyBytes (tyBytes tallyState) = some tallyState := ty_roundTrip _

#assert_axioms reuseOfTag_reuseTag
#assert_axioms quantityOfTag_quantityTag
#assert_axioms decodeTy_encodeTy
#assert_axioms ty_roundTrip
#assert_axioms decodeTyBytes_canonical
#assert_axioms typedAt_takeField
#assert_axioms caseTyped_caseOf
#assert_axioms subtype_sound
#assert_axioms typedAt_of_stateSubtype
#assert_axioms tally_typed
#assert_axioms tally_extra_field_refused
#assert_axioms tally_missing_field_refused
#assert_axioms tally_repeated_field_refused
#assert_axioms added_field_not_subtype
#assert_axioms reordered_subtype
#assert_axioms added_case_subtype
#assert_axioms arrow_not_subtype
end Minidregg.Kernel.ObjectStateType
