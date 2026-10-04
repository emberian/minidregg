/- Lexical invariants for the partial Objective Bend edition. These proofs do
not assert totality, ownership of native effects, or source/heap adequacy. -/
import Theory.ObjectiveBendDemandMachine
namespace Minidregg.Theory.ObjectiveBendDemandInvariant
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
set_option autoImplicit false

/-- All free indices have lexical bindings. A successor branch binds the
predecessor; a lambda binds its argument. Recursive self is bound by the heap
machine, rather than counted as a free index of the source Fix constructor. -/
inductive Scoped : Nat → Term → Prop where
  | bound {n i : Nat} : i < n → Scoped n (.bound i)
  | lam {n : Nat} {body : Term} : Scoped (n+1) body → Scoped n (.lam body)
  | app {n : Nat} {f a : Term} : Scoped n f → Scoped n a → Scoped n (.app f a)
  | mix {n : Nat} {a b : Term} : Scoped n a → Scoped n b → Scoped n (.mix a b)
  | fix {n : Nat} {a b : Term} : Scoped n a → Scoped n b → Scoped n (.fix a b)
  | specification {n : Nat} {a b : Term} : Scoped n a → Scoped n b → Scoped n (.specification a b)
  | prototype {n : Nat} {a b : Term} : Scoped n a → Scoped n b → Scoped n (.prototype a b)
  | reflect {n : Nat} {t : Term} : Scoped n t → Scoped n (.reflect t)
  | metadata {n : Nat} {t : Term} : Scoped n t → Scoped n (.metadata t)
  | project {n : Nat} {t : Term} : Scoped n t → Scoped n (.project t)
  | natural {n : Nat} (v : Nat) : Scoped n (.nat v)
  | boolean {n : Nat} (v : Bool) : Scoped n (.boolean v)
  | label {n : Nat} (v : String) : Scoped n (.label v)
  | binary {n : Nat} {p : Primitive} {a b : Term} : Scoped n a → Scoped n b → Scoped n (.binary p a b)
  | extend {n : Nat} {t : Term} {fs : List (String × Term)} :
      Scoped n t → (∀ f ∈ fs, Scoped n f.2) → Scoped n (.extend t fs)
  | record {n : Nat} {fs : List (String × Term)} :
      (∀ f ∈ fs, Scoped n f.2) → Scoped n (.record fs)
  | get {n : Nat} {t : Term} {name : String} : Scoped n t → Scoped n (.get t name)
  | condition {n : Nat} {t z s : Term} : Scoped n t → Scoped n z → Scoped (n+1) s → Scoped n (.ifZero t z s)
  | inject {n : Nat} {tag : String} {p : Term} : Scoped n p → Scoped n (.inject tag p)
  | case {n : Nat} {t : Term} {arms : List (String × Term)} :
      Scoped n t → (∀ arm ∈ arms, Scoped (n+1) arm.2) → Scoped n (.case t arms)
  | ifBool {n : Nat} {c t f : Term} : Scoped n c → Scoped n t → Scoped n f → Scoped n (.ifBool c t f)

@[simp] theorem scoped_bound_iff (n : Nat) (i : Nat) :
    Scoped n (.bound i) ↔ i < n := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .bound h

@[simp] theorem scoped_lam_iff (n : Nat) (body : Term) :
    Scoped n (.lam body) ↔ Scoped (n+1) body := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .lam h

@[simp] theorem scoped_app_iff (n : Nat) (a b : Term) :
    Scoped n (.app a b) ↔ Scoped n a ∧ Scoped n b := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · intro h; exact .app h.1 h.2

@[simp] theorem scoped_mix_iff (n : Nat) (a b : Term) :
    Scoped n (.mix a b) ↔ Scoped n a ∧ Scoped n b := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · intro h; exact .mix h.1 h.2

@[simp] theorem scoped_fix_iff (n : Nat) (a b : Term) :
    Scoped n (.fix a b) ↔ Scoped n a ∧ Scoped n b := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · intro h; exact .fix h.1 h.2

@[simp] theorem scoped_specification_iff (n : Nat) (a b : Term) :
    Scoped n (.specification a b) ↔ Scoped n a ∧ Scoped n b := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · intro h; exact .specification h.1 h.2

@[simp] theorem scoped_prototype_iff (n : Nat) (a b : Term) :
    Scoped n (.prototype a b) ↔ Scoped n a ∧ Scoped n b := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · intro h; exact .prototype h.1 h.2

@[simp] theorem scoped_reflect_iff (n : Nat) (body : Term) :
    Scoped n (.reflect body) ↔ Scoped n body := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .reflect h

@[simp] theorem scoped_metadata_iff (n : Nat) (body : Term) :
    Scoped n (.metadata body) ↔ Scoped n body := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .metadata h

@[simp] theorem scoped_project_iff (n : Nat) (body : Term) :
    Scoped n (.project body) ↔ Scoped n body := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .project h

@[simp] theorem scoped_binary_iff (n : Nat) (p : Primitive) (a b : Term) :
    Scoped n (.binary p a b) ↔ Scoped n a ∧ Scoped n b := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · intro h; exact .binary h.1 h.2

@[simp] theorem scoped_extend_iff (n : Nat) (body : Term) (fields : List (String × Term)) :
    Scoped n (.extend body fields) ↔ Scoped n body ∧ ∀ field ∈ fields, Scoped n field.2 := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · intro h; exact .extend h.1 h.2

@[simp] theorem scoped_record_iff (n : Nat) (fields : List (String × Term)) :
    Scoped n (.record fields) ↔ ∀ field ∈ fields, Scoped n field.2 := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .record h

@[simp] theorem scoped_get_iff (n : Nat) (body : Term) (name : String) :
    Scoped n (.get body name) ↔ Scoped n body := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .get h

@[simp] theorem scoped_condition_iff (n : Nat) (v z b : Term) :
    Scoped n (.ifZero v z b) ↔ Scoped n v ∧ Scoped n z ∧ Scoped (n+1) b := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption,by assumption⟩
  · intro h; exact .condition h.1 h.2.1 h.2.2

@[simp] theorem scoped_inject_iff (n : Nat) (tag : String) (p : Term) :
    Scoped n (.inject tag p) ↔ Scoped n p := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .inject h

@[simp] theorem scoped_case_iff (n : Nat) (t : Term) (arms : List (String × Term)) :
    Scoped n (.case t arms) ↔ Scoped n t ∧ ∀ arm ∈ arms, Scoped (n+1) arm.2 := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · intro h; exact .case h.1 h.2

@[simp] theorem scoped_ifBool_iff (n : Nat) (c t f : Term) :
    Scoped n (.ifBool c t f) ↔ Scoped n c ∧ Scoped n t ∧ Scoped n f := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption,by assumption⟩
  · intro h; exact .ifBool h.1 h.2.1 h.2.2

 theorem scoped_rename {n : Nat} {t : Term} (h : Scoped n t)
    (f : Nat → Nat) (m : Nat) (hf : ∀ i, i < n → f i < m) :
    Scoped m (t.rename f) := by
  induction h generalizing m f with
  | bound hi =>
      simp only [Term.rename]
      exact .bound (hf _ hi)
  | lam h ih =>
      simp only [Term.rename]

      apply Scoped.lam
      apply ih (liftRename f) (m+1)
      intro i hi
      cases i with
      | zero => simp [liftRename]
      | succ i => simp only [liftRename]; exact Nat.succ_lt_succ (hf i (Nat.lt_of_succ_lt_succ hi))
  | app _ _ ih₁ ih₂ =>
      simp only [Term.rename]
      exact .app (ih₁ f m hf) (ih₂ f m hf)
  | mix _ _ ih₁ ih₂ =>
      simp only [Term.rename]
      exact .mix (ih₁ f m hf) (ih₂ f m hf)
  | fix _ _ ih₁ ih₂ =>
      simp only [Term.rename]
      exact .fix (ih₁ f m hf) (ih₂ f m hf)
  | specification _ _ ih₁ ih₂ =>
      simp only [Term.rename]
      exact .specification (ih₁ f m hf) (ih₂ f m hf)
  | prototype _ _ ih₁ ih₂ =>
      simp only [Term.rename]
      exact .prototype (ih₁ f m hf) (ih₂ f m hf)
  | reflect _ ih =>
      simp only [Term.rename]
      exact .reflect (ih f m hf)
  | metadata _ ih =>
      simp only [Term.rename]
      exact .metadata (ih f m hf)
  | project _ ih =>
      simp only [Term.rename]
      exact .project (ih f m hf)
  | natural v =>
      simp only [Term.rename]
      exact .natural v
  | boolean v =>
      simp only [Term.rename]
      exact .boolean v
  | label v =>
      simp only [Term.rename]
      exact .label v
  | binary _ _ ih₁ ih₂ =>
      simp only [Term.rename]
      exact .binary (ih₁ f m hf) (ih₂ f m hf)
  | extend _ _ ih₁ ih₂ =>
      simp only [Term.rename]

      apply Scoped.extend (ih₁ f m hf)
      intro field member
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp member
      exact ih₂ original ho f m hf
  | record _ ih =>
      simp only [Term.rename]

      apply Scoped.record
      intro field member
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp member
      exact ih original ho f m hf
  | get _ ih =>
      simp only [Term.rename]
      exact .get (ih f m hf)
  | condition _ _ _ ih₁ ih₂ ih₃ =>
      simp only [Term.rename]

      apply Scoped.condition (ih₁ f m hf) (ih₂ f m hf)
      apply ih₃ (liftRename f) (m+1)
      intro i hi
      cases i with
      | zero => simp [liftRename]
      | succ i => simp only [liftRename]; exact Nat.succ_lt_succ (hf i (Nat.lt_of_succ_lt_succ hi))
  | inject _ ih =>
      simp only [Term.rename]
      exact .inject (ih f m hf)
  | case _ _ ih₁ ih₂ =>
      simp only [Term.rename]
      apply Scoped.case (ih₁ f m hf)
      intro arm member
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp member
      apply ih₂ original ho (liftRename f) (m+1)
      intro i hi
      cases i with
      | zero => simp [liftRename]
      | succ i => simp only [liftRename]; exact Nat.succ_lt_succ (hf i (Nat.lt_of_succ_lt_succ hi))
  | ifBool _ _ _ ih₁ ih₂ ih₃ =>
      simp only [Term.rename]
      exact .ifBool (ih₁ f m hf) (ih₂ f m hf) (ih₃ f m hf)

 theorem scoped_weaken {n : Nat} {t : Term} (h : Scoped n t) :
    Scoped (n+1) (t.rename Nat.succ) :=
  scoped_rename h Nat.succ (n+1) (fun _ hi => Nat.succ_lt_succ hi)

 theorem scoped_substitute {n : Nat} {t : Term} (h : Scoped n t)
    (substitution : Nat → Term) (m : Nat)
    (hs : ∀ i, i < n → Scoped m (substitution i)) : Scoped m (t.substitute substitution) := by
  induction h generalizing m substitution with
  | bound hi =>
      simp only [Term.substitute]
      exact hs _ hi
  | lam h ih =>
      simp only [Term.substitute]

      apply Scoped.lam
      apply ih (liftSubstitution substitution) (m+1)
      intro i hi
      cases i with
      | zero => exact .bound (Nat.zero_lt_succ _)
      | succ i => exact scoped_weaken (hs i (Nat.lt_of_succ_lt_succ hi))
  | app _ _ ih₁ ih₂ =>
      simp only [Term.substitute]
      exact .app (ih₁ substitution m hs) (ih₂ substitution m hs)
  | mix _ _ ih₁ ih₂ =>
      simp only [Term.substitute]
      exact .mix (ih₁ substitution m hs) (ih₂ substitution m hs)
  | fix _ _ ih₁ ih₂ =>
      simp only [Term.substitute]
      exact .fix (ih₁ substitution m hs) (ih₂ substitution m hs)
  | specification _ _ ih₁ ih₂ =>
      simp only [Term.substitute]
      exact .specification (ih₁ substitution m hs) (ih₂ substitution m hs)
  | prototype _ _ ih₁ ih₂ =>
      simp only [Term.substitute]
      exact .prototype (ih₁ substitution m hs) (ih₂ substitution m hs)
  | reflect _ ih =>
      simp only [Term.substitute]
      exact .reflect (ih substitution m hs)
  | metadata _ ih =>
      simp only [Term.substitute]
      exact .metadata (ih substitution m hs)
  | project _ ih =>
      simp only [Term.substitute]
      exact .project (ih substitution m hs)
  | natural v =>
      simp only [Term.substitute]
      exact .natural v
  | boolean v =>
      simp only [Term.substitute]
      exact .boolean v
  | label v =>
      simp only [Term.substitute]
      exact .label v
  | binary _ _ ih₁ ih₂ =>
      simp only [Term.substitute]
      exact .binary (ih₁ substitution m hs) (ih₂ substitution m hs)
  | extend _ _ ih₁ ih₂ =>
      simp only [Term.substitute]

      apply Scoped.extend (ih₁ substitution m hs)
      intro field member
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp member
      exact ih₂ original ho substitution m hs
  | record _ ih =>
      simp only [Term.substitute]

      apply Scoped.record
      intro field member
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp member
      exact ih original ho substitution m hs
  | get _ ih =>
      simp only [Term.substitute]
      exact .get (ih substitution m hs)
  | condition _ _ _ ih₁ ih₂ ih₃ =>
      simp only [Term.substitute]

      apply Scoped.condition (ih₁ substitution m hs) (ih₂ substitution m hs)
      apply ih₃ (liftSubstitution substitution) (m+1)
      intro i hi
      cases i with
      | zero => exact .bound (Nat.zero_lt_succ _)
      | succ i => exact scoped_weaken (hs i (Nat.lt_of_succ_lt_succ hi))
  | inject _ ih =>
      simp only [Term.substitute]
      exact .inject (ih substitution m hs)
  | case _ _ ih₁ ih₂ =>
      simp only [Term.substitute]
      apply Scoped.case (ih₁ substitution m hs)
      intro arm member
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp member
      apply ih₂ original ho (liftSubstitution substitution) (m+1)
      intro i hi
      cases i with
      | zero => exact .bound (Nat.zero_lt_succ _)
      | succ i => exact scoped_weaken (hs i (Nat.lt_of_succ_lt_succ hi))
  | ifBool _ _ _ ih₁ ih₂ ih₃ =>
      simp only [Term.substitute]
      exact .ifBool (ih₁ substitution m hs) (ih₂ substitution m hs) (ih₃ substitution m hs)

 theorem scoped_mixBody {n : Nat} {lower upper : Term}
    (hl : Scoped n lower) (hu : Scoped n upper) : Scoped n (mixBody lower upper) := by
  apply Scoped.lam
  apply Scoped.lam
  apply Scoped.app
  · exact .app (scoped_rename hu (fun i => i+2) (n+1+1)
      (fun i hi => Nat.add_lt_add_right hi 2)) (.bound (by omega))
  · exact .app (.app (scoped_rename hl (fun i => i+2) (n+1+1)
      (fun i hi => Nat.add_lt_add_right hi 2)) (.bound (by omega))) (.bound (by omega))

/-- Unlike a tree-unfolding predicate, this permits a thunk to capture itself
and permits mutually reachable cells. It only requires allocated addresses. -/
def EnvironmentValid (bound : Nat) (environment : Environment) : Prop :=
  ∀ address ∈ environment, address < bound

def RuntimeValueValid (bound : Nat) : RuntimeValue → Prop
  | .closure body environment => Scoped (environment.length+1) body ∧ EnvironmentValid bound environment
  | .natural _ | .boolean _ | .label _ => True
  | .record fields => ∀ field ∈ fields, field.2 < bound
  | .specification metadata extension => metadata < bound ∧ extension < bound
  | .prototype specification target => specification < bound ∧ target < bound
  | .variant _ payload => payload < bound

 theorem environmentValid_mono {a b : Nat} {environment : Environment}
    (h : EnvironmentValid a environment) (hab : a ≤ b) : EnvironmentValid b environment :=
  fun address member => Nat.lt_of_lt_of_le (h address member) hab

 theorem environmentValid_tied {bound : Nat} {environment : Environment}
    (h : EnvironmentValid bound environment) : EnvironmentValid (bound+1) (bound::environment) := by
  intro address member
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact Nat.lt_succ_self _
  · exact Nat.lt_succ_of_lt (h address member)

def ClosureValid (bound : Nat) (closure : Closure) : Prop :=
  Scoped closure.environment.length closure.term ∧ EnvironmentValid bound closure.environment

def CellValid (bound : Nat) : Cell → Prop
  | .suspended origin | .evaluating origin => ClosureValid bound origin
  | .cached origin value => ClosureValid bound origin ∧ RuntimeValueValid bound value

def FrameValid (bound : Nat) : Frame → Prop
  | .argument term environment | .binaryLeft _ term environment => ClosureValid bound ⟨term,environment⟩
  | .update address => address < bound
  | .field _ | .reflect | .metadata | .project => True
  | .extend fields environment => EnvironmentValid bound environment ∧ ∀ field ∈ fields, Scoped environment.length field.2
  | .condition zero successorBody environment => EnvironmentValid bound environment ∧
      Scoped environment.length zero ∧ Scoped (environment.length+1) successorBody
  | .binaryRight _ value => RuntimeValueValid bound value
  | .case arms environment => EnvironmentValid bound environment ∧
      ∀ arm ∈ arms, Scoped (environment.length+1) arm.2
  | .ifBool whenTrue whenFalse environment => EnvironmentValid bound environment ∧
      Scoped environment.length whenTrue ∧ Scoped environment.length whenFalse

def ControlValid (bound : Nat) : Control → Prop
  | .evaluate term environment => ClosureValid bound ⟨term,environment⟩
  | .enter address | .blackhole address => address < bound
  | .returned value | .complete value => RuntimeValueValid bound value
  | .refused _ => True

def LexicalInvariant (state : State) : Prop :=
  (∀ (address : Nat) (cell : Cell), state.heap[address]? = some cell → CellValid state.heap.size cell) ∧
    ControlValid state.heap.size state.control ∧ ∀ frame ∈ state.stack, FrameValid state.heap.size frame

 theorem initial_lexicalInvariant {term : Term} (closed : Scoped 0 term) :
    LexicalInvariant (initial term) := by
  refine ⟨?_,⟨closed,?_⟩,?_⟩
  · intro address cell found; simp [initial] at found
  · intro address member; simp at member
  · intro frame member; simp [initial] at member

 theorem runtimeValueValid_mono {a b : Nat} {value : RuntimeValue}
    (h : RuntimeValueValid a value) (hab : a ≤ b) : RuntimeValueValid b value := by
  cases value with
  | closure body environment => exact ⟨h.1,environmentValid_mono h.2 hab⟩
  | natural _ | boolean _ | label _ => trivial
  | record fields => exact fun field member => Nat.lt_of_lt_of_le (h field member) hab
  | specification _ _ | prototype _ _ => exact ⟨Nat.lt_of_lt_of_le h.1 hab,Nat.lt_of_lt_of_le h.2 hab⟩
  | variant _ _ => exact Nat.lt_of_lt_of_le h hab

 theorem closureValid_mono {a b : Nat} {closure : Closure}
    (h : ClosureValid a closure) (hab : a ≤ b) : ClosureValid b closure :=
  ⟨h.1,environmentValid_mono h.2 hab⟩

 theorem cellValid_mono {a b : Nat} {cell : Cell}
    (h : CellValid a cell) (hab : a ≤ b) : CellValid b cell := by
  cases cell with
  | suspended _ | evaluating _ => exact closureValid_mono h hab
  | cached _ _ => exact ⟨closureValid_mono h.1 hab,runtimeValueValid_mono h.2 hab⟩

 theorem frameValid_mono {a b : Nat} {frame : Frame}
    (h : FrameValid a frame) (hab : a ≤ b) : FrameValid b frame := by
  cases frame with
  | argument _ _ | binaryLeft _ _ _ => exact closureValid_mono h hab
  | update _ => exact Nat.lt_of_lt_of_le h hab
  | field _ | reflect | metadata | project => trivial
  | extend _ _ => exact ⟨environmentValid_mono h.1 hab,h.2⟩
  | condition _ _ _ => exact ⟨environmentValid_mono h.1 hab,h.2⟩
  | binaryRight _ _ => exact runtimeValueValid_mono h hab
  | case _ _ => exact ⟨environmentValid_mono h.1 hab,h.2⟩
  | ifBool _ _ _ => exact ⟨environmentValid_mono h.1 hab,h.2⟩

 theorem controlValid_mono {a b : Nat} {control : Control}
    (h : ControlValid a control) (hab : a ≤ b) : ControlValid b control := by
  cases control with
  | evaluate _ _ => exact closureValid_mono h hab
  | enter _ | blackhole _ => exact Nat.lt_of_lt_of_le h hab
  | returned _ | complete _ => exact runtimeValueValid_mono h hab
  | refused _ => trivial

abbrev HeapValid (heap : Array Cell) : Prop :=
  ∀ (address : Nat) (cell : Cell), heap[address]? = some cell → CellValid heap.size cell

 theorem heapValid_push {heap : Array Cell} {cell : Cell} (h : HeapValid heap)
    (hc : CellValid (heap.size+1) cell) : HeapValid (heap.push cell) := by
  intro address value found
  rw [Array.getElem?_push] at found
  split at found
  · cases found; simpa using hc
  · exact cellValid_mono (h address value found) (by simp)

 theorem heapValid_set {heap : Array Cell} {address : Nat} {cell : Cell}
    (h : HeapValid heap) (hc : CellValid heap.size cell) : HeapValid (heap.set! address cell) := by
  intro index value found
  by_cases he : address < heap.size
  · by_cases same : index = address
    · subst index
      simp [Array.set!,Array.setIfInBounds,he] at found
      subst value; simpa [Array.set!] using hc
    · have old : heap[index]? = some value := by simpa [Array.set!,Array.setIfInBounds,he,same,Ne.symm same] using found
      simpa [Array.set!] using h index value old
  · simpa [Array.set!,Array.setIfInBounds,he] using h index value (by simpa [Array.set!,Array.setIfInBounds,he] using found)

 theorem allocateFields_valid {heap : Array Cell} {environment : Environment}
    {fields : List (String × Term)} (hh : HeapValid heap)
    (he : EnvironmentValid heap.size environment)
    (hf : ∀ field ∈ fields, Scoped environment.length field.2) :
    HeapValid (allocateFields heap environment fields).1 ∧
      ∀ field ∈ (allocateFields heap environment fields).2,
        field.2 < (allocateFields heap environment fields).1.size := by
  have loop : ∀ (fields : List (String × Term)) (pair : Array Cell × List (String × Address)),
      HeapValid pair.1 → EnvironmentValid pair.1.size environment →
      (∀ field ∈ pair.2, field.2 < pair.1.size) →
      (∀ field ∈ fields, Scoped environment.length field.2) →
      let result := fields.foldl (fun prior field =>
        (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2)) pair
      HeapValid result.1 ∧ ∀ field ∈ result.2, field.2 < result.1.size := by
    intro fs
    induction fs with
    | nil => intro pair hp he hr hs; exact ⟨hp,hr⟩
    | cons field fs ih =>
      intro pair hp he hr hs
      apply ih (pair.1.push (.suspended ⟨field.2,environment⟩),(field.1,pair.1.size)::pair.2)
      · apply heapValid_push hp
        exact ⟨hs field (by simp),environmentValid_mono he (by simp)⟩
      · exact environmentValid_mono he (by simp)
      · intro f member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · simp
        · exact Nat.lt_of_lt_of_le (hr f member) (by simp)
      · intro f member; exact hs f (by simp [member])
  obtain ⟨hp,hr⟩ := loop fields (heap,[]) hh he (by simp) hf
  refine ⟨hp,?_⟩
  intro f member
  exact hr f (List.mem_reverse.mp member)

 theorem allocateFields_cellValid {heap : Array Cell} {environment : Environment}
    {fields : List (String × Term)} (hh : HeapValid heap)
    (he : EnvironmentValid heap.size environment)
    (hf : ∀ field ∈ fields, Scoped environment.length field.2)
    (address : Nat) (cell : Cell) (found : (allocateFields heap environment fields).1[address]? = some cell) :
    CellValid (allocateFields heap environment fields).1.size cell :=
  (allocateFields_valid hh he hf).1 address cell found

 theorem allocateFields_addressValid {heap : Array Cell} {environment : Environment}
    {fields : List (String × Term)} (hh : HeapValid heap)
    (he : EnvironmentValid heap.size environment)
    (hf : ∀ field ∈ fields, Scoped environment.length field.2)
    (field : String × Address) (member : field ∈ (allocateFields heap environment fields).2) :
    field.2 < (allocateFields heap environment fields).1.size :=
  (allocateFields_valid hh he hf).2 field member

 theorem scalarValue_valid {term : Term} {value : RuntimeValue} (bound : Nat)
    (h : scalarValue term = some value) : RuntimeValueValid bound value := by
  cases term <;> simp [scalarValue] at h
  all_goals cases h; trivial

/-- Origin is lexical source plus capture vector, retained even while a cell is
being evaluated or after its result has been memoized. -/
def cellOrigin : Cell → Closure
  | .suspended origin | .evaluating origin | .cached origin _ => origin

/-- No transition can retarget an allocated thunk. This permits new allocations
and memoization; it forbids changing either its source or its lexical captures. -/
def PreservesOrigins (before after : Array Cell) : Prop :=
  before.size ≤ after.size ∧ ∀ (address : Nat) (cell : Cell), before[address]? = some cell →
    ∃ (next : Cell), after[address]? = some next ∧ cellOrigin next = cellOrigin cell

 theorem preservesOrigins_refl (heap : Array Cell) : PreservesOrigins heap heap :=
  ⟨Nat.le_refl _,fun _ cell found => ⟨cell,found,rfl⟩⟩

 theorem preservesOrigins_trans {a b c : Array Cell}
    (hab : PreservesOrigins a b) (hbc : PreservesOrigins b c) : PreservesOrigins a c := by
  constructor
  · exact Nat.le_trans hab.1 hbc.1
  · intro address cell found
    obtain ⟨middle, hm, ho⟩ := hab.2 address cell found
    obtain ⟨next, hn, hon⟩ := hbc.2 address middle hm
    exact ⟨next,hn,hon.trans ho⟩

 theorem preservesOrigins_push (heap : Array Cell) (cell : Cell) :
    PreservesOrigins heap (heap.push cell) := by
  constructor
  · simp
  · intro address original found
    have hbound : address < heap.size := by
      exact (Array.getElem?_eq_some_iff.mp found).1
    exact ⟨original,by simpa [Array.getElem?_push, Nat.ne_of_lt hbound] using found,rfl⟩

 theorem preservesOrigins_set {heap : Array Cell} {address : Nat} {old next : Cell}
    (found : heap[address]? = some old) (origin : cellOrigin next = cellOrigin old) :
    PreservesOrigins heap (heap.set! address next) := by
  have hbound : address < heap.size := (Array.getElem?_eq_some_iff.mp found).1
  constructor
  · simp [Array.set!]
  · intro index original hi
    by_cases same : index = address
    · subst index
      have eq : original = old := Option.some.inj (hi.symm.trans found)
      subst original
      exact ⟨next,by simp [Array.set!,hbound],origin⟩
    · exact ⟨original,by simpa [Array.set!,same,Ne.symm same] using hi,rfl⟩

 theorem allocateFields_preservesOrigins (heap : Array Cell) (environment : Environment)
    (fields : List (String × Term)) :
    PreservesOrigins heap (allocateFields heap environment fields).1 := by
  have loop : ∀ (fields : List (String × Term)) (pair : Array Cell × List (String × Address)),
      PreservesOrigins pair.1
        (fields.foldl (fun prior field => (prior.1.push (.suspended ⟨field.2,environment⟩),
          (field.1,prior.1.size)::prior.2)) pair).1 := by
    intro fields
    induction fields with
    | nil => intro pair; exact preservesOrigins_refl _
    | cons field fields ih =>
      intro pair
      simpa only [List.foldl_cons] using preservesOrigins_trans (preservesOrigins_push pair.1 (.suspended ⟨field.2,environment⟩)) (ih (pair.1.push (.suspended ⟨field.2,environment⟩),(field.1,pair.1.size)::pair.2))
  exact loop fields (heap,[])

 theorem allocateFields_size_mono (heap : Array Cell) (environment : Environment)
    (fields : List (String × Term)) : heap.size ≤ (allocateFields heap environment fields).1.size :=
  (allocateFields_preservesOrigins heap environment fields).1

/-- Every raw transition, including all terminal, refusal and blackhole cases,
preserves origin at every previously allocated address. No reachability or
adequacy oracle is a premise. -/
 theorem stepRaw_preservesOrigins (state : State) :
    PreservesOrigins state.heap (stepRaw state).heap := by
  unfold stepRaw
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals first
    | exact preservesOrigins_refl _
    | exact preservesOrigins_push _ _
    | exact preservesOrigins_trans (preservesOrigins_push _ _) (preservesOrigins_push _ _)
    | exact allocateFields_preservesOrigins _ _ _
    | apply preservesOrigins_set; assumption; rfl

 theorem environmentValid_lookup {bound index address : Nat} {environment : Environment}
    (h : EnvironmentValid bound environment) (found : environment[index]? = some address) :
    address < bound := h address (List.mem_of_getElem? found)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1200000 in
 theorem stepRaw_lexicalInvariant {state : State} (invariant : LexicalInvariant state) :
    LexicalInvariant (stepRaw state) := by
  rcases invariant with ⟨hh,hc,hs⟩
  have stackHead : ∀ frame rest, state.stack = frame::rest → FrameValid state.heap.size frame := by
    intro frame rest eq
    exact hs frame (eq ▸ List.mem_cons_self)
  have hp := stepRaw_preservesOrigins state
  have hg : state.heap.size ≤ (stepRaw state).heap.size := hp.1
  unfold stepRaw
  split <;> repeat' first | split
  all_goals try dsimp only at *
  all_goals try (have headValid := stackHead _ _ (by assumption))
  all_goals simp_all only [LexicalInvariant, ControlValid, ClosureValid,
    CellValid.eq_1, CellValid.eq_2, CellValid.eq_3,
    RuntimeValueValid.eq_1, RuntimeValueValid.eq_2, RuntimeValueValid.eq_3, RuntimeValueValid.eq_4, RuntimeValueValid.eq_5, RuntimeValueValid.eq_6, RuntimeValueValid.eq_7,
    FrameValid.eq_1, FrameValid.eq_2, FrameValid.eq_3, FrameValid.eq_4, FrameValid.eq_5, FrameValid.eq_6, FrameValid.eq_7, FrameValid.eq_8, FrameValid.eq_9, FrameValid.eq_10, FrameValid.eq_11, FrameValid.eq_12,
    scoped_bound_iff, scoped_lam_iff, scoped_app_iff,
    scoped_mix_iff, scoped_fix_iff, scoped_specification_iff, scoped_prototype_iff,
    scoped_reflect_iff, scoped_metadata_iff, scoped_project_iff, scoped_binary_iff,
    scoped_extend_iff, scoped_record_iff, scoped_get_iff, scoped_condition_iff,
    scoped_inject_iff, scoped_case_iff, scoped_ifBool_iff,
    List.mem_cons, List.not_mem_nil, false_or, or_false, Array.size_push]
  all_goals try (have lookupValid := environmentValid_lookup hc.2 (by assumption))
  all_goals try (have allocationValid := allocateFields_valid hh hc.2 hc.1)
  all_goals try (have allocationValid := allocateFields_valid hh headValid.1 headValid.2)
  all_goals grind [heapValid_push,heapValid_set, allocateFields_cellValid, allocateFields_addressValid, allocateFields_size_mono, scalarValue_valid,
    ClosureValid, CellValid, FrameValid, RuntimeValueValid, EnvironmentValid, environmentValid_lookup, Scoped.app, Scoped.bound, Scoped.natural, Scoped.boolean, Scoped.label, List.length_cons, List.mem_of_getElem?, List.mem_of_find?_eq_some,
    environmentValid_mono,environmentValid_tied,cellValid_mono,frameValid_mono,
    runtimeValueValid_mono,scoped_weaken,scoped_mixBody]

/-- Memoization is permanent: later raw steps cannot overwrite or re-enter an
already cached cell. This is the operational sharing fact; it makes no native
effect claim (this edition has no native-effect value constructor). -/
def PreservesCached (before after : Array Cell) : Prop :=
  ∀ (address : Nat) (origin : Closure) (value : RuntimeValue),
    before[address]? = some (.cached origin value) → after[address]? = some (.cached origin value)

 theorem preservesCached_refl (heap : Array Cell) : PreservesCached heap heap :=
  fun _ _ _ found => found

 theorem preservesCached_trans {a b c : Array Cell}
    (hab : PreservesCached a b) (hbc : PreservesCached b c) : PreservesCached a c :=
  fun address origin value found => hbc address origin value (hab address origin value found)

 theorem preservesCached_push (heap : Array Cell) (cell : Cell) :
    PreservesCached heap (heap.push cell) := by
  intro address origin value found
  have bound := (Array.getElem?_eq_some_iff.mp found).1
  simpa [Array.getElem?_push,Nat.ne_of_lt bound] using found

 theorem preservesCached_set {heap : Array Cell} {address : Nat} {old next : Cell}
    (found : heap[address]? = some old)
    (uncached : ∀ origin value, old ≠ .cached origin value) :
    PreservesCached heap (heap.set! address next) := by
  intro index origin value cached
  by_cases same : index = address
  · subst index
    exact False.elim (uncached origin value (Option.some.inj (found.symm.trans cached)))
  · simpa [Array.set!,same,Ne.symm same] using cached

 theorem allocateFields_preservesCached (heap : Array Cell) (environment : Environment)
    (fields : List (String × Term)) :
    PreservesCached heap (allocateFields heap environment fields).1 := by
  have loop : ∀ (fields : List (String × Term)) (pair : Array Cell × List (String × Address)),
      PreservesCached pair.1
        (fields.foldl (fun prior field => (prior.1.push (.suspended ⟨field.2,environment⟩),
          (field.1,prior.1.size)::prior.2)) pair).1 := by
    intro fields
    induction fields with
    | nil => intro pair; exact preservesCached_refl _
    | cons field fields ih =>
      intro pair
      simpa only [List.foldl_cons] using preservesCached_trans
        (preservesCached_push pair.1 (.suspended ⟨field.2,environment⟩))
        (ih (pair.1.push (.suspended ⟨field.2,environment⟩),(field.1,pair.1.size)::pair.2))
  exact loop fields (heap,[])

 theorem stepRaw_preservesCached (state : State) :
    PreservesCached state.heap (stepRaw state).heap := by
  unfold stepRaw
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals first
    | exact preservesCached_refl _
    | exact preservesCached_push _ _
    | exact preservesCached_trans (preservesCached_push _ _) (preservesCached_push _ _)
    | exact allocateFields_preservesCached _ _ _
    | apply preservesCached_set; assumption; intro origin value equality; cases equality

/-- Raw reachability is resource independent. Capacity may postpone a raw
transition, but cannot turn it into a different heap computation. -/
inductive Reachable (initial : State) : State → Prop where
  | start : Reachable initial initial
  | next {state : State} : Reachable initial state → Reachable initial (stepRaw state)

 theorem reachable_preservesOrigins {initial state : State}
    (reachable : Reachable initial state) : PreservesOrigins initial.heap state.heap := by
  induction reachable with
  | start => exact preservesOrigins_refl _
  | next reachable ih => exact preservesOrigins_trans ih (stepRaw_preservesOrigins _)

 theorem reachable_lexicalInvariant {source : Term} {state : State}
    (closed : Scoped 0 source) (reachable : Reachable (initial source) state) :
    LexicalInvariant state := by
  induction reachable with
  | start => exact initial_lexicalInvariant closed
  | next _ ih => exact stepRaw_lexicalInvariant ih

 theorem reachable_preservesCached {initial state : State}
    (reachable : Reachable initial state) : PreservesCached initial.heap state.heap := by
  induction reachable with
  | start => exact preservesCached_refl _
  | next _ ih => exact preservesCached_trans ih (stepRaw_preservesCached _)

/-- The active update stack owns evaluation marks. The relation permits cyclic
origins, but never duplicate active demand of one address. Re-entry observes a
blackhole before pushing another update frame. -/
def stackUpdates : List Frame → List Address
  | [] => []
  | .update address::rest => address::stackUpdates rest
  | _::rest => stackUpdates rest

def Busy (heap : Array Cell) (stack : List Frame) : Prop :=
  (stackUpdates stack).Nodup ∧ ∀ address,
    address ∈ stackUpdates stack ↔ ∃ origin, heap[address]? = some (.evaluating origin)

def BusyInvariant (state : State) : Prop := Busy state.heap state.stack

 theorem initial_busyInvariant (source : Term) : BusyInvariant (initial source) := by
  simp [BusyInvariant,Busy,initial,stackUpdates]

 theorem busy_stack_eq {heap : Array Cell} {before after : List Frame}
    (busy : Busy heap before) (same : stackUpdates after = stackUpdates before) : Busy heap after := by
  simpa only [Busy,same] using busy

 theorem busy_push {heap : Array Cell} {stack : List Frame} {cell : Cell}
    (busy : Busy heap stack) (notEvaluating : ∀ origin, cell ≠ .evaluating origin) :
    Busy (heap.push cell) stack := by
  refine ⟨busy.1,?_⟩
  intro address
  constructor
  · intro member
    obtain ⟨origin,found⟩ := (busy.2 address).mp member
    have bound := (Array.getElem?_eq_some_iff.mp found).1
    exact ⟨origin,by simpa [Array.getElem?_push,Nat.ne_of_lt bound] using found⟩
  · intro ⟨origin,found⟩
    rw [Array.getElem?_push] at found
    split at found
    · exact False.elim (notEvaluating origin (Option.some.inj found))
    · exact (busy.2 address).mpr ⟨origin,found⟩

 theorem busy_enter {heap : Array Cell} {stack : List Frame} {address : Nat} {origin : Closure}
    (busy : Busy heap stack) (found : heap[address]? = some (.suspended origin)) :
    Busy (heap.set! address (.evaluating origin)) (.update address::stack) := by
  have bound := (Array.getElem?_eq_some_iff.mp found).1
  have absent : address ∉ stackUpdates stack := by
    intro member
    obtain ⟨other,marked⟩ := (busy.2 address).mp member
    have contradiction := Option.some.inj (found.symm.trans marked)
    cases contradiction
  refine ⟨List.nodup_cons.mpr ⟨absent,busy.1⟩,?_⟩
  intro index
  by_cases same : index = address
  · subst index
    simp [stackUpdates,Array.set!,bound]
  · simpa [stackUpdates,Array.set!,same,Ne.symm same] using busy.2 index

 theorem busy_update_exists {heap : Array Cell} {stack rest : List Frame} {address : Nat}
    (busy : Busy heap stack) (head : stack = .update address::rest) :
    ∃ origin, heap[address]? = some (.evaluating origin) :=
  (busy.2 address).mp (by simp [head,stackUpdates])

 theorem busy_cache {heap : Array Cell} {stack rest : List Frame} {address : Nat} {origin : Closure}
    (busy : Busy heap stack) (head : stack = .update address::rest)
    (found : heap[address]? = some (.evaluating origin)) (value : RuntimeValue) :
    Busy (heap.set! address (.cached origin value)) rest := by
  have bound := (Array.getElem?_eq_some_iff.mp found).1
  have noDup : (address::stackUpdates rest).Nodup := by simpa [head,stackUpdates] using busy.1
  have absent := (List.nodup_cons.mp noDup).1
  refine ⟨(List.nodup_cons.mp noDup).2,?_⟩
  intro index
  by_cases same : index = address
  · subst index
    simp [Array.set!,bound,absent]
  · simpa [head,stackUpdates,Array.set!,same,Ne.symm same] using busy.2 index

 theorem allocateFields_busy {heap : Array Cell} {stack : List Frame}
    (busy : Busy heap stack) (environment : Environment) (fields : List (String × Term)) :
    Busy (allocateFields heap environment fields).1 stack := by
  have loop : ∀ (fields : List (String × Term)) (pair : Array Cell × List (String × Address)),
      Busy pair.1 stack → Busy
        (fields.foldl (fun prior field => (prior.1.push (.suspended ⟨field.2,environment⟩),
          (field.1,prior.1.size)::prior.2)) pair).1 stack := by
    intro fields
    induction fields with
    | nil => intro pair busy; exact busy
    | cons field fields ih =>
      intro pair busy
      apply ih (pair.1.push (.suspended ⟨field.2,environment⟩),(field.1,pair.1.size)::pair.2)
      exact busy_push busy (by intro origin equality; cases equality)
  exact loop fields (heap,[]) busy

 theorem stepRaw_busyInvariant {state : State} (busy : BusyInvariant state) :
    BusyInvariant (stepRaw state) := by
  change Busy state.heap state.stack at busy
  unfold BusyInvariant stepRaw
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals solve
    | exact busy
    | apply busy_stack_eq busy; simp [stackUpdates, *]
    | apply busy_enter busy; assumption
    | apply busy_cache busy; assumption; assumption
    | apply busy_push busy; intro origin equality; cases equality
    | apply busy_push (busy_push busy (by intro origin equality; cases equality));
      intro origin equality; cases equality
    | exact allocateFields_busy busy _ _
    | apply busy_stack_eq (busy_push busy (by intro origin equality; cases equality));
      simp [stackUpdates, *]
    | apply busy_stack_eq (allocateFields_busy busy _ _); simp [stackUpdates, *]
    | exfalso
      have marked := busy_update_exists busy (by assumption)
      obtain ⟨origin,found⟩ := marked
      grind

 theorem reachable_busyInvariant {source : Term} {state : State}
    (reachable : Reachable (initial source) state) : BusyInvariant state := by
  induction reachable with
  | start => exact initial_busyInvariant _
  | next _ ih => exact stepRaw_busyInvariant ih

 theorem stepRaw_no_invalidUpdate {state : State} (busy : BusyInvariant state)
    (prior : state.control ≠ .refused .invalidUpdate) :
    (stepRaw state).control ≠ .refused .invalidUpdate := by
  change Busy state.heap state.stack at busy
  unfold stepRaw
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals solve
    | exact prior
    | simp_all
    | have marked := busy_update_exists busy (by assumption)
      obtain ⟨origin,found⟩ := marked
      grind

 theorem stepRaw_no_unbound {state : State} (lexical : LexicalInvariant state)
    (prior : state.control ≠ .refused .unbound) :
    (stepRaw state).control ≠ .refused .unbound := by
  unfold stepRaw
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals solve
    | exact prior
    | simp_all
    | simp_all [LexicalInvariant,ControlValid,ClosureValid,scoped_bound_iff]

 theorem stepRaw_no_missingCell {state : State} (lexical : LexicalInvariant state)
    (prior : state.control ≠ .refused .missingCell) :
    (stepRaw state).control ≠ .refused .missingCell := by
  unfold stepRaw
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals solve
    | exact prior
    | simp_all
    | simp_all [LexicalInvariant,ControlValid]

 theorem reachable_no_internalRefusal {source : Term} {state : State}
    (closed : Scoped 0 source) (reachable : Reachable (initial source) state) :
    state.control ≠ .refused .unbound ∧ state.control ≠ .refused .missingCell ∧
      state.control ≠ .refused .invalidUpdate := by
  induction reachable with
  | start => simp [initial]
  | next reachable ih =>
      have lexical := reachable_lexicalInvariant closed reachable
      have busy := reachable_busyInvariant reachable
      exact ⟨stepRaw_no_unbound lexical ih.1,stepRaw_no_missingCell lexical ih.2.1,
        stepRaw_no_invalidUpdate busy ih.2.2⟩

/-- Completion is exposed only after the continuation has been discharged. -/
def FinalStackInvariant (state : State) : Prop :=
  ∀ value, state.control = .complete value → state.stack = []

 theorem initial_finalStackInvariant (source : Term) : FinalStackInvariant (initial source) := by
  intro value complete; cases complete

 theorem stepRaw_finalStackInvariant {state : State} (final : FinalStackInvariant state) :
    FinalStackInvariant (stepRaw state) := by
  unfold FinalStackInvariant stepRaw at *
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals solve | exact final | simp_all

 theorem reachable_finalStackInvariant {source : Term} {state : State}
    (reachable : Reachable (initial source) state) : FinalStackInvariant state := by
  induction reachable with
  | start => exact initial_finalStackInvariant _
  | next _ ih => exact stepRaw_finalStackInvariant ih

/--
info: 'Minidregg.Theory.ObjectiveBendDemandInvariant.stepRaw_lexicalInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms stepRaw_lexicalInvariant
/--
info: 'Minidregg.Theory.ObjectiveBendDemandInvariant.stepRaw_preservesOrigins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms stepRaw_preservesOrigins
/--
info: 'Minidregg.Theory.ObjectiveBendDemandInvariant.stepRaw_preservesCached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms stepRaw_preservesCached
/--
info: 'Minidregg.Theory.ObjectiveBendDemandInvariant.stepRaw_busyInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms stepRaw_busyInvariant
/--
info: 'Minidregg.Theory.ObjectiveBendDemandInvariant.stepRaw_finalStackInvariant' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms stepRaw_finalStackInvariant
/--
info: 'Minidregg.Theory.ObjectiveBendDemandInvariant.reachable_no_internalRefusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms reachable_no_internalRefusal

end Minidregg.Theory.ObjectiveBendDemandInvariant
