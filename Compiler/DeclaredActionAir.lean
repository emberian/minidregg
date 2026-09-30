/-
# Compiler.DeclaredActionAir -- the bounded declared-action AIR seam

This module arithmetizes only the closed action vocabulary already owned by
`Theory.DeclaredActionLowering`: create, guarded write, and exact account move.
It does not add an action interpreter.  The ordered observations below are a
projection of the declaration's one guarded patch (`Declaration.patch`): one
observation per `Store.Op`, read at the store its prefix produced.  The
reflection theorem returns to `Patch.ValidFrom` and `Declaration.run`, whose
post is `Patch.run`.

The emitted descriptor is statement-specific.  Its public prefix is the exact
lawful declaration bytes, the request's policy-id/grant-generation/source-revision bytes, and the
canonical pre-state root bytes.  Its private original variables are the
expected/observed sparse values at every ordered guarded operation.  Pin constraints
bind those private values to the generated observation trace; equality
constraints then enforce every guard.  Option-Int codes must be below the
BabyBear modulus, making their field embedding injective rather than silently
identifying distinct full-width integers modulo the field.

The declaration's same scoped-action admission check selects either this
derived system or the unsatisfiable constant relation. Its amount/target checks
are on the pinned statement data, not a caller-supplied acceptance bit.

This is not a policy verifier: `PolicyWitness`, signatures, membership proofs,
and the policy predicate remain in `TypedAuthorization`.  It is also not a
generic effect registry or a callback semantics.
-/
import Compiler.DeclaredActionBytes
import Compiler.EmitSerialize
import Compiler.Sp800185Cshake256
import Compiler.Tower256ConcreteBackend

namespace Minidregg.Compiler.DeclaredActionAir

open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Theory.EffectDeclaration (effectLayout)
open Minidregg.Theory.Store
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev EffectFields := Store effectLayout

/-! ## Exact projection of the one guarded patch -/

structure GuardObservation where
  expected : Option Int
  observed : Option Int
  deriving DecidableEq, Repr

/-- The value an operation's guard requires at its address: a read's observed
value, a write's or free's prior value, and absence for an allocation. -/
def opGuard : Op effectLayout -> Option Int
  | .read _ _ observed => observed
  | .write _ _ before _ => some before
  | .allocate _ _ _ => none
  | .free _ _ before => some before

/-- On the all-RAM effect layout an operation is enabled exactly when its
address holds its guard value. -/
theorem enabled_iff_opGuard (fields : EffectFields) (op : Op effectLayout) :
    op.Enabled fields <-> fields op.address = opGuard op := by
  cases op <;> simp [Op.Enabled, Op.address, opGuard, Store.Fresh]

/-- Observe the guard read at each step of the patch.  The next store is the
same `Op.apply` that `Patch.run` uses; this is a trace projection, not an
alternative state transition. -/
def observeGuards : Patch effectLayout -> EffectFields -> List GuardObservation
  | [], _ => []
  | op :: ops, fields =>
      { expected := opGuard op, observed := fields op.address } ::
        observeGuards ops (op.apply fields)

@[simp] theorem observeGuards_length (patch : Patch effectLayout)
    (fields : EffectFields) :
    (observeGuards patch fields).length = patch.length := by
  induction patch generalizing fields with
  | nil => rfl
  | cons op ops induction =>
      simp [observeGuards, induction]

def GuardsExact (observations : List GuardObservation) : Prop :=
  forall observation, observation ∈ observations ->
    observation.expected = observation.observed

theorem observeGuards_exact_iff_valid (patch : Patch effectLayout)
    (fields : EffectFields) :
    GuardsExact (observeGuards patch fields) <-> Patch.ValidFrom fields patch := by
  induction patch generalizing fields with
  | nil => simp [GuardsExact, observeGuards, Patch.ValidFrom]
  | cons op ops induction =>
      simp only [observeGuards, GuardsExact, List.mem_cons, forall_eq_or_imp,
        Patch.ValidFrom, enabled_iff_opGuard]
      rw [← induction (op.apply fields)]
      constructor
      · rintro ⟨guard, rest⟩
        exact ⟨guard.symm, rest⟩
      · rintro ⟨guard, rest⟩
        exact ⟨guard.symm, rest⟩

/-! ## Exact public bytes -/

/-- The request policy selection that this AIR actually binds.  There is no
claim here that these three scalars encode a portal's `PolicyWitness`. -/
def policyBytes (context : RequestContext) : List UInt8 :=
  StreamCodec.nat.encode context.policyId.value ++
    StreamCodec.nat.encode context.policyEpoch ++
    StreamCodec.nat.encode context.policyRevision

def actionBytes {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : List UInt8 :=
  (declarationCodec target).encode declaration

def stateRootBytes {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : List UInt8 :=
  digestCodec.encode declaration.expectedPreRoot

def publicBytes {kind : ResourceKind} {target : ResourceId kind}
    (context : RequestContext) (declaration : Declaration target) : List UInt8 :=
  actionBytes declaration ++ policyBytes context ++ stateRootBytes declaration

/-! ## Bounded BabyBear layout and generated assignment -/

def optionCode (value : Option Int) : Nat := optionIntCode value

theorem optionCode_injective : Function.Injective optionCode := by
  intro left right equal
  have decoded := congrArg optionIntOfCode equal
  simpa [optionCode] using decoded

/-- The explicit finite-field range premise: visible for arbitrary full-width
`Int`s. -/
def CodesBounded (observations : List GuardObservation) : Prop :=
  forall observation, observation ∈ observations ->
    optionCode observation.expected < babyBearP /\
      optionCode observation.observed < babyBearP

def wireCount (publicWidth guardCount : Nat) : Nat :=
  publicWidth + 2 * guardCount

def byteWire {publicWidth guardCount : Nat} (index : Fin publicWidth) :
    Fin (wireCount publicWidth guardCount) :=
  ⟨index.val, by
    have := index.isLt
    unfold wireCount
    omega⟩

def expectedWire {publicWidth guardCount : Nat} (index : Fin guardCount) :
    Fin (wireCount publicWidth guardCount) :=
  ⟨publicWidth + index.val, by
    have := index.isLt
    unfold wireCount
    omega⟩

def observedWire {publicWidth guardCount : Nat} (index : Fin guardCount) :
    Fin (wireCount publicWidth guardCount) :=
  ⟨publicWidth + guardCount + index.val, by
    have := index.isLt
    unfold wireCount
    omega⟩

abbrev WireIx {kind : ResourceKind} {target : ResourceId kind}
    (context : RequestContext) (declaration : Declaration target)
    (fields : EffectFields) :=
  Fin (wireCount (publicBytes context declaration).length
    (observeGuards declaration.patch fields).length)

def observations {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) (fields : EffectFields) :
    List GuardObservation :=
  observeGuards declaration.patch fields

def observationAt {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) (fields : EffectFields)
    (index : Fin (observations declaration fields).length) : GuardObservation :=
  (observations declaration fields).get index

/-- The complete original-variable assignment generated from the canonical
statement.  The emitted public prefix is literally the first branch. -/
def assignment {kind : ResourceKind} {target : ResourceId kind}
    (context : RequestContext) (declaration : Declaration target)
    (fields : EffectFields) : WireIx context declaration fields -> BabyBear :=
  fun index =>
    if hbyte : index.val < (publicBytes context declaration).length then
      ((publicBytes context declaration).get ⟨index.val, hbyte⟩).toNat
    else if hexpected : index.val <
        (publicBytes context declaration).length +
          (observations declaration fields).length then
      optionCode (observationAt declaration fields
        ⟨index.val - (publicBytes context declaration).length, by omega⟩).expected
    else
      optionCode (observationAt declaration fields
        ⟨index.val - (publicBytes context declaration).length -
          (observations declaration fields).length, by
            have indexBound := index.isLt
            change index.val < (publicBytes context declaration).length +
              2 * (observations declaration fields).length at indexBound
            omega⟩).observed

@[simp] theorem assignment_byte {kind : ResourceKind}
    {target : ResourceId kind} (context : RequestContext)
    (declaration : Declaration target) (fields : EffectFields)
    (index : Fin (publicBytes context declaration).length) :
    assignment context declaration fields (byteWire index) =
      ((publicBytes context declaration).get index).toNat := by
  unfold assignment byteWire
  rw [dif_pos index.isLt]

@[simp] theorem assignment_expected {kind : ResourceKind}
    {target : ResourceId kind} (context : RequestContext)
    (declaration : Declaration target) (fields : EffectFields)
    (index : Fin (observations declaration fields).length) :
    assignment context declaration fields (expectedWire index) =
      optionCode (observationAt declaration fields index).expected := by
  have notByte : ¬ (expectedWire
      (publicWidth := (publicBytes context declaration).length) index).val <
      (publicBytes context declaration).length := by
    change ¬ ((publicBytes context declaration).length + index.val <
      (publicBytes context declaration).length)
    omega
  have expectedBound : (expectedWire
      (publicWidth := (publicBytes context declaration).length) index).val <
      (publicBytes context declaration).length +
        (observations declaration fields).length := by
    change (publicBytes context declaration).length + index.val <
      (publicBytes context declaration).length +
        (observations declaration fields).length
    omega
  unfold assignment
  split
  · next hbyte => exact False.elim (notByte hbyte)
  · split
    · apply congrArg (fun code : Nat => (code : BabyBear))
      apply congrArg optionCode
      apply congrArg GuardObservation.expected
      apply congrArg (observationAt declaration fields)
      apply Fin.ext
      simp [expectedWire]
    · next hexpected => exact False.elim (hexpected expectedBound)

@[simp] theorem assignment_observed {kind : ResourceKind}
    {target : ResourceId kind} (context : RequestContext)
    (declaration : Declaration target) (fields : EffectFields)
    (index : Fin (observations declaration fields).length) :
    assignment context declaration fields (observedWire index) =
      optionCode (observationAt declaration fields index).observed := by
  have notByte : ¬ (observedWire
      (publicWidth := (publicBytes context declaration).length) index).val <
      (publicBytes context declaration).length := by
    change ¬ ((publicBytes context declaration).length +
      (observations declaration fields).length + index.val <
        (publicBytes context declaration).length)
    omega
  have notExpected : ¬ (observedWire
      (publicWidth := (publicBytes context declaration).length) index).val <
      (publicBytes context declaration).length +
        (observations declaration fields).length := by
    change ¬ ((publicBytes context declaration).length +
      (observations declaration fields).length + index.val <
        (publicBytes context declaration).length +
          (observations declaration fields).length)
    omega
  unfold assignment
  split
  · next hbyte => exact False.elim (notByte hbyte)
  · split
    · next hexpected => exact False.elim (notExpected hexpected)
    · apply congrArg (fun code : Nat => (code : BabyBear))
      apply congrArg optionCode
      apply congrArg GuardObservation.observed
      apply congrArg (observationAt declaration fields)
      apply Fin.ext
      change (publicBytes context declaration).length +
          (observations declaration fields).length + index.val -
            (publicBytes context declaration).length -
              (observations declaration fields).length = index.val
      omega

/-! ## Lean-authored constraints and emitted descriptor -/

def pinTerm {m : Nat} (wire : Fin m) (value : BabyBear) :
    Term (AirSig BabyBear (Fin m)) :=
  add' (vr wire) (cst (-value))

def eqTerm {m : Nat} (left right : Fin m) :
    Term (AirSig BabyBear (Fin m)) :=
  add' (vr left) (mul' (cst (-1)) (vr right))

@[simp] theorem pinTerm_correct {m : Nat} (asg : Fin m -> BabyBear)
    (wire : Fin m) (value : BabyBear) :
    accepts asg (pinTerm wire value) <-> asg wire = value := by
  simpa [accepts, pinTerm, sub_eq_add_neg] using
    (sub_eq_zero : asg wire - value = 0 ↔ asg wire = value)

@[simp] theorem eqTerm_correct {m : Nat} (asg : Fin m -> BabyBear)
    (left right : Fin m) :
    accepts asg (eqTerm left right) <-> asg left = asg right := by
  simpa [accepts, eqTerm, sub_eq_add_neg] using
    (sub_eq_zero : asg left - asg right = 0 ↔ asg left = asg right)

def pinSystem {m : Nat} (canonical : Fin m -> BabyBear) :
    ConstraintSystem BabyBear (Fin m) :=
  (List.finRange m).map fun index => pinTerm index (canonical index)

theorem pinSystem_correct {m : Nat} (canonical asg : Fin m -> BabyBear) :
    systemAccepts asg (pinSystem canonical) <-> asg = canonical := by
  constructor
  · intro accepted
    funext index
    apply (pinTerm_correct asg index (canonical index)).mp
    exact accepted _ (List.mem_map.mpr
      ⟨index, List.mem_finRange index, rfl⟩)
  · intro asgExact
    subst asg
    intro term member
    obtain ⟨index, -, rfl⟩ := List.mem_map.mp member
    exact (pinTerm_correct canonical index (canonical index)).mpr rfl

def guardSystem {kind : ResourceKind} {target : ResourceId kind}
    (context : RequestContext) (declaration : Declaration target)
    (fields : EffectFields) :
    ConstraintSystem BabyBear (WireIx context declaration fields) :=
  (List.finRange (observations declaration fields).length).map fun index =>
    eqTerm (expectedWire index) (observedWire index)

def system {kind : ResourceKind} {target : ResourceId kind}
    (context : RequestContext) (declaration : Declaration target)
    (fields : EffectFields) :
    ConstraintSystem BabyBear (WireIx context declaration fields) :=
  if declaration.admissionCheck then
    pinSystem (assignment context declaration fields) ++
      guardSystem context declaration fields
  else [cst 1]

theorem guardSystem_correct {kind : ResourceKind}
    {target : ResourceId kind} (context : RequestContext)
    (declaration : Declaration target) (fields : EffectFields)
    (bounded : CodesBounded (observations declaration fields)) :
    systemAccepts (assignment context declaration fields)
        (guardSystem context declaration fields) <->
      GuardsExact (observations declaration fields) := by
  constructor
  · intro accepted observation member
    rw [List.mem_iff_get] at member
    obtain ⟨index, exact⟩ := member
    subst observation
    have equalFields := (eqTerm_correct (assignment context declaration fields)
      (expectedWire index) (observedWire index)).mp
      (accepted _ (List.mem_map.mpr
        ⟨index, List.mem_finRange index, rfl⟩))
    simp only [assignment_expected, assignment_observed] at equalFields
    have range :
        optionCode (observationAt declaration fields index).expected < babyBearP /\
          optionCode (observationAt declaration fields index).observed < babyBearP := by
      simpa [observationAt] using bounded _ (List.get_mem _ index)
    have equalCodes :
        optionCode (observationAt declaration fields index).expected =
          optionCode (observationAt declaration fields index).observed := by
      have modEqual := (ZMod.natCast_eq_natCast_iff' _ _ babyBearP).mp equalFields
      rw [Nat.mod_eq_of_lt range.1, Nat.mod_eq_of_lt range.2] at modEqual
      exact modEqual
    exact optionCode_injective equalCodes
  · intro exact term member
    obtain ⟨index, -, rfl⟩ := List.mem_map.mp member
    apply (eqTerm_correct (assignment context declaration fields)
      (expectedWire index) (observedWire index)).mpr
    simp only [assignment_expected, assignment_observed]
    exact congrArg (fun value : Nat => (value : BabyBear))
      (congrArg optionCode (exact _ (List.get_mem _ index)))

theorem system_correct {kind : ResourceKind} {target : ResourceId kind}
    (context : RequestContext) (declaration : Declaration target)
    (fields : EffectFields)
    (bounded : CodesBounded (observations declaration fields))
    (asg : WireIx context declaration fields -> BabyBear) :
    systemAccepts asg (system context declaration fields) <->
      asg = assignment context declaration fields /\
        declaration.run fields =
          some (Patch.run fields declaration.patch) := by
  by_cases admitted : declaration.admissionCheck = true
  · rw [system, if_pos admitted, systemAccepts_append, pinSystem_correct]
    constructor
    · rintro ⟨rfl, guards⟩
      refine ⟨rfl, ?_⟩
      have valid := (observeGuards_exact_iff_valid declaration.patch fields).mp
        ((guardSystem_correct context declaration fields bounded).mp guards)
      exact (declaration.run_eq_some_iff _ _).mpr ⟨admitted, valid, rfl⟩
    · rintro ⟨rfl, run⟩
      refine ⟨rfl, (guardSystem_correct context declaration fields bounded).mpr ?_⟩
      apply (observeGuards_exact_iff_valid declaration.patch fields).mpr
      exact ((declaration.run_eq_some_iff _ _).mp run).2.1
  · have notAdmitted : ¬ declaration.Admitted := admitted
    have refused : declaration.run fields ≠ some (Patch.run fields declaration.patch) :=
      fun run => notAdmitted ((declaration.run_eq_some_iff _ _).mp run).1
    simp only [system, admitted, Bool.false_eq_true, if_false, refused, and_false,
      iff_false]
    intro accepted
    have impossible := accepted (cst 1) (by simp)
    change (1 : BabyBear) = 0 at impossible
    exact one_ne_zero impossible


def descriptor {kind : ResourceKind} {target : ResourceId kind}
    (context : RequestContext) (declaration : Declaration target)
    (fields : EffectFields) : ConstraintDescriptor BabyBear :=
  let m := wireCount (publicBytes context declaration).length
    (observations declaration fields).length
  emit Fin.val (publicBytes context declaration).length m
    (system context declaration fields)

theorem descriptor_wellFormed {kind : ResourceKind}
    {target : ResourceId kind} (context : RequestContext)
    (declaration : Declaration target) (fields : EffectFields) :
    (descriptor context declaration fields).WellFormed := by
  apply emit_wellFormed Fin.val
  · unfold wireCount
    omega
  · intro index
    exact index.isLt

/-- Descriptor acceptance pins only the emitted public byte prefix.  The
private expected/observed guard lanes must be forced by the descriptor. -/
def DescriptorAccepts {kind : ResourceKind} {target : ResourceId kind}
    (context : RequestContext) (declaration : Declaration target)
    (fields : EffectFields) : Prop :=
  exists wireValues : Nat -> BabyBear,
    (forall index : Fin (publicBytes context declaration).length,
      wireValues index.val =
        ((publicBytes context declaration).get index).toNat) /\
    descriptorHolds (descriptor context declaration fields) wireValues

/-- Ill-scoped or unfunded source syntax emits an inconsistent constraint.
This refusal is independent of guard-value bounds and holds for every
assignment supplied to the emitted descriptor. -/
theorem no_descriptorAccepts_of_inadmissible {kind : ResourceKind}
    {target : ResourceId kind} (context : RequestContext)
    (declaration : Declaration target) (fields : EffectFields)
    (inadmissible : ¬ declaration.Admitted) :
    ¬ DescriptorAccepts context declaration fields := by
  rintro ⟨wireValues, _, holds⟩
  have emitted := (emit_faithful Fin.val
    (publicBytes context declaration).length
    (wireCount (publicBytes context declaration).length
      (observations declaration fields).length)
    (system context declaration fields) wireValues).mp holds
  have accepted := flattenSystem_forces
    (fun index : WireIx context declaration fields => wireValues index.val)
    (readAux (wireCount (publicBytes context declaration).length
      (observations declaration fields).length) wireValues)
    (system context declaration fields) 0 emitted.1 emitted.2
  have check : declaration.admissionCheck ≠ true := inadmissible
  have impossible := accepted (cst 1) (by simp [system, check])
  change (1 : BabyBear) = 0 at impossible
  exact one_ne_zero impossible

/-- **Load-bearing reflection.**  The emitted descriptor accepts its exact
action/policy/root public bytes iff the declaration's checker accepts at the
pre-store, with the post `Patch.run` of its one patch. -/
theorem descriptor_accepts_iff_run {kind : ResourceKind}
    {target : ResourceId kind} (context : RequestContext)
    (declaration : Declaration target) (fields : EffectFields)
    (bounded : CodesBounded (observations declaration fields)) :
    DescriptorAccepts context declaration fields <->
      declaration.run fields =
        some (Patch.run fields declaration.patch) := by
  constructor
  · rintro ⟨wireValues, publicExact, holds⟩
    have emitted := (emit_faithful Fin.val
      (publicBytes context declaration).length
      (wireCount (publicBytes context declaration).length
        (observations declaration fields).length)
      (system context declaration fields) wireValues).mp holds
    have accepted := flattenSystem_forces
      (fun index : WireIx context declaration fields => wireValues index.val)
      (readAux (wireCount (publicBytes context declaration).length
        (observations declaration fields).length) wireValues)
      (system context declaration fields) 0 emitted.1 emitted.2
    exact ((system_correct context declaration fields bounded _).mp accepted).2
  · intro run
    have accepted : systemAccepts (assignment context declaration fields)
        (system context declaration fields) :=
      (system_correct context declaration fields bounded _).mpr ⟨rfl, run⟩
    obtain ⟨wireValues, pinned, holds⟩ :=
      (emit_accepts_iff_fin
        (wireCount (publicBytes context declaration).length
          (observations declaration fields).length)
        (publicBytes context declaration).length
        (assignment context declaration fields)
        (system context declaration fields)).mpr accepted
    refine ⟨wireValues, ?_, holds⟩
    intro index
    have pinnedByte := pinned (byteWire
      (guardCount := (observations declaration fields).length) index)
    unfold assignment byteWire at pinnedByte
    rw [dif_pos index.isLt] at pinnedByte
    exact pinnedByte

/-- Proof-relevant generated witness.  The original variable assignment is
computable (`assignment`); the existing emit completeness theorem supplies the
fresh auxiliary gate wires. -/
structure GeneratedWitness {kind : ResourceKind} {target : ResourceId kind}
    (context : RequestContext) (declaration : Declaration target)
    (fields : EffectFields) where
  wireValues : Nat -> BabyBear
  publicExact : forall index : Fin (publicBytes context declaration).length,
    wireValues index.val = ((publicBytes context declaration).get index).toNat
  holds : descriptorHolds (descriptor context declaration fields) wireValues

noncomputable def generateWitness {kind : ResourceKind}
    {target : ResourceId kind} (context : RequestContext)
    (declaration : Declaration target) (fields : EffectFields)
    (bounded : CodesBounded (observations declaration fields))
    (run : declaration.run fields =
      some (Patch.run fields declaration.patch)) :
    GeneratedWitness context declaration fields := by
  have existsWitness : DescriptorAccepts context declaration fields :=
    (descriptor_accepts_iff_run context declaration fields bounded).mpr run
  exact
    { wireValues := existsWitness.choose
      publicExact := existsWitness.choose_spec.1
      holds := existsWitness.choose_spec.2 }

/-! ## Exact byte projections exposed by the public assignment -/

theorem generated_public_bytes_exact {kind : ResourceKind}
    {target : ResourceId kind} (context : RequestContext)
    (declaration : Declaration target) (fields : EffectFields) :
    (List.ofFn fun index : Fin (publicBytes context declaration).length =>
      UInt8.ofNat ((assignment context declaration fields (byteWire index)).val)) =
      publicBytes context declaration := by
  apply List.ext_get
  · simp
  · intro n leftBound rightBound
    simp only [List.get_ofFn]
    let index : Fin (publicBytes context declaration).length :=
      ⟨n, by simpa using leftBound⟩
    change UInt8.ofNat
      ((assignment context declaration fields (byteWire index)).val) =
        (publicBytes context declaration).get index
    simp only [assignment_byte]
    rw [ZMod.val_natCast]
    have byteLt :
        ((publicBytes context declaration).get index).toNat < babyBearP :=
      lt_of_lt_of_le (UInt8.toNat_lt _) (by norm_num [babyBearP])
    rw [Nat.mod_eq_of_lt byteLt]
    exact UInt8.ofNat_toNat

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.DeclaredActionAir.descriptor_accepts_iff_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms descriptor_accepts_iff_run
/-- info: 'Minidregg.Compiler.DeclaredActionAir.no_descriptorAccepts_of_inadmissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_descriptorAccepts_of_inadmissible

end Minidregg.Compiler.DeclaredActionAir
