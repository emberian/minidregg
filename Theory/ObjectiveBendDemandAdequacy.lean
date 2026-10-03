/- Source/graph correspondence foundations for the new partial lazy edition.
This module deliberately does not claim an inhabited Representation contract:
transition preservation, administrative progress and full completeness are
separate substantive obligations. Finite ground laws below use the real executor. -/
import Theory.ObjectiveBendDemandInvariant
namespace Minidregg.Theory.ObjectiveBendDemandAdequacy
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandInvariant
set_option autoImplicit false

 theorem sourceSteps_trans {a b c : Term} (first : Steps a b) (second : Steps b c) : Steps a c := by
  induction first with
  | refl => exact second
  | next step _ ih => exact .next step (ih second)

 theorem scoped_rename_identity {n : Nat} {term : Term} (h : Scoped n term)
    (f : Nat → Nat) (hf : ∀ i, i < n → f i = i) : term.rename f = term := by
  induction h generalizing f with
  | bound hi => simp only [Term.rename,hf _ hi]
  | lam h ih =>
      simp only [Term.rename]
      congr 1
      apply ih (liftRename f)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp [liftRename,hf i (Nat.lt_of_succ_lt_succ hi)]
  | app _ _ ih₁ ih₂ => simp only [Term.rename,ih₁ f hf,ih₂ f hf]
  | mix _ _ ih₁ ih₂ => simp only [Term.rename,ih₁ f hf,ih₂ f hf]
  | fix _ _ ih₁ ih₂ => simp only [Term.rename,ih₁ f hf,ih₂ f hf]
  | specification _ _ ih₁ ih₂ => simp only [Term.rename,ih₁ f hf,ih₂ f hf]
  | prototype _ _ ih₁ ih₂ => simp only [Term.rename,ih₁ f hf,ih₂ f hf]
  | binary _ _ ih₁ ih₂ => simp only [Term.rename,ih₁ f hf,ih₂ f hf]
  | reflect _ ih => simp only [Term.rename,ih f hf]
  | metadata _ ih => simp only [Term.rename,ih f hf]
  | project _ ih => simp only [Term.rename,ih f hf]
  | get _ ih => simp only [Term.rename,ih f hf]
  | natural _ => simp only [Term.rename]
  | boolean _ => simp only [Term.rename]
  | label _ => simp only [Term.rename]
  | extend _ _ ih₁ ih₂ =>
      simp only [Term.rename,ih₁ f hf]
      congr 1
      apply Eq.trans _ (List.map_id' _)
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih₂ original member f hf)
  | record _ ih =>
      simp only [Term.rename]
      congr 1
      apply Eq.trans _ (List.map_id' _)
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih original member f hf)
  | condition _ _ _ ih₁ ih₂ ih₃ =>
      simp only [Term.rename,ih₁ f hf,ih₂ f hf]
      congr 1
      apply ih₃ (liftRename f)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp [liftRename,hf i (Nat.lt_of_succ_lt_succ hi)]

 theorem scoped_substitute_identity {n : Nat} {term : Term} (h : Scoped n term)
    (f : Nat → Term) (hf : ∀ i, i < n → f i = .bound i) : term.substitute f = term := by
  induction h generalizing f with
  | bound hi => simp only [Term.substitute,hf _ hi]
  | lam h ih =>
      simp only [Term.substitute]
      congr 1
      apply ih (liftSubstitution f)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp [liftSubstitution,hf i (Nat.lt_of_succ_lt_succ hi),Term.rename]
  | app _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ f hf,ih₂ f hf]
  | mix _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ f hf,ih₂ f hf]
  | fix _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ f hf,ih₂ f hf]
  | specification _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ f hf,ih₂ f hf]
  | prototype _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ f hf,ih₂ f hf]
  | binary _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ f hf,ih₂ f hf]
  | reflect _ ih => simp only [Term.substitute,ih f hf]
  | metadata _ ih => simp only [Term.substitute,ih f hf]
  | project _ ih => simp only [Term.substitute,ih f hf]
  | get _ ih => simp only [Term.substitute,ih f hf]
  | natural _ => simp only [Term.substitute]
  | boolean _ => simp only [Term.substitute]
  | label _ => simp only [Term.substitute]
  | extend _ _ ih₁ ih₂ =>
      simp only [Term.substitute,ih₁ f hf]
      congr 1
      apply Eq.trans _ (List.map_id' _)
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih₂ original member f hf)
  | record _ ih =>
      simp only [Term.substitute]
      congr 1
      apply Eq.trans _ (List.map_id' _)
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih original member f hf)
  | condition _ _ _ ih₁ ih₂ ih₃ =>
      simp only [Term.substitute,ih₁ f hf,ih₂ f hf]
      congr 1
      apply ih₃ (liftSubstitution f)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp [liftSubstitution,hf i (Nat.lt_of_succ_lt_succ hi),Term.rename]

 theorem scoped_substitution_congr {n : Nat} {term : Term} (h : Scoped n term)
    (first second : Nat → Term) (same : ∀ i, i < n → first i = second i) :
    term.substitute first = term.substitute second := by
  induction h generalizing first second with
  | bound hi => simp only [Term.substitute,same _ hi]
  | lam h ih =>
      simp only [Term.substitute]
      congr 1
      apply ih (liftSubstitution first) (liftSubstitution second)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp only [liftSubstitution,same i (Nat.lt_of_succ_lt_succ hi)]
  | app _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first second same,ih₂ first second same]
  | mix _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first second same,ih₂ first second same]
  | fix _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first second same,ih₂ first second same]
  | specification _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first second same,ih₂ first second same]
  | prototype _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first second same,ih₂ first second same]
  | binary _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first second same,ih₂ first second same]
  | reflect _ ih => simp only [Term.substitute,ih first second same]
  | metadata _ ih => simp only [Term.substitute,ih first second same]
  | project _ ih => simp only [Term.substitute,ih first second same]
  | get _ ih => simp only [Term.substitute,ih first second same]
  | natural _ | boolean _ | label _ => simp only [Term.substitute]
  | extend _ _ ih₁ ih₂ =>
      simp only [Term.substitute,ih₁ first second same]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih₂ original member first second same)
  | record _ ih =>
      simp only [Term.substitute]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih original member first second same)
  | condition _ _ _ ih₁ ih₂ ih₃ =>
      simp only [Term.substitute,ih₁ first second same,ih₂ first second same]
      congr 1
      apply ih₃ (liftSubstitution first) (liftSubstitution second)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp only [liftSubstitution,same i (Nat.lt_of_succ_lt_succ hi)]

 theorem liftRename_comp (first second : Nat → Nat) :
    (fun i => liftRename second (liftRename first i)) = liftRename (fun i => second (first i)) := by
  funext i; cases i <;> rfl

 theorem liftRename_substitution_comp (rename : Nat → Nat) (substitution : Nat → Term) :
    (fun i => liftSubstitution substitution (liftRename rename i)) =
      liftSubstitution (fun i => substitution (rename i)) := by
  funext i; cases i <;> rfl

 theorem scoped_rename_comp {n : Nat} {term : Term} (h : Scoped n term)
    (first : Nat → Nat) (second : Nat → Nat) :
    (term.rename first).rename second = term.rename (fun i => second (first i)) := by
  induction h generalizing first second with
  | bound _ => simp only [Term.rename,Term.rename]
  | lam h ih =>
      simp only [Term.rename,Term.rename,ih,liftRename_comp]
  | app _ _ ih₁ ih₂ => simp only [Term.rename,Term.rename,ih₁ first second,ih₂ first second]
  | mix _ _ ih₁ ih₂ => simp only [Term.rename,Term.rename,ih₁ first second,ih₂ first second]
  | fix _ _ ih₁ ih₂ => simp only [Term.rename,Term.rename,ih₁ first second,ih₂ first second]
  | specification _ _ ih₁ ih₂ => simp only [Term.rename,Term.rename,ih₁ first second,ih₂ first second]
  | prototype _ _ ih₁ ih₂ => simp only [Term.rename,Term.rename,ih₁ first second,ih₂ first second]
  | binary _ _ ih₁ ih₂ => simp only [Term.rename,Term.rename,ih₁ first second,ih₂ first second]
  | reflect _ ih => simp only [Term.rename,Term.rename,ih first second]
  | metadata _ ih => simp only [Term.rename,Term.rename,ih first second]
  | project _ ih => simp only [Term.rename,Term.rename,ih first second]
  | get _ ih => simp only [Term.rename,Term.rename,ih first second]
  | natural _ | boolean _ | label _ => simp only [Term.rename,Term.rename]
  | extend _ _ ih₁ ih₂ =>
      simp only [Term.rename,Term.rename,List.map_map,ih₁ first second]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih₂ original member first second)
  | record _ ih =>
      simp only [Term.rename,Term.rename,List.map_map]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih original member first second)
  | condition _ _ _ ih₁ ih₂ ih₃ =>
      simp only [Term.rename,Term.rename,ih₁ first second,ih₂ first second,ih₃,liftRename_comp]

 theorem scoped_rename_substitute {n : Nat} {term : Term} (h : Scoped n term)
    (first : Nat → Nat) (second : Nat → Term) :
    (term.rename first).substitute second = term.substitute (fun i => second (first i)) := by
  induction h generalizing first second with
  | bound _ => simp only [Term.rename,Term.substitute]
  | lam h ih =>
      simp only [Term.rename,Term.substitute,ih,liftRename_substitution_comp]
  | app _ _ ih₁ ih₂ => simp only [Term.rename,Term.substitute,ih₁ first second,ih₂ first second]
  | mix _ _ ih₁ ih₂ => simp only [Term.rename,Term.substitute,ih₁ first second,ih₂ first second]
  | fix _ _ ih₁ ih₂ => simp only [Term.rename,Term.substitute,ih₁ first second,ih₂ first second]
  | specification _ _ ih₁ ih₂ => simp only [Term.rename,Term.substitute,ih₁ first second,ih₂ first second]
  | prototype _ _ ih₁ ih₂ => simp only [Term.rename,Term.substitute,ih₁ first second,ih₂ first second]
  | binary _ _ ih₁ ih₂ => simp only [Term.rename,Term.substitute,ih₁ first second,ih₂ first second]
  | reflect _ ih => simp only [Term.rename,Term.substitute,ih first second]
  | metadata _ ih => simp only [Term.rename,Term.substitute,ih first second]
  | project _ ih => simp only [Term.rename,Term.substitute,ih first second]
  | get _ ih => simp only [Term.rename,Term.substitute,ih first second]
  | natural _ | boolean _ | label _ => simp only [Term.rename,Term.substitute]
  | extend _ _ ih₁ ih₂ =>
      simp only [Term.rename,Term.substitute,List.map_map,ih₁ first second]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih₂ original member first second)
  | record _ ih =>
      simp only [Term.rename,Term.substitute,List.map_map]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih original member first second)
  | condition _ _ _ ih₁ ih₂ ih₃ =>
      simp only [Term.rename,Term.substitute,ih₁ first second,ih₂ first second,ih₃,liftRename_substitution_comp]

 theorem lifted_substitution_scoped {n m : Nat} {substitution : Nat → Term}
    (images : ∀ i, i < n → Scoped m (substitution i)) :
    ∀ i, i < n+1 → Scoped (m+1) (liftSubstitution substitution i) := by
  intro i hi
  cases i with
  | zero => exact .bound (Nat.zero_lt_succ _)
  | succ i => exact scoped_weaken (images i (Nat.lt_of_succ_lt_succ hi))

 theorem lifted_substitution_rename {n m : Nat} {substitution : Nat → Term}
    (images : ∀ i, i < n → Scoped m (substitution i)) (rename : Nat → Nat) :
    ∀ i, i < n+1 →
      (liftSubstitution substitution i).rename (liftRename rename) =
        liftSubstitution (fun j => (substitution j).rename rename) i := by
  intro i hi
  cases i with
  | zero => simp [liftSubstitution,Term.rename,liftRename]
  | succ i =>
      simp only [liftSubstitution]
      rw [scoped_rename_comp (images i (Nat.lt_of_succ_lt_succ hi)),
        scoped_rename_comp (images i (Nat.lt_of_succ_lt_succ hi))]
      rfl

 theorem scoped_substitute_rename {n m : Nat} {term : Term} (h : Scoped n term)
    (substitution : Nat → Term) (images : ∀ i, i < n → Scoped m (substitution i))
    (rename : Nat → Nat) :
    (term.substitute substitution).rename rename =
      term.substitute (fun i => (substitution i).rename rename) := by
  induction h generalizing m substitution rename with
  | bound hi => simp only [Term.substitute]
  | lam h ih =>
      simp only [Term.substitute,Term.rename]
      congr 1
      rw [ih _ (lifted_substitution_scoped images)]
      exact scoped_substitution_congr h _ _ (lifted_substitution_rename images rename)
  | app _ _ ih₁ ih₂ => simp only [Term.substitute,Term.rename,ih₁ substitution images rename,ih₂ substitution images rename]
  | mix _ _ ih₁ ih₂ => simp only [Term.substitute,Term.rename,ih₁ substitution images rename,ih₂ substitution images rename]
  | fix _ _ ih₁ ih₂ => simp only [Term.substitute,Term.rename,ih₁ substitution images rename,ih₂ substitution images rename]
  | specification _ _ ih₁ ih₂ => simp only [Term.substitute,Term.rename,ih₁ substitution images rename,ih₂ substitution images rename]
  | prototype _ _ ih₁ ih₂ => simp only [Term.substitute,Term.rename,ih₁ substitution images rename,ih₂ substitution images rename]
  | binary _ _ ih₁ ih₂ => simp only [Term.substitute,Term.rename,ih₁ substitution images rename,ih₂ substitution images rename]
  | reflect _ ih => simp only [Term.substitute,Term.rename,ih substitution images rename]
  | metadata _ ih => simp only [Term.substitute,Term.rename,ih substitution images rename]
  | project _ ih => simp only [Term.substitute,Term.rename,ih substitution images rename]
  | get _ ih => simp only [Term.substitute,Term.rename,ih substitution images rename]
  | natural _ | boolean _ | label _ => simp only [Term.substitute,Term.rename]
  | extend _ _ ih₁ ih₂ =>
      simp only [Term.substitute,Term.rename,List.map_map,ih₁ substitution images rename]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih₂ original member substitution images rename)
  | record _ ih =>
      simp only [Term.substitute,Term.rename,List.map_map]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih original member substitution images rename)
  | condition _ _ h ih₁ ih₂ ih₃ =>
      simp only [Term.substitute,Term.rename,ih₁ substitution images rename,ih₂ substitution images rename]
      congr 1
      rw [ih₃ _ (lifted_substitution_scoped images)]
      exact scoped_substitution_congr h _ _ (lifted_substitution_rename images rename)

 theorem lifted_substitution_comp {n m k : Nat} {first second : Nat → Term}
    (images : ∀ i, i < n → Scoped m (first i))
    (nextImages : ∀ i, i < m → Scoped k (second i)) :
    ∀ i, i < n+1 → (liftSubstitution first i).substitute (liftSubstitution second) =
      liftSubstitution (fun j => (first j).substitute second) i := by
  intro i hi
  cases i with
  | zero => simp [liftSubstitution,Term.substitute]
  | succ i =>
      simp only [liftSubstitution]
      rw [scoped_rename_substitute (images i (Nat.lt_of_succ_lt_succ hi))]
      simpa only [liftSubstitution] using
        (scoped_substitute_rename (images i (Nat.lt_of_succ_lt_succ hi)) second nextImages Nat.succ).symm

 theorem scoped_substitute_comp {n m k : Nat} {term : Term} (h : Scoped n term)
    (first : Nat → Term) (images : ∀ i, i < n → Scoped m (first i))
    (second : Nat → Term) (nextImages : ∀ i, i < m → Scoped k (second i)) :
    (term.substitute first).substitute second =
      term.substitute (fun i => (first i).substitute second) := by
  induction h generalizing m k first second with
  | bound _ => simp only [Term.substitute]
  | lam h ih =>
      simp only [Term.substitute]
      congr 1
      rw [ih _ (lifted_substitution_scoped images) _ (lifted_substitution_scoped nextImages)]
      exact scoped_substitution_congr h _ _ (lifted_substitution_comp images nextImages)
  | app _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first images second nextImages,ih₂ first images second nextImages]
  | mix _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first images second nextImages,ih₂ first images second nextImages]
  | fix _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first images second nextImages,ih₂ first images second nextImages]
  | specification _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first images second nextImages,ih₂ first images second nextImages]
  | prototype _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first images second nextImages,ih₂ first images second nextImages]
  | binary _ _ ih₁ ih₂ => simp only [Term.substitute,ih₁ first images second nextImages,ih₂ first images second nextImages]
  | reflect _ ih => simp only [Term.substitute,ih first images second nextImages]
  | metadata _ ih => simp only [Term.substitute,ih first images second nextImages]
  | project _ ih => simp only [Term.substitute,ih first images second nextImages]
  | get _ ih => simp only [Term.substitute,ih first images second nextImages]
  | natural _ | boolean _ | label _ => simp only [Term.substitute]
  | extend _ _ ih₁ ih₂ =>
      simp only [Term.substitute,List.map_map,ih₁ first images second nextImages]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih₂ original member first images second nextImages)
  | record _ ih =>
      simp only [Term.substitute,List.map_map]
      congr 1
      apply List.map_congr_left
      intro original member
      exact Prod.ext rfl (ih original member first images second nextImages)
  | condition _ _ h ih₁ ih₂ ih₃ =>
      simp only [Term.substitute,ih₁ first images second nextImages,ih₂ first images second nextImages]
      congr 1
      rw [ih₃ _ (lifted_substitution_scoped images) _ (lifted_substitution_scoped nextImages)]
      exact scoped_substitution_congr h _ _ (lifted_substitution_comp images nextImages)

/-- The assignment gives each address a finite source computation; it does NOT
recursively unfold its pointers. In particular a recursive address can denote a
source Fix while its origin denotes the one-step expansion of that same Fix. -/
abbrev AddressMeaning := Address → Term

def environmentSubstitution (meaning : AddressMeaning) (environment : Environment) (index : Nat) : Term :=
  match environment[index]? with
  | some address => meaning address
  | none => .bound index

def closeTerm (meaning : AddressMeaning) (environment : Environment) (term : Term) : Term :=
  match environment with
  | [] => term
  | _::_ => term.substitute (environmentSubstitution meaning environment)

def closeOrigin (meaning : AddressMeaning) (origin : Closure) : Term :=
  closeTerm meaning origin.environment origin.term

def valueMeaning (meaning : AddressMeaning) : RuntimeValue → Term
  | .closure body environment => closeTerm meaning environment (.lam body)
  | .natural value => .nat value
  | .boolean value => .boolean value
  | .label value => .label value
  | .record fields => .record (fields.map fun field => (field.1,meaning field.2))
  | .specification metadata extension => .specification (meaning metadata) (meaning extension)
  | .prototype specification target => .prototype (meaning specification) (meaning target)

/- The evaluating phase retains its source meaning. A cache additionally has
an actual independent reference evaluation, rather than an arbitrary cached
scalar. Stable origins let the same relation survive the phase change. -/
/-- Each allocated graph name denotes a closed source computation. The
assignment remains finite syntax even when these computations contain Fix. -/
def MeaningsScoped (bound : Nat) (meaning : AddressMeaning) : Prop :=
  ∀ address, address < bound → Scoped 0 (meaning address)

 theorem environmentSubstitution_scoped {bound : Nat} {meaning : AddressMeaning}
    {environment : Environment} (names : MeaningsScoped bound meaning)
    (captures : EnvironmentValid bound environment) :
    ∀ index, index < environment.length → Scoped 0 (environmentSubstitution meaning environment index) := by
  intro index hi
  have found : environment[index]? = some environment[index] := getElem?_pos environment index hi
  simpa [environmentSubstitution,found] using names _ (captures _ (List.mem_of_getElem? found))

 theorem closeTerm_eq_substitution {meaning : AddressMeaning} {environment : Environment}
    {term : Term} (h : Scoped environment.length term) :
    closeTerm meaning environment term = term.substitute (environmentSubstitution meaning environment) := by
  cases environment with
  | nil =>
      exact (scoped_substitute_identity h _ (by intro i hi; simp at hi)).symm
  | cons _ _ => rfl

/-- Extending an allocated prefix cannot change the source meaning of a
lexical capture. The agreement is only required at actually allocated names. -/
 theorem closeTerm_meaning_congr {bound : Nat} {first second : AddressMeaning}
    {environment : Environment} {term : Term} (captures : EnvironmentValid bound environment)
    (scope : Scoped environment.length term) (same : ∀ address, address < bound → first address = second address) :
    closeTerm first environment term = closeTerm second environment term := by
  rw [closeTerm_eq_substitution scope,closeTerm_eq_substitution scope]
  apply scoped_substitution_congr scope
  intro index hi
  have found : environment[index]? = some environment[index] := getElem?_pos environment index hi
  simp only [environmentSubstitution,found]
  exact same _ (captures _ (List.mem_of_getElem? found))

/-- A call allocates a name for its lazy argument. This equation proves that
entering the captured body with that name is exactly independent source beta
substitution, even when the environment points into a cyclic heap. -/
 theorem closeTerm_beta {bound : Nat} {meaning extended : AddressMeaning}
    {captured : Environment} {body argument : Term}
    (names : MeaningsScoped bound meaning) (captures : EnvironmentValid bound captured)
    (bodyScope : Scoped (captured.length+1) body) (argumentScope : Scoped 0 argument)
    (same : ∀ address, address < bound → meaning address = extended address)
    (fresh : extended bound = argument) :
    instantiate (body.substitute (liftSubstitution (environmentSubstitution meaning captured))) argument =
      closeTerm extended (bound::captured) body := by
  let sigma := environmentSubstitution meaning captured
  let inst : Nat → Term := fun i => match i with | 0 => argument | n+1 => .bound n
  have images : ∀ i, i < captured.length → Scoped 0 (sigma i) :=
    environmentSubstitution_scoped names captures
  have nextImages : ∀ i, i < 1 → Scoped 0 (inst i) := by
    intro i hi
    have : i = 0 := by omega
    subst i
    exact argumentScope
  change (body.substitute (liftSubstitution sigma)).substitute inst = _
  rw [scoped_substitute_comp bodyScope _ (lifted_substitution_scoped images) inst nextImages]
  rw [closeTerm_eq_substitution (by simpa using bodyScope)]
  apply scoped_substitution_congr bodyScope
  intro i hi
  cases i with
  | zero => simp [liftSubstitution,Term.substitute,environmentSubstitution,fresh,inst]
  | succ i =>
      have lt : i < captured.length := by omega
      have closed := images i lt
      have renameSame := scoped_rename_identity closed Nat.succ (by intro j hj; omega)
      have substSame := scoped_substitute_identity closed inst (by intro j hj; omega)
      have found : captured[i]? = some captured[i] := getElem?_pos captured i lt
      simp only [liftSubstitution,renameSame,substSame,environmentSubstitution,List.getElem?_cons_succ,found]
      simpa only [sigma,environmentSubstitution,found] using same _ (captures _ (List.mem_of_getElem? found))

 theorem closeTerm_scoped {bound : Nat} {meaning : AddressMeaning} {environment : Environment}
    {term : Term} (names : MeaningsScoped bound meaning)
    (captures : EnvironmentValid bound environment) (hscope : Scoped environment.length term) :
    Scoped 0 (closeTerm meaning environment term) := by
  cases environment with
  | nil => exact hscope
  | cons address rest =>
      apply scoped_substitute hscope (environmentSubstitution meaning (address::rest)) 0
      intro index hi
      have found : (address::rest)[index]? = some (address::rest)[index] := getElem?_pos (address::rest) index hi
      have allocated := captures _ (List.mem_of_getElem? found)
      simpa [environmentSubstitution,found] using names _ allocated

 theorem valueMeaning_scoped {bound : Nat} {meaning : AddressMeaning} {value : RuntimeValue}
    (names : MeaningsScoped bound meaning) (valid : RuntimeValueValid bound value) :
    Scoped 0 (valueMeaning meaning value) := by
  cases value with
  | closure body environment => exact closeTerm_scoped names valid.2 (Scoped.lam valid.1)
  | natural n => exact .natural _
  | boolean n => exact .boolean _
  | label n => exact .label _
  | record fields =>
      apply Scoped.record
      intro field member
      obtain ⟨original,ho,rfl⟩ := List.mem_map.mp member
      exact names _ (valid original ho)
  | specification metadata extension => exact .specification (names _ valid.1) (names _ valid.2)
  | prototype specification target => exact .prototype (names _ valid.1) (names _ valid.2)

def CellRealizes (meaning : AddressMeaning) (address : Address) (cell : Cell) : Prop :=
  Steps (meaning address) (closeOrigin meaning (cellOrigin cell)) ∧
    match cell with
    | .cached _ value => Evaluates (meaning address) (valueMeaning meaning value)
    | _ => True

def HeapRealizes (meaning : AddressMeaning) (heap : Array Cell) : Prop :=
  ∀ (address : Nat) (cell : Cell), heap[address]? = some cell → CellRealizes meaning address cell

 theorem valueMeaning_congr {bound : Nat} {first second : AddressMeaning} {value : RuntimeValue}
    (valid : RuntimeValueValid bound value)
    (same : ∀ address, address < bound → first address = second address) :
    valueMeaning first value = valueMeaning second value := by
  cases value with
  | closure body environment => exact closeTerm_meaning_congr valid.2 (Scoped.lam valid.1) same
  | natural _ | boolean _ | label _ => rfl
  | record fields =>
      simp only [valueMeaning]
      congr 1
      apply List.map_congr_left
      intro field member
      exact Prod.ext rfl (same _ (valid field member))
  | specification metadata extension => simp only [valueMeaning,same _ valid.1,same _ valid.2]
  | prototype specification target => simp only [valueMeaning,same _ valid.1,same _ valid.2]

 theorem cellRealizes_congr {bound address : Nat} {first second : AddressMeaning} {cell : Cell}
    (allocated : address < bound) (valid : CellValid bound cell)
    (same : ∀ address, address < bound → first address = second address) :
    CellRealizes first address cell ↔ CellRealizes second address cell := by
  cases cell with
  | suspended origin | evaluating origin =>
      simp only [CellRealizes,cellOrigin,closeOrigin,same _ allocated,
        closeTerm_meaning_congr valid.2 valid.1 same]
  | cached origin value =>
      simp only [CellRealizes,cellOrigin,closeOrigin,same _ allocated,
        closeTerm_meaning_congr valid.1.2 valid.1.1 same,valueMeaning_congr valid.2 same]

 theorem heapRealizes_congr {heap : Array Cell} {first second : AddressMeaning}
    (valid : HeapValid heap) (same : ∀ address, address < heap.size → first address = second address)
    (realizes : HeapRealizes first heap) : HeapRealizes second heap := by
  intro address cell found
  have allocated := (Array.getElem?_eq_some_iff.mp found).1
  exact (cellRealizes_congr allocated (valid address cell found) same).mp (realizes address cell found)

 theorem heapRealizes_push {heap : Array Cell} {meaning : AddressMeaning} {cell : Cell}
    (realizes : HeapRealizes meaning heap) (fresh : CellRealizes meaning heap.size cell) :
    HeapRealizes meaning (heap.push cell) := by
  intro address other found
  by_cases eq : address = heap.size
  · subst address
    simp at found
    subst other
    exact fresh
  · apply realizes address other
    simpa [Array.getElem?_push,eq] using found

def frameMeaning (meaning : AddressMeaning) (frame : Frame) (hole : Term) : Term :=
  match frame with
  | .argument term environment => .app hole (closeTerm meaning environment term)
  | .update _ => hole
  | .field name => .get hole name
  | .reflect => .reflect hole
  | .metadata => .metadata hole
  | .project => .project hole
  | .extend fields environment => .extend hole
      (fields.map fun field => (field.1,closeTerm meaning environment field.2))
  | .condition zero successorBody environment => .ifZero hole
      (closeTerm meaning environment zero)
      (successorBody.substitute (liftSubstitution (environmentSubstitution meaning environment)))
  | .binaryLeft primitive right environment => .binary primitive hole (closeTerm meaning environment right)
  | .binaryRight primitive left => .binary primitive (valueMeaning meaning left) hole

 theorem frameMeaning_congr {bound : Nat} {first second : AddressMeaning} {frame : Frame} {hole : Term}
    (valid : FrameValid bound frame)
    (same : ∀ address, address < bound → first address = second address) :
    frameMeaning first frame hole = frameMeaning second frame hole := by
  cases frame with
  | argument term environment | binaryLeft primitive term environment =>
      simp only [frameMeaning,closeTerm_meaning_congr valid.2 valid.1 same]
  | update _ | field _ | reflect | metadata | project => rfl
  | binaryRight primitive value => simp only [frameMeaning,valueMeaning_congr valid same]
  | extend fields environment =>
      simp only [frameMeaning]
      congr 1
      apply List.map_congr_left
      intro field member
      exact Prod.ext rfl (closeTerm_meaning_congr valid.1 (valid.2 field member) same)
  | condition zero body environment =>
      simp only [frameMeaning,closeTerm_meaning_congr valid.1 valid.2.1 same]
      congr 1
      apply scoped_substitution_congr valid.2.2
      intro i hi
      cases i with
      | zero => rfl
      | succ i =>
          have lt : i < environment.length := by omega
          have found : environment[i]? = some environment[i] := getElem?_pos environment i lt
          simp only [liftSubstitution,environmentSubstitution,found,same _ (valid.1 _ (List.mem_of_getElem? found))]

def stackMeaning (meaning : AddressMeaning) (stack : List Frame) (hole : Term) : Term :=
  stack.foldl (fun prior frame => frameMeaning meaning frame prior) hole

def controlMeaning (meaning : AddressMeaning) : Control → Option Term
  | .evaluate term environment => some (closeTerm meaning environment term)
  | .enter address => some (meaning address)
  | .returned value | .complete value => some (valueMeaning meaning value)
  | .blackhole _ | .refused _ => none

 theorem valueMeaning_value (meaning : AddressMeaning) (value : RuntimeValue) :
    Value (valueMeaning meaning value) := by
  cases value with
  | closure body environment =>
      cases environment <;> simp only [valueMeaning,closeTerm,Term.substitute]
      all_goals exact .function _
  | natural n => exact .natural _
  | boolean n => exact .boolean _
  | label n => exact .label _
  | record fields => exact .record _
  | specification _ _ => exact .specification _ _
  | prototype _ _ => exact .prototype _ _

 theorem sourceSteps_frame (meaning : AddressMeaning) (frame : Frame)
    {before after : Term} (steps : Steps before after) :
    Steps (frameMeaning meaning frame before) (frameMeaning meaning frame after) := by
  induction steps with
  | refl => exact .refl _
  | next step steps ih =>
      apply Steps.next _ ih
      cases frame with
      | argument term environment => exact .application _ step
      | update _ => exact step
      | field name => exact .target _ step
      | reflect => exact .reflectStep step
      | metadata => exact .metadataStep step
      | project => exact .projectStep step
      | extend fields environment => exact .extendTarget _ step
      | condition zero successorBody environment => exact .condition _ _ step
      | binaryLeft primitive right environment => exact .binaryLeft _ _ step
      | binaryRight primitive left => exact .binaryRight _ _ (valueMeaning_value _ _) step

/-- Every active update carries its own demand-segment source evaluation.
Erasing update frames would lose the LOCAL proof required when writing a cache:
a whole-program reduction alone cannot justify that heap-cell result. -/
def StackRealizes (meaning : AddressMeaning) (root focus : Term) : List Frame → Prop
  | [] => Steps root focus
  | .update address::rest =>
      Steps (meaning address) focus ∧ StackRealizes meaning root (meaning address) rest
  | frame::rest => StackRealizes meaning root (frameMeaning meaning frame focus) rest

 theorem stackRealizes_congr {bound : Nat} {first second : AddressMeaning} {root focus : Term}
    {stack : List Frame} (valid : ∀ frame ∈ stack, FrameValid bound frame)
    (same : ∀ address, address < bound → first address = second address)
    (realizes : StackRealizes first root focus stack) : StackRealizes second root focus stack := by
  induction stack generalizing focus with
  | nil => exact realizes
  | cons frame rest ih =>
      have hv := valid frame (List.mem_cons_self ..)
      have ht : ∀ frame ∈ rest, FrameValid bound frame := fun f member => valid f (List.mem_cons_of_mem _ member)
      cases frame with
      | update address =>
          exact ⟨by simpa only [StackRealizes,same _ hv] using realizes.1,
            by simpa only [same _ hv] using ih ht realizes.2⟩
      | argument _ _ | field _ | reflect | metadata | project | extend _ _ | condition _ _ _ | binaryLeft _ _ _ | binaryRight _ _ =>
          simpa only [StackRealizes,frameMeaning_congr hv same] using ih ht realizes

 theorem stackRealizes_steps {meaning : AddressMeaning} {root before after : Term}
    {stack : List Frame} (realizes : StackRealizes meaning root before stack)
    (steps : Steps before after) : StackRealizes meaning root after stack := by
  induction stack generalizing before after with
  | nil => exact sourceSteps_trans realizes steps
  | cons frame rest ih =>
      cases frame with
      | update address => exact ⟨sourceSteps_trans realizes.1 steps,realizes.2⟩
      | argument _ _ | field _ | reflect | metadata | project | extend _ _ | condition _ _ _ | binaryLeft _ _ _ | binaryRight _ _ =>
          exact ih realizes (sourceSteps_frame _ _ steps)

 theorem heapRealizes_set {meaning : AddressMeaning} {heap : Array Cell}
    {address : Nat} {cell : Cell} (realizes : HeapRealizes meaning heap)
    (valid : CellRealizes meaning address cell) : HeapRealizes meaning (heap.set! address cell) := by
  intro index other found
  by_cases bound : address < heap.size
  · by_cases same : index = address
    · subst index
      simp [Array.set!,bound] at found
      subst other
      exact valid
    · apply realizes index other
      simpa [Array.set!,same,Ne.symm same] using found
  · apply realizes index other
    simpa [Array.set!,Array.setIfInBounds,bound] using found

/-- The cache proof is recovered from the actual local update segment, not an
assumed evaluator oracle. This works for cyclic assignments and arbitrary
runtime closures/records as well as scalars. -/
 theorem cachedCell_realizes {meaning : AddressMeaning} {heap : Array Cell}
    {address : Nat} {origin : Closure} {root : Term} {rest : List Frame} {value : RuntimeValue}
    (heapRealizes : HeapRealizes meaning heap)
    (found : heap[address]? = some (.evaluating origin))
    (stackRealizes : StackRealizes meaning root (valueMeaning meaning value) (.update address::rest)) :
    CellRealizes meaning address (.cached origin value) :=
  ⟨(heapRealizes address _ found).1,stackRealizes.1,valueMeaning_value _ _⟩

/-- This is a concrete heap/continuation relation, not a record of assumed
simulation fields. Its initialization and finished-ground consequence are
proved below. Preservation through execution remains an explicit open theorem. -/
def GraphRepresents (state : State) (source : Term) : Prop :=
  LexicalInvariant state ∧ BusyInvariant state ∧ FinalStackInvariant state ∧ ∃ meaning, MeaningsScoped state.heap.size meaning ∧ HeapRealizes meaning state.heap ∧
    ∃ residual, controlMeaning meaning state.control = some residual ∧
      StackRealizes meaning source residual state.stack

 theorem graph_initializes {source : Term} (closed : Scoped 0 source) :
    GraphRepresents (initial source) source := by
  refine ⟨initial_lexicalInvariant closed,initial_busyInvariant source,initial_finalStackInvariant source,fun _ => .bound 0,?_,?_,source,?_,?_⟩
  · intro address allocated; simp [initial] at allocated
  · intro address cell found; simp [initial] at found
  · rfl
  · exact .refl _

 theorem graph_complete_natural_sound {state : State} {source : Term} {number : Nat}
    (represented : GraphRepresents state source)
    (complete : state.control = .complete (.natural number)) :
    Evaluates source (.nat number) := by
  obtain ⟨_,_,final,meaning,_,_,residual,control,steps⟩ := represented
  have empty := final _ complete
  simp [complete,controlMeaning,valueMeaning] at control
  subst residual
  simpa [empty,StackRealizes] using And.intro steps (Value.natural number)

 theorem graph_complete_label_sound {state : State} {source : Term} {name : String}
    (represented : GraphRepresents state source)
    (complete : state.control = .complete (.label name)) :
    Evaluates source (.label name) := by
  obtain ⟨_,_,final,meaning,_,_,residual,control,steps⟩ := represented
  have empty := final _ complete
  simp [complete,controlMeaning,valueMeaning] at control
  subst residual
  simpa [empty,StackRealizes] using And.intro steps (Value.label name)

 theorem graph_complete_boolean_sound {state : State} {source : Term} {value : Bool}
    (represented : GraphRepresents state source)
    (complete : state.control = .complete (.boolean value)) :
    Evaluates source (.boolean value) := by
  obtain ⟨_,_,final,meaning,_,_,residual,control,steps⟩ := represented
  have empty := final _ complete
  simp [complete,controlMeaning,valueMeaning] at control
  subst residual
  simpa [empty,StackRealizes] using And.intro steps (Value.boolean value)

/-- The source contexts that start a lexical demand without allocating heap
cells. This enumerates actual syntax and actual machine frames. -/
inductive DemandContext where
  | argument (term : Term)
  | field (name : String)
  | reflect | metadata | project
  | extend (fields : List (String × Term))
  | condition (zero successorBody : Term)
  | binary (primitive : Primitive) (right : Term)

def DemandContext.term : DemandContext → Term → Term
  | .argument arg, hole => .app hole arg
  | .field name, hole => .get hole name
  | .reflect, hole => .reflect hole
  | .metadata, hole => .metadata hole
  | .project, hole => .project hole
  | .extend fields, hole => .extend hole fields
  | .condition zero successorBody, hole => .ifZero hole zero successorBody
  | .binary primitive right, hole => .binary primitive hole right

def DemandContext.frame : DemandContext → Environment → Frame
  | .argument arg, environment => .argument arg environment
  | .field name, _ => .field name
  | .reflect, _ => .reflect
  | .metadata, _ => .metadata
  | .project, _ => .project
  | .extend fields, environment => .extend fields environment
  | .condition zero successorBody, environment => .condition zero successorBody environment
  | .binary primitive right, environment => .binaryLeft primitive right environment

 theorem demandContext_closes (context : DemandContext) (meaning : AddressMeaning)
    (environment : Environment) (hole : Term)
    (scope : Scoped environment.length (context.term hole)) :
    closeTerm meaning environment (context.term hole) =
      frameMeaning meaning (context.frame environment) (closeTerm meaning environment hole) := by
  cases environment with
  | cons address rest => cases context <;> simp [DemandContext.term,DemandContext.frame,closeTerm,Term.substitute,frameMeaning]
  | nil =>
      have lifted : liftSubstitution (environmentSubstitution meaning []) = Term.bound := by
        funext i
        cases i <;> simp [liftSubstitution,environmentSubstitution,Term.rename]
      cases context with
      | condition zero body =>
          have scopedBody : Scoped 1 body := (scoped_condition_iff ..).mp scope |>.2.2
          simp only [DemandContext.term,DemandContext.frame,closeTerm,frameMeaning,lifted,
            scoped_substitute_identity scopedBody Term.bound (by intros; rfl)]
      | extend fields => simp [DemandContext.term,DemandContext.frame,closeTerm,frameMeaning]
      | argument _ | field _ | reflect | metadata | project | binary _ _ => rfl

 theorem demandContext_dispatch {state : State} {context : DemandContext} {hole : Term} {environment : Environment}
    (evaluate : state.control = .evaluate (context.term hole) environment) :
    stepRaw state = {state with control := .evaluate hole environment,stack := context.frame environment::state.stack} := by
  cases context <;> simp [stepRaw,evaluate,DemandContext.term,DemandContext.frame]

/-- Every demand-starting context advances through the real dispatcher,
including fields, reflection, extension, conditionals and binary operands. -/
 theorem graph_evaluate_context {state : State} {source hole : Term} {context : DemandContext} {environment : Environment}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (context.term hole) environment) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have scope : Scoped environment.length (context.term hole) := by
    have valid := lexical.2.1
    rw [evaluate] at valid
    exact valid.1
  simp [controlMeaning,evaluate] at control
  subst focus
  have dispatched := demandContext_dispatch evaluate
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,meaning,?_,?_,closeTerm meaning environment hole,?_,?_⟩
  · simpa only [dispatched] using names
  · simpa only [dispatched] using heap
  · simp only [dispatched,controlMeaning]
  · rw [demandContext_closes context meaning environment hole scope] at stack
    cases context <;> simpa only [dispatched,DemandContext.frame,StackRealizes] using stack

 theorem graph_evaluate_bound {state : State} {source : Term} {environment : Environment} {index address : Nat}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (.bound index) environment)
    (found : environment[index]? = some address) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have closes : closeTerm meaning environment (.bound index) = meaning address := by
    cases environment with
    | nil => simp at found
    | cons _ _ => simp [closeTerm,Term.substitute,environmentSubstitution,found]
  simp [controlMeaning,evaluate,closes] at control
  subst focus
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,meaning,?_,?_,meaning address,?_,?_⟩
  · simpa [stepRaw,evaluate,found] using names
  · simpa [stepRaw,evaluate,found] using heap
  · simp [stepRaw,evaluate,found,controlMeaning]
  · simpa [stepRaw,evaluate,found] using stack

inductive ImmediateValue where
  | closure (body : Term)
  | natural (number : Nat)
  | boolean (value : Bool)
  | label (name : String)

def ImmediateValue.term : ImmediateValue → Term
  | .closure body => .lam body
  | .natural number => .nat number
  | .boolean value => .boolean value
  | .label name => .label name

def ImmediateValue.runtime : ImmediateValue → Environment → RuntimeValue
  | .closure body, environment => .closure body environment
  | .natural number, _ => .natural number
  | .boolean value, _ => .boolean value
  | .label name, _ => .label name

 theorem graph_evaluate_immediate {state : State} {source : Term} {immediate : ImmediateValue} {environment : Environment}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate immediate.term environment) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have denotes : valueMeaning meaning (immediate.runtime environment) = closeTerm meaning environment immediate.term := by
    cases immediate <;> cases environment <;> simp [ImmediateValue.term,ImmediateValue.runtime,valueMeaning,closeTerm,Term.substitute]
  simp [controlMeaning,evaluate] at control
  subst focus
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,meaning,?_,?_,valueMeaning meaning (immediate.runtime environment),?_,?_⟩
  · cases immediate <;> simpa [stepRaw,evaluate,ImmediateValue.term] using names
  · cases immediate <;> simpa [stepRaw,evaluate,ImmediateValue.term] using heap
  · cases immediate <;> simp [stepRaw,evaluate,ImmediateValue.term,ImmediateValue.runtime,controlMeaning]
  · rw [denotes]
    cases immediate <;> simpa [stepRaw,evaluate,ImmediateValue.term] using stack

inductive ObjectAccess where
  | reflect | metadata | project

def ObjectAccess.frame : ObjectAccess → Frame
  | .reflect => .reflect | .metadata => .metadata | .project => .project

def ObjectAccess.value : ObjectAccess → Address → Address → RuntimeValue
  | .reflect, first, second => .prototype first second
  | .metadata, first, second => .specification first second
  | .project, first, second => .prototype first second

def ObjectAccess.address : ObjectAccess → Address → Address → Address
  | .reflect, first, _ => first | .metadata, first, _ => first | .project, _, second => second

 theorem graph_object_access {state : State} {source : Term} {access : ObjectAccess} {first second : Address} {rest : List Frame}
    (represented : GraphRepresents state source)
    (returned : state.control = .returned (access.value first second))
    (head : state.stack = access.frame::rest) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned] at control
  subst focus
  have before : StackRealizes meaning source
      (frameMeaning meaning access.frame (valueMeaning meaning (access.value first second))) rest := by
    cases access <;> simpa [head,ObjectAccess.frame,StackRealizes] using stack
  have reduce : Step (frameMeaning meaning access.frame (valueMeaning meaning (access.value first second)))
      (meaning (access.address first second)) := by
    cases access with
    | reflect => exact Step.reflectPrototype _ _
    | metadata => exact Step.metadataSpecification _ _
    | project => exact Step.projectPrototype _ _
  have advanced := stackRealizes_steps before (Steps.next reduce (Steps.refl _))
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,meaning,?_,?_,meaning (access.address first second),?_,?_⟩
  · cases access <;> simpa [stepRaw,returned,head,ObjectAccess.frame,ObjectAccess.value] using names
  · cases access <;> simpa [stepRaw,returned,head,ObjectAccess.frame,ObjectAccess.value] using heap
  · cases access <;> simp [stepRaw,returned,head,ObjectAccess.frame,ObjectAccess.value,ObjectAccess.address,controlMeaning]
  · cases access <;> simpa [stepRaw,returned,head,ObjectAccess.frame,ObjectAccess.value] using advanced

 theorem graph_specification_call {state : State} {source argument : Term} {environment : Environment}
    {descriptor extension : Address} {rest : List Frame} (represented : GraphRepresents state source)
    (returned : state.control = .returned (.specification descriptor extension))
    (head : state.stack = .argument argument environment::rest) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned] at control
  subst focus
  have before : StackRealizes meaning source
      (.app (.specification (meaning descriptor) (meaning extension)) (closeTerm meaning environment argument)) rest := by
    simpa only [head,StackRealizes,frameMeaning,valueMeaning] using stack
  have advanced := stackRealizes_steps before (Steps.next (Step.applySpecification _ _ _) (Steps.refl _))
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,meaning,?_,?_,meaning extension,?_,?_⟩
  · simpa [stepRaw,returned,head] using names
  · simpa [stepRaw,returned,head] using heap
  · simp [stepRaw,returned,head,controlMeaning]
  · simpa [stepRaw,returned,head,StackRealizes,frameMeaning] using advanced

 theorem valueTerm_meaning {value : RuntimeValue} {term : Term} (found : valueTerm value = some term)
    (meaning : AddressMeaning) : valueMeaning meaning value = term := by
  cases value <;> simp [valueTerm] at found
  all_goals subst term; rfl

 theorem scalarValue_meaning {value : RuntimeValue} {term : Term} (found : scalarValue term = some value)
    (meaning : AddressMeaning) : valueMeaning meaning value = term := by
  cases term <;> simp [scalarValue] at found
  all_goals subst value; rfl

/-- Every successful primitive dispatch performs the independent source
primitive step. The premises are the actual dispatch branches, rather than a
semantic oracle; all four primitives and all scalar results are covered. -/
 theorem graph_primitive_return {state : State} {source result : Term} {primitive : Primitive}
    {left right next : RuntimeValue} {rest : List Frame}
    (represented : GraphRepresents state source) (returned : state.control = .returned right)
    (head : state.stack = .binaryRight primitive left::rest)
    (dispatch : (valueTerm left).bind (fun l => (valueTerm right).bind (primitiveResult primitive l)) = some result)
    (scalar : scalarValue result = some next) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned] at control
  subst focus
  obtain ⟨leftTerm,leftFound,rightResult⟩ := Option.bind_eq_some_iff.mp dispatch
  obtain ⟨rightTerm,rightFound,primitiveFound⟩ := Option.bind_eq_some_iff.mp rightResult
  have reduce : Step (.binary primitive (valueMeaning meaning left) (valueMeaning meaning right)) (valueMeaning meaning next) := by
    have rule := Step.primitive primitive _ _ result (valueMeaning_value meaning left) (valueMeaning_value meaning right)
      (by simpa only [valueTerm_meaning leftFound meaning,valueTerm_meaning rightFound meaning] using primitiveFound)
    simpa only [scalarValue_meaning scalar meaning] using rule
  have before : StackRealizes meaning source (.binary primitive (valueMeaning meaning left) (valueMeaning meaning right)) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  have advanced := stackRealizes_steps before (Steps.next reduce (Steps.refl _))
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,meaning,?_,?_,valueMeaning meaning next,?_,?_⟩
  · simpa [stepRaw,returned,head,dispatch,scalar] using names
  · simpa [stepRaw,returned,head,dispatch,scalar] using heap
  · simp [stepRaw,returned,head,dispatch,scalar,controlMeaning]
  · simpa [stepRaw,returned,head,dispatch,scalar] using advanced

/-- General suspended→evaluating transition preserves the complete graph
relation, installing local source provenance at its actual update frame. -/
 theorem graph_enter_suspended {state : State} {source : Term} {address : Nat} {origin : Closure}
    (represented : GraphRepresents state source) (enter : state.control = .enter address)
    (found : state.heap[address]? = some (.suspended origin)) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,enter] at control
  subst focus
  have oldCell := heap address _ found
  have newCell : CellRealizes meaning address (.evaluating origin) := oldCell
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,stepRaw_finalStackInvariant final,meaning,?_,?_,
    closeOrigin meaning origin,?_,?_⟩
  · simpa [stepRaw,enter,found] using names
  · simpa [stepRaw,enter,found] using heapRealizes_set heap newCell
  · simp [stepRaw,enter,found,controlMeaning,closeOrigin]
  · simpa [stepRaw,enter,found,StackRealizes] using And.intro oldCell.1 stack

/-- General evaluating→cached transition preserves the graph relation, using
the LOCAL update-segment derivation to certify the cell and to advance its
consumers. Closure/record caches are covered, and cyclic origins are allowed. -/
 theorem graph_cache_update {state : State} {source : Term} {address : Nat}
    {rest : List Frame} {value : RuntimeValue}
    (represented : GraphRepresents state source) (returned : state.control = .returned value)
    (update : state.stack = .update address::rest) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  obtain ⟨origin,found⟩ := busy_update_exists busy update
  simp [controlMeaning,returned] at control
  subst focus
  have segments : StackRealizes meaning source (valueMeaning meaning value) (.update address::rest) :=
    update ▸ stack
  have cached := cachedCell_realizes heap found segments
  have consumers := stackRealizes_steps segments.2 segments.1
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,stepRaw_finalStackInvariant final,meaning,?_,?_,
    valueMeaning meaning value,?_,?_⟩
  · simpa [stepRaw,returned,update,found] using names
  · simpa [stepRaw,returned,update,found] using heapRealizes_set heap cached
  · simp [stepRaw,returned,update,found,controlMeaning]
  · simpa [stepRaw,returned,update,found] using consumers

/-- A later demand reuses the memoized value, with independent source
reduction justified by the cache's graph relation. It covers all value shapes. -/
 theorem graph_enter_cached {state : State} {source : Term} {address : Nat}
    {origin : Closure} {value : RuntimeValue}
    (represented : GraphRepresents state source) (enter : state.control = .enter address)
    (found : state.heap[address]? = some (.cached origin value)) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,enter] at control
  subst focus
  have cached := heap address _ found
  have consumed := stackRealizes_steps stack cached.2.1
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,meaning,?_,?_,valueMeaning meaning value,?_,?_⟩
  · simpa [stepRaw,enter,found] using names
  · simpa [stepRaw,enter,found] using heap
  · simp [stepRaw,enter,found,controlMeaning]
  · simpa [stepRaw,enter,found] using consumed

 theorem closeTerm_app (meaning : AddressMeaning) (environment : Environment) (function argument : Term) :
    closeTerm meaning environment (.app function argument) =
      .app (closeTerm meaning environment function) (closeTerm meaning environment argument) := by
  cases environment <;> simp [closeTerm,Term.substitute]

 theorem closeTerm_lambda {meaning : AddressMeaning} {environment : Environment} {body : Term}
    (scope : Scoped (environment.length+1) body) :
    closeTerm meaning environment (.lam body) =
      .lam (body.substitute (liftSubstitution (environmentSubstitution meaning environment))) := by
  rw [closeTerm_eq_substitution (Scoped.lam scope)]
  simp only [Term.substitute]

def extendMeaning (meaning : AddressMeaning) (address : Address) (term : Term) : AddressMeaning :=
  fun index => if index = address then term else meaning index

 theorem extendMeaning_prefix (meaning : AddressMeaning) (bound : Nat) (term : Term) :
    ∀ address, address < bound → meaning address = extendMeaning meaning bound term address := by
  intro address allocated
  simp [extendMeaning,Nat.ne_of_lt allocated]

/-- The shared allocation lemma records the actual suspended origin, its
closed source name and exact agreement at every old allocated address. -/
 theorem allocateClosure_realizes {heap : Array Cell} {meaning : AddressMeaning}
    {term : Term} {environment : Environment} (validHeap : HeapValid heap)
    (names : MeaningsScoped heap.size meaning) (realizes : HeapRealizes meaning heap)
    (scope : Scoped environment.length term) (captures : EnvironmentValid heap.size environment) :
    ∃ extended : AddressMeaning,
      MeaningsScoped (heap.push (.suspended ⟨term,environment⟩)).size extended ∧
      HeapRealizes extended (heap.push (.suspended ⟨term,environment⟩)) ∧
      (∀ address, address < heap.size → meaning address = extended address) ∧
      extended heap.size = closeTerm meaning environment term := by
  let source := closeTerm meaning environment term
  let extended := extendMeaning meaning heap.size source
  have same : ∀ address, address < heap.size → meaning address = extended address :=
    extendMeaning_prefix _ _ _
  have fresh : extended heap.size = source := by simp [extended,extendMeaning]
  have closed := closeTerm_scoped names captures scope
  refine ⟨extended,?_,?_,same,fresh⟩
  · intro address allocated
    by_cases eq : address = heap.size
    · subst address; simpa only [fresh] using closed
    · have old : address < heap.size := by simp only [Array.size_push] at allocated; omega
      simpa only [←same address old] using names address old
  · apply heapRealizes_push (heapRealizes_congr validHeap same realizes)
    refine ⟨?_,True.intro⟩
    have originEq := closeTerm_meaning_congr captures scope same
    simpa only [fresh,cellOrigin,closeOrigin,←originEq] using Steps.refl source

inductive PairObject where
  | specification | prototype

def PairObject.term : PairObject → Term → Term → Term
  | .specification, first, second => .specification first second
  | .prototype, first, second => .prototype first second

def PairObject.value : PairObject → Address → Address → RuntimeValue
  | .specification, first, second => .specification first second
  | .prototype, first, second => .prototype first second

/-- Specifications and prototypes allocate two independently suspended
closures. Both names denote their lexical source computations; neither field
is forced by constructing the value. -/
 theorem graph_evaluate_pair {state : State} {source first second : Term} {environment : Environment}
    {kind : PairObject} (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (kind.term first second) environment) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨kind.term first second,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scopes : Scoped environment.length first ∧ Scoped environment.length second := by
    cases kind <;> simpa [PairObject.term] using valid.1
  obtain ⟨one,oneNames,oneHeap,oneSame,oneFresh⟩ :=
    allocateClosure_realizes lexical.1 names heap scopes.1 valid.2
  have oneValid := heapValid_push lexical.1
    (show CellValid (state.heap.size+1) (.suspended ⟨first,environment⟩) from
      ⟨scopes.1,environmentValid_mono valid.2 (Nat.le_succ _)⟩)
  have capturesOne : EnvironmentValid (state.heap.push (.suspended ⟨first,environment⟩)).size environment :=
    environmentValid_mono valid.2 (by simp)
  obtain ⟨two,twoNames,twoHeap,twoSame,twoFresh⟩ :=
    allocateClosure_realizes oneValid oneNames oneHeap scopes.2 capturesOne
  have same : ∀ address, address < state.heap.size → meaning address = two address := by
    intro address allocated
    exact (oneSame address allocated).trans (twoSame address (by simpa using Nat.lt_succ_of_lt allocated))
  have firstEq : two state.heap.size = closeTerm meaning environment first := by
    rw [←twoSame state.heap.size (by simp),oneFresh]
  have secondEq : two (state.heap.size+1) = closeTerm meaning environment second := by
    have closeEq := closeTerm_meaning_congr valid.2 scopes.2 oneSame
    simpa only [Array.size_push,←closeEq] using twoFresh
  have sourceEq : valueMeaning two (kind.value state.heap.size (state.heap.size+1)) =
      closeTerm meaning environment (kind.term first second) := by
    cases kind <;> cases environment <;> simp [PairObject.term,PairObject.value,valueMeaning,firstEq,secondEq,closeTerm,Term.substitute]
  simp [controlMeaning,evaluate] at control
  subst focus
  have consumers := stackRealizes_congr lexical.2.2 same stack
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,two,?_,?_,
    valueMeaning two (kind.value state.heap.size (state.heap.size+1)),?_,?_⟩
  · cases kind <;> simpa [stepRaw,evaluate,PairObject.term] using twoNames
  · cases kind <;> simpa [stepRaw,evaluate,PairObject.term] using twoHeap
  · cases kind <;> simp [stepRaw,evaluate,PairObject.term,PairObject.value,controlMeaning]
  · rw [sourceEq]
    cases kind <;> simpa [stepRaw,evaluate,PairObject.term] using consumers

def allocationLoop (environment : Environment) (fields : List (String × Term))
    (heap : Array Cell) (prior : List (String × Address)) : Array Cell × List (String × Address) :=
  fields.foldl (fun pair field =>
    (pair.1.push (.suspended ⟨field.2,environment⟩),(field.1,pair.1.size)::pair.2)) (heap,prior)

 theorem allocationLoop_accumulator (environment : Environment) (fields : List (String × Term))
    (heap : Array Cell) (prior : List (String × Address)) :
    allocationLoop environment fields heap prior =
      ((allocationLoop environment fields heap []).1,(allocationLoop environment fields heap []).2++prior) := by
  induction fields generalizing heap prior with
  | nil => simp [allocationLoop]
  | cons field fields ih =>
      change allocationLoop environment fields (heap.push (.suspended ⟨field.2,environment⟩)) ((field.1,heap.size)::prior) =
        ((allocationLoop environment fields (heap.push (.suspended ⟨field.2,environment⟩)) [(field.1,heap.size)]).1,
         (allocationLoop environment fields (heap.push (.suspended ⟨field.2,environment⟩)) [(field.1,heap.size)]).2++prior)
      rw [ih _ ((field.1,heap.size)::prior),ih _ [(field.1,heap.size)]]
      simp [List.append_assoc]

 theorem allocateFields_cons (heap : Array Cell) (environment : Environment) (field : String × Term)
    (fields : List (String × Term)) :
    allocateFields heap environment (field::fields) =
      ((allocateFields (heap.push (.suspended ⟨field.2,environment⟩)) environment fields).1,
       (field.1,heap.size)::(allocateFields (heap.push (.suspended ⟨field.2,environment⟩)) environment fields).2) := by
  change ((allocationLoop environment fields (heap.push (.suspended ⟨field.2,environment⟩)) [(field.1,heap.size)]).1,
    (allocationLoop environment fields (heap.push (.suspended ⟨field.2,environment⟩)) [(field.1,heap.size)]).2.reverse) = _
  rw [allocationLoop_accumulator]
  simp [allocateFields,allocationLoop,List.reverse_append]

/-- Arbitrary lazy record allocation: every generated field name denotes the
original captured computation, in field order, while all old graph meanings
and all source origins are retained. Fields may contain general Fix. -/
 theorem allocateFields_realizes {heap : Array Cell} {meaning : AddressMeaning} {environment : Environment}
    {fields : List (String × Term)} (valid : HeapValid heap) (names : MeaningsScoped heap.size meaning)
    (realizes : HeapRealizes meaning heap) (captures : EnvironmentValid heap.size environment)
    (scopes : ∀ field ∈ fields, Scoped environment.length field.2) :
    ∃ extended : AddressMeaning,
      MeaningsScoped (allocateFields heap environment fields).1.size extended ∧
      HeapRealizes extended (allocateFields heap environment fields).1 ∧
      (∀ address, address < heap.size → meaning address = extended address) ∧
      ((allocateFields heap environment fields).2.map fun field => (field.1,extended field.2)) =
        (fields.map fun field => (field.1,closeTerm meaning environment field.2)) := by
  induction fields generalizing heap meaning with
  | nil => exact ⟨meaning,names,realizes,by intros; rfl,rfl⟩
  | cons field fields ih =>
      have headScope := scopes field (List.mem_cons_self ..)
      have tailScopes : ∀ field ∈ fields, Scoped environment.length field.2 :=
        fun field member => scopes field (List.mem_cons_of_mem _ member)
      obtain ⟨one,oneNames,oneHeap,oneSame,oneFresh⟩ := allocateClosure_realizes valid names realizes headScope captures
      have oneValid := heapValid_push valid
        (show CellValid (heap.size+1) (.suspended ⟨field.2,environment⟩) from
          ⟨headScope,environmentValid_mono captures (Nat.le_succ _)⟩)
      have capturesOne : EnvironmentValid (heap.push (.suspended ⟨field.2,environment⟩)).size environment :=
        environmentValid_mono captures (by simp)
      obtain ⟨two,twoNames,twoHeap,twoSame,twoFields⟩ := ih oneValid oneNames oneHeap capturesOne tailScopes
      have same : ∀ address, address < heap.size → meaning address = two address := by
        intro address allocated
        exact (oneSame address allocated).trans (twoSame address (by simpa using Nat.lt_succ_of_lt allocated))
      refine ⟨two,?_,?_,same,?_⟩
      · simpa only [allocateFields_cons] using twoNames
      · simpa only [allocateFields_cons] using twoHeap
      · rw [allocateFields_cons,List.map_cons,twoFields]
        have firstEq : two heap.size = closeTerm meaning environment field.2 := by
          rw [←twoSame heap.size (by simp),oneFresh]
        rw [firstEq,List.map_cons]
        congr 1
        apply List.map_congr_left
        intro f member
        exact Prod.ext rfl (closeTerm_meaning_congr captures (tailScopes f member) oneSame).symm

 theorem closeTerm_record (meaning : AddressMeaning) (environment : Environment) (fields : List (String × Term)) :
    closeTerm meaning environment (.record fields) =
      .record (fields.map fun field => (field.1,closeTerm meaning environment field.2)) := by
  cases environment <;> simp [closeTerm,Term.substitute]

 theorem graph_evaluate_record {state : State} {source : Term} {fields : List (String × Term)} {environment : Environment}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (.record fields) environment) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨.record fields,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scopes : ∀ field ∈ fields, Scoped environment.length field.2 := by simpa using valid.1
  obtain ⟨extended,newNames,newHeap,same,fieldsEq⟩ := allocateFields_realizes lexical.1 names heap valid.2 scopes
  have denotes : valueMeaning extended (.record (allocateFields state.heap environment fields).2) =
      closeTerm meaning environment (.record fields) := by simp only [valueMeaning,fieldsEq,closeTerm_record]
  simp [controlMeaning,evaluate] at control
  subst focus
  have consumers := stackRealizes_congr lexical.2.2 same stack
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,extended,?_,?_,
    valueMeaning extended (.record (allocateFields state.heap environment fields).2),?_,?_⟩
  · simpa [stepRaw,evaluate] using newNames
  · simpa [stepRaw,evaluate] using newHeap
  · simp [stepRaw,evaluate,controlMeaning]
  · rw [denotes]
    simpa [stepRaw,evaluate] using consumers

 theorem graph_field_return {state : State} {source : Term} {fields : List (String × Address)}
    {name key : String} {address : Address} {rest : List Frame}
    (represented : GraphRepresents state source) (returned : state.control = .returned (.record fields))
    (head : state.stack = .field name::rest)
    (found : fields.find? (fun field => field.1 == name) = some (key,address)) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have keyEq : key = name := by simpa using List.find?_some found
  subst key
  have sourceFound : (fields.map fun field => (field.1,meaning field.2)).find? (fun field => field.1 == name) = some (name,meaning address) := by
    simp [List.find?_map,Function.comp_def,found]
  have reduce := Step.field _ name (meaning address) sourceFound
  simp [controlMeaning,returned] at control
  subst focus
  have before : StackRealizes meaning source (.get (valueMeaning meaning (.record fields)) name) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  have advanced := stackRealizes_steps before (Steps.next reduce (Steps.refl _))
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,meaning,?_,?_,meaning address,?_,?_⟩
  · simpa [stepRaw,returned,head,found] using names
  · simpa [stepRaw,returned,head,found] using heap
  · simp [stepRaw,returned,head,found,controlMeaning]
  · simpa [stepRaw,returned,head,found] using advanced

 theorem closeTerm_mixBody {bound : Nat} {meaning : AddressMeaning} {environment : Environment} {lower upper : Term}
    (names : MeaningsScoped bound meaning) (captures : EnvironmentValid bound environment)
    (lowerScope : Scoped environment.length lower) (upperScope : Scoped environment.length upper) :
    closeTerm meaning environment (mixBody lower upper) =
      mixBody (closeTerm meaning environment lower) (closeTerm meaning environment upper) := by
  let sigma := environmentSubstitution meaning environment
  have images : ∀ i, i < environment.length → Scoped 0 (sigma i) := environmentSubstitution_scoped names captures
  have shifted : ∀ term, Scoped environment.length term →
      (term.rename (fun n => n+2)).substitute (liftSubstitution (liftSubstitution sigma)) = term.substitute sigma := by
    intro term scope
    rw [scoped_rename_substitute scope]
    apply scoped_substitution_congr scope
    intro i hi
    simp only [liftSubstitution,
      scoped_rename_identity (images i hi) Nat.succ (by intro j hj; omega)]
  have lowerClosed := closeTerm_scoped names captures lowerScope
  have upperClosed := closeTerm_scoped names captures upperScope
  rw [closeTerm_eq_substitution (scoped_mixBody lowerScope upperScope)]
  simp only [mixBody,Term.substitute]
  have liftedOne : liftSubstitution (liftSubstitution (environmentSubstitution meaning environment)) 1 = .bound 1 := by
    simp [liftSubstitution,Term.rename]
  have liftedZero : liftSubstitution (liftSubstitution (environmentSubstitution meaning environment)) 0 = .bound 0 := rfl
  simp only [liftedOne,liftedZero]
  change Term.lam (.lam (.app (.app ((upper.rename (fun n => n+2)).substitute (liftSubstitution (liftSubstitution sigma))) (.bound 1))
    (.app (.app ((lower.rename (fun n => n+2)).substitute (liftSubstitution (liftSubstitution sigma))) (.bound 1)) (.bound 0)))) = _
  rw [shifted upper upperScope,shifted lower lowerScope]
  rw [scoped_rename_identity lowerClosed (fun n => n+2) (by intro j hj; omega),
    scoped_rename_identity upperClosed (fun n => n+2) (by intro j hj; omega)]
  simp only [closeTerm_eq_substitution lowerScope,closeTerm_eq_substitution upperScope,sigma]

 theorem graph_evaluate_mix {state : State} {source lower upper : Term} {environment : Environment}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (.mix lower upper) environment) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨.mix lower upper,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scopes : Scoped environment.length lower ∧ Scoped environment.length upper := by simpa using valid.1
  have reduce : Step (closeTerm meaning environment (.mix lower upper)) (closeTerm meaning environment (mixBody lower upper)) := by
    rw [closeTerm_mixBody names valid.2 scopes.1 scopes.2]
    have rule := Step.mix (closeTerm meaning environment lower) (closeTerm meaning environment upper)
    cases environment <;> simpa [closeTerm,Term.substitute] using rule
  simp [controlMeaning,evaluate] at control
  subst focus
  have advanced := stackRealizes_steps stack (Steps.next reduce (Steps.refl _))
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,meaning,?_,?_,closeTerm meaning environment (mixBody lower upper),?_,?_⟩
  · simpa [stepRaw,evaluate] using names
  · simpa [stepRaw,evaluate] using heap
  · simp [stepRaw,evaluate,controlMeaning]
  · simpa [stepRaw,evaluate] using advanced

 theorem graph_condition_zero {state : State} {source zero body : Term} {environment : Environment} {rest : List Frame}
    (represented : GraphRepresents state source) (returned : state.control = .returned (.natural 0))
    (head : state.stack = .condition zero body environment::rest) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned,valueMeaning] at control
  subst focus
  have before : StackRealizes meaning source
      (.ifZero (.nat 0) (closeTerm meaning environment zero)
        (body.substitute (liftSubstitution (environmentSubstitution meaning environment)))) rest := by
    simpa only [head,StackRealizes,frameMeaning] using stack
  have advanced := stackRealizes_steps before (Steps.next (Step.zero _ _) (Steps.refl _))
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,meaning,?_,?_,closeTerm meaning environment zero,?_,?_⟩
  · simpa [stepRaw,returned,head] using names
  · simpa [stepRaw,returned,head] using heap
  · simp [stepRaw,returned,head,controlMeaning]
  · simpa [stepRaw,returned,head] using advanced

 theorem closeTerm_weaken {bound : Nat} {meaning extended : AddressMeaning}
    {environment : Environment} {term : Term}
    (captures : EnvironmentValid bound environment) (scope : Scoped environment.length term)
    (same : ∀ address, address < bound → meaning address = extended address) :
    closeTerm extended (bound::environment) (term.rename Nat.succ) = closeTerm meaning environment term := by
  have shifted := scoped_rename scope Nat.succ (environment.length+1) (by intro i hi; omega)
  rw [closeTerm_eq_substitution (by simpa using shifted),closeTerm_eq_substitution scope,
    scoped_rename_substitute scope]
  apply scoped_substitution_congr scope
  intro i hi
  have found : environment[i]? = some environment[i] := getElem?_pos environment i hi
  simp only [environmentSubstitution,List.getElem?_cons_succ,found]
  exact (same _ (captures _ (List.mem_of_getElem? found))).symm

 theorem closeTerm_fix (meaning : AddressMeaning) (environment : Environment) (spec inherited : Term) :
    closeTerm meaning environment (.fix spec inherited) =
      .fix (closeTerm meaning environment spec) (closeTerm meaning environment inherited) := by
  cases environment <;> simp only [closeTerm,Term.substitute]

/-- Allocating any lexical Fix ties one stable address to the closed source
Fix and retains its one-step unfolding as the cell origin. This is a general
graph preservation theorem, including nonempty captured environments and
active surrounding update segments. -/
 theorem graph_evaluate_fix {state : State} {source spec inherited : Term} {environment : Environment}
    (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (.fix spec inherited) environment) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have valid : ClosureValid state.heap.size ⟨.fix spec inherited,environment⟩ := by
    simpa only [evaluate,ControlValid] using lexical.2.1
  have scopes : Scoped environment.length spec ∧ Scoped environment.length inherited := by
    simpa using valid.1
  let fixSource := closeTerm meaning environment (.fix spec inherited)
  let extended := extendMeaning meaning state.heap.size fixSource
  have same : ∀ address, address < state.heap.size → meaning address = extended address :=
    extendMeaning_prefix _ _ _
  have fresh : extended state.heap.size = fixSource := by simp [extended,extendMeaning]
  have closed : Scoped 0 fixSource := closeTerm_scoped names valid.2 valid.1
  have newNames : MeaningsScoped (state.heap.size+1) extended := by
    intro address allocated
    by_cases eq : address = state.heap.size
    · subst address; simpa only [fresh] using closed
    · have old : address < state.heap.size := by omega
      simpa only [←same address old] using names address old
  have newHeap := heapRealizes_congr lexical.1 same heap
  let body := Term.app (Term.app (spec.rename Nat.succ) (.bound 0)) (inherited.rename Nat.succ)
  have originEq : closeTerm extended (state.heap.size::environment) body =
      .app (.app (closeTerm meaning environment spec) fixSource) (closeTerm meaning environment inherited) := by
    simp only [body,closeTerm_app,closeTerm_weaken valid.2 scopes.1 same,
      closeTerm_weaken valid.2 scopes.2 same]
    simp [closeTerm,Term.substitute,environmentSubstitution,fresh]
  have newCell : CellRealizes extended state.heap.size (.suspended ⟨body,state.heap.size::environment⟩) := by
    refine ⟨?_,True.intro⟩
    simp only [cellOrigin,closeOrigin,fresh,originEq]
    simpa only [fixSource,closeTerm_fix] using
      Steps.next (Step.fix (closeTerm meaning environment spec) (closeTerm meaning environment inherited)) (Steps.refl _)
  simp [controlMeaning,evaluate] at control
  subst focus
  have consumers := stackRealizes_congr lexical.2.2 same stack
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,extended,?_,?_,fixSource,?_,?_⟩
  · simpa [stepRaw,evaluate] using newNames
  · simpa [stepRaw,evaluate,body] using heapRealizes_push newHeap newCell
  · simp [stepRaw,evaluate,controlMeaning,fresh]
  · simpa [stepRaw,evaluate,fixSource] using consumers

/-- General lazy closure beta through the actual allocator. The newly suspended
argument has a closed source name, existing heap names retain their meanings,
and each local update segment advances by the independent source beta rule. -/
 theorem graph_closure_call {state : State} {source body argument : Term}
    {captured environment : Environment} {rest : List Frame}
    (represented : GraphRepresents state source)
    (returned : state.control = .returned (.closure body captured))
    (head : state.stack = .argument argument environment::rest) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  have closureValid : RuntimeValueValid state.heap.size (.closure body captured) := by
    simpa only [returned,ControlValid] using lexical.2.1
  have argumentValid : ClosureValid state.heap.size ⟨argument,environment⟩ := by
    have hv := lexical.2.2 (.argument argument environment) (head ▸ List.mem_cons_self ..)
    exact hv
  have restValid : ∀ frame ∈ rest, FrameValid state.heap.size frame := by
    intro frame member
    apply lexical.2.2 frame
    rw [head]
    exact List.mem_cons_of_mem _ member
  let argumentSource := closeTerm meaning environment argument
  let extended := extendMeaning meaning state.heap.size argumentSource
  have same : ∀ address, address < state.heap.size → meaning address = extended address :=
    extendMeaning_prefix _ _ _
  have fresh : extended state.heap.size = argumentSource := by simp [extended,extendMeaning]
  have argClosed : Scoped 0 argumentSource := closeTerm_scoped names argumentValid.2 argumentValid.1
  have newNames : MeaningsScoped (state.heap.size+1) extended := by
    intro address allocated
    by_cases eq : address = state.heap.size
    · subst address; simpa only [fresh] using argClosed
    · have old : address < state.heap.size := by omega
      simpa only [←same address old] using names address old
  have newHeap := heapRealizes_congr lexical.1 same heap
  have newCell : CellRealizes extended state.heap.size (.suspended ⟨argument,environment⟩) := by
    refine ⟨?_,True.intro⟩
    have argSame := closeTerm_meaning_congr argumentValid.2 argumentValid.1 same
    simpa only [fresh,cellOrigin,closeOrigin,←argSame] using Steps.refl argumentSource
  have beta : Step (.app (valueMeaning meaning (.closure body captured)) argumentSource)
      (closeTerm extended (state.heap.size::captured) body) := by
    simp only [valueMeaning,closeTerm_lambda closureValid.1]
    rw [←closeTerm_beta names closureValid.2 closureValid.1 argClosed same fresh]
    exact Step.beta _ _
  simp [returned,controlMeaning] at control
  subst focus
  have consumers : StackRealizes meaning source
      (.app (valueMeaning meaning (.closure body captured)) argumentSource) rest := by
    simpa only [head,StackRealizes,frameMeaning,argumentSource] using stack
  have newConsumers := stackRealizes_congr restValid same consumers
  have advanced := stackRealizes_steps newConsumers (Steps.next beta (Steps.refl _))
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,extended,?_,?_,
    closeTerm extended (state.heap.size::captured) body,?_,?_⟩
  · simpa [stepRaw,returned,head] using newNames
  · simpa [stepRaw,returned,head] using heapRealizes_push newHeap newCell
  · simp [stepRaw,returned,head,controlMeaning]
  · simpa [stepRaw,returned,head] using advanced

/-- Entering a source application installs the lexical argument continuation;
its semantic demand segment is the independently defined source application. -/
 theorem graph_evaluate_application {state : State} {source function argument : Term}
    {environment : Environment} (represented : GraphRepresents state source)
    (evaluate : state.control = .evaluate (.app function argument) environment) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,evaluate] at control
  subst focus
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,meaning,?_,?_,closeTerm meaning environment function,?_,?_⟩
  · simpa [stepRaw,evaluate] using names
  · simpa [stepRaw,evaluate] using heap
  · simp [stepRaw,evaluate,controlMeaning]
  · simpa [stepRaw,evaluate,StackRealizes,frameMeaning,closeTerm_app] using stack

/-- Binary evaluation switches from the left demand to the right one without
forcing any captured arguments of the returned left value. -/
 theorem graph_binary_left_return {state : State} {source right : Term} {primitive : Primitive}
    {environment : Environment} {rest : List Frame} {value : RuntimeValue}
    (represented : GraphRepresents state source) (returned : state.control = .returned value)
    (head : state.stack = .binaryLeft primitive right environment::rest) :
    GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned] at control
  subst focus
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,meaning,?_,?_,closeTerm meaning environment right,?_,?_⟩
  · simpa [stepRaw,returned,head] using names
  · simpa [stepRaw,returned,head] using heap
  · simp [stepRaw,returned,head,controlMeaning]
  · simpa [stepRaw,returned,head,StackRealizes,frameMeaning] using stack

 theorem graph_complete_return {state : State} {source : Term} {value : RuntimeValue}
    (represented : GraphRepresents state source) (returned : state.control = .returned value)
    (empty : state.stack = []) : GraphRepresents (stepRaw state) source := by
  obtain ⟨lexical,busy,final,meaning,names,heap,focus,control,stack⟩ := represented
  simp [controlMeaning,returned] at control
  subst focus
  refine ⟨stepRaw_lexicalInvariant lexical,stepRaw_busyInvariant busy,
    stepRaw_finalStackInvariant final,meaning,?_,?_,valueMeaning meaning value,?_,?_⟩
  · simpa [stepRaw,returned,empty] using names
  · simpa [stepRaw,returned,empty] using heap
  · simp [stepRaw,returned,empty,controlMeaning]
  · simpa [stepRaw,returned,empty] using stack

/-- A concrete cyclic heap instance: its one address denotes the source Fix;
the saved origin captures that same address and denotes its independent source
unfolding. Neither this witness nor the lexical invariant forbids the cycle. -/
 theorem initial_fix_graph {spec inherited : Term}
    (hs : Scoped 0 spec) (hi : Scoped 0 inherited) :
    GraphRepresents (stepRaw (initial (.fix spec inherited))) (.fix spec inherited) := by
  have lexical := stepRaw_lexicalInvariant (initial_lexicalInvariant (Scoped.fix hs hi))
  let meaning : AddressMeaning := fun _ => .fix spec inherited
  have rs : spec.rename Nat.succ = spec := scoped_rename_identity hs _ (by intros; omega)
  have ri : inherited.rename Nat.succ = inherited := scoped_rename_identity hi _ (by intros; omega)
  have ss : spec.substitute (environmentSubstitution meaning [0]) = spec :=
    scoped_substitute_identity hs _ (by intros; omega)
  have si : inherited.substitute (environmentSubstitution meaning [0]) = inherited :=
    scoped_substitute_identity hi _ (by intros; omega)
  refine ⟨lexical,stepRaw_busyInvariant (initial_busyInvariant _),stepRaw_finalStackInvariant (initial_finalStackInvariant _),meaning,?_,?_,.fix spec inherited,?_,?_⟩
  · intro address allocated
    exact Scoped.fix hs hi
  · intro address cell found
    simp [initial,stepRaw] at found
    have bound := (List.getElem?_eq_some_iff.mp found).1
    have zero : address = 0 := by simpa using bound
    subst address
    simp at found
    subst cell
    constructor
    · simpa [closeOrigin,closeTerm,cellOrigin,Term.substitute,rs,ri,ss,si,
        environmentSubstitution,meaning] using Steps.next (Step.fix spec inherited) (Steps.refl _)
    · trivial
  · simp [initial,stepRaw,controlMeaning,meaning]
  · simp only [initial,stepRaw,StackRealizes]
    exact .refl _

/-- Finite raw execution is independent of capacity. Resource completeness
below computes a sufficient bound from this real transition trace; it does not
assert that a source computation terminates. -/
def rawRun : Nat → State → State
  | 0,state => state
  | ticks+1,state => rawRun ticks (stepRaw state)

def retainedState : Outcome → State
  | .finished _ state | .suspended _ state | .divergent _ state | .refused _ state => state

def TraceFits (limits : Limits) : Nat → State → Prop
  | 0,_ => True
  | ticks+1,state =>
      (stepRaw state).heap.size ≤ limits.heap ∧
      (stepRaw state).stack.length ≤ limits.stack ∧ TraceFits limits ticks (stepRaw state)

/-- Explicit maximum heap/stack bounds along the requested finite trace. Tick
bound is its length. A resource suspension requires larger bounds and keeps the
exact resumable state; this maximum is a semantic bound, not a native allocator. -/
def traceLimits : Nat → State → Limits
  | 0,_ => ⟨0,0⟩
  | ticks+1,state =>
      let next := stepRaw state
      let later := traceLimits ticks next
      ⟨max next.heap.size later.heap,max next.stack.length later.stack⟩

 theorem traceFits_mono {ticks : Nat} {state : State} {small large : Limits}
    (fits : TraceFits small ticks state) (heap : small.heap ≤ large.heap)
    (stack : small.stack ≤ large.stack) : TraceFits large ticks state := by
  induction ticks generalizing state with
  | zero => trivial
  | succ ticks ih =>
      exact ⟨Nat.le_trans fits.1 heap,Nat.le_trans fits.2.1 stack,ih fits.2.2⟩

 theorem traceFits_traceLimits (ticks : Nat) (state : State) :
    TraceFits (traceLimits ticks state) ticks state := by
  induction ticks generalizing state with
  | zero => trivial
  | succ ticks ih =>
      refine ⟨Nat.le_max_left _ _,Nat.le_max_left _ _,?_⟩
      exact traceFits_mono (ih (stepRaw state)) (Nat.le_max_right _ _) (Nat.le_max_right _ _)

 theorem rawRun_absorbs {state : State} (ticks : Nat) (absorbs : stepRaw state = state) :
    rawRun ticks state = state := by
  induction ticks with
  | zero => rfl
  | succ ticks ih => simpa only [rawRun,absorbs] using ih

 theorem runBounded_retains_rawRun {limits : Limits} {ticks : Nat} {state : State}
    (fits : TraceFits limits ticks state) :
    retainedState (runBounded limits ticks state) = rawRun ticks state := by
  induction ticks generalizing state with
  | zero => cases control : state.control <;> simp [runBounded,rawRun,retainedState,control]
  | succ ticks ih =>
      have next := ih fits.2.2
      cases control : state.control
      all_goals first
        | have admitted : step limits state = .suspended .ticks (stepRaw state) := by
            simp [step,control,fits.1,fits.2.1]
          simpa only [runBounded,admitted,rawRun] using next
        | have absorbing : stepRaw state = state := by simp [stepRaw,control]
          simpa only [runBounded,step,control,retainedState] using
            (rawRun_absorbs (ticks+1) absorbing).symm

set_option linter.unnecessarySimpa false in
 theorem runBounded_complete_classifies {limits : Limits} {ticks : Nat} {state : State}
    {value : RuntimeValue}
    (complete : (retainedState (runBounded limits ticks state)).control = .complete value) :
    runBounded limits ticks state =
      .finished value (retainedState (runBounded limits ticks state)) := by
  induction ticks generalizing state with
  | zero => cases control : state.control <;> simp_all [runBounded,retainedState]
  | succ ticks ih =>
      cases control : state.control
      all_goals first
        | simpa [runBounded,step,control,retainedState] using complete
        | by_cases within : (stepRaw state).heap.size ≤ limits.heap ∧
              (stepRaw state).stack.length ≤ limits.stack
          · have admitted : step limits state = .suspended .ticks (stepRaw state) := by
              simp [step,control,within.1,within.2]
            simp only [runBounded,admitted] at complete ⊢
            exact ih complete
          · have capacity : step limits state = .suspended .capacity state := by
              simp [step,control,Bool.and_eq_true,within]
            simp only [runBounded,capacity,retainedState] at complete
            rw [control] at complete
            contradiction

 theorem adequate_trace_execution (ticks : Nat) (state : State) :
    retainedState (runBounded (traceLimits ticks state) ticks state) = rawRun ticks state :=
  runBounded_retains_rawRun (traceFits_traceLimits ticks state)

 theorem adequate_trace_completion {ticks : Nat} {state : State} {value : RuntimeValue}
    (complete : (rawRun ticks state).control = .complete value) :
    runBounded (traceLimits ticks state) ticks state = .finished value (rawRun ticks state) := by
  have retained := adequate_trace_execution ticks state
  have classified := runBounded_complete_classifies (retained ▸ complete)
  simpa only [retained] using classified

 theorem rawRun_lexicalInvariant {source : Term} (closed : Scoped 0 source) (ticks : Nat) :
    LexicalInvariant (rawRun ticks (initial source)) := by
  have general : ∀ ticks state, LexicalInvariant state → LexicalInvariant (rawRun ticks state) := by
    intro ticks
    induction ticks with
    | zero => intro state invariant; exact invariant
    | succ ticks ih => intro state invariant; exact ih _ (stepRaw_lexicalInvariant invariant)
  exact general ticks _ (initial_lexicalInvariant closed)

 theorem rawRun_preservesOrigins (ticks : Nat) (state : State) :
    PreservesOrigins state.heap (rawRun ticks state).heap := by
  induction ticks generalizing state with
  | zero => exact preservesOrigins_refl _
  | succ ticks ih => exact preservesOrigins_trans (stepRaw_preservesOrigins _) (ih _)

 theorem rawRun_preservesCached (ticks : Nat) (state : State) :
    PreservesCached state.heap (rawRun ticks state).heap := by
  induction ticks generalizing state with
  | zero => exact preservesCached_refl _
  | succ ticks ih => exact preservesCached_trans (stepRaw_preservesCached _) (ih _)

/-- All unused arguments, including arbitrary diverging Fix computations,
remain suspended at their original lexical address. This is a general theorem
about the actual bounded executor, not a single closed native test. -/
 theorem unused_argument_executor (argument : Term) (number : Nat) :
    runBounded ⟨1,1⟩ 5 (initial (.app (.lam (.nat number)) argument)) =
      .finished (.natural number)
        ⟨#[.suspended ⟨argument,[]⟩],.complete (.natural number),[]⟩ := by
  simp [runBounded,step,stepRaw,initial]

 theorem unused_argument_source (argument : Term) (number : Nat) :
    Evaluates (.app (.lam (.nat number)) argument) (.nat number) := by
  constructor
  · have beta := Step.beta (.nat number) argument
    simpa [instantiate,Term.substitute] using Steps.next beta (Steps.refl _)
  · exact .natural _

/-- The second demand sees the first demand's cache at the identical address.
This exercises real memoization for every natural argument. -/
 theorem shared_argument_executor (number : Nat) :
    runBounded ⟨1,2⟩ 13
      (initial (.app (.lam (.binary .add (.bound 0) (.bound 0))) (.nat number))) =
    .finished (.natural (number+number))
      ⟨#[.cached ⟨.nat number,[]⟩ (.natural number)],.complete (.natural (number+number)),[]⟩ := by
  simp [runBounded,step,stepRaw,initial,primitiveResult,valueTerm,scalarValue,
    Array.set!,Array.setIfInBounds]

 theorem shared_argument_source (number : Nat) :
    Evaluates (.app (.lam (.binary .add (.bound 0) (.bound 0))) (.nat number)) (.nat (number+number)) := by
  constructor
  · have beta := Step.beta (.binary .add (.bound 0) (.bound 0)) (.nat number)
    have primitive := Step.primitive .add (.nat number) (.nat number) (.nat (number+number))
      (.natural _) (.natural _) rfl
    exact .next (by simpa [instantiate,Term.substitute] using beta) (.next primitive (.refl _))
  · exact .natural _

/-- Two demands of the same record field cache exactly its one address. The
other field retains arbitrary source, including a divergent knot, suspended.
The record target itself also retains its original source and cached pointer map. -/
 theorem shared_field_executor (unused : Term) (number : Nat) :
    runBounded ⟨3,3⟩ 21
      (initial (.app
        (.lam (.binary .add (.get (.bound 0) "x") (.get (.bound 0) "x")))
        (.record [("x",.nat number),("unused",unused)]))) =
    .finished (.natural (number+number))
      ⟨#[.cached ⟨.record [("x",.nat number),("unused",unused)],[]⟩
          (.record [("x",1),("unused",2)]),
        .cached ⟨.nat number,[]⟩ (.natural number),
        .suspended ⟨unused,[]⟩],.complete (.natural (number+number)),[]⟩ := by
  simp [runBounded,step,stepRaw,initial,primitiveResult,valueTerm,scalarValue,
    allocateFields,Array.set!,Array.setIfInBounds]

 theorem shared_field_source (unused : Term) (number : Nat) :
    Evaluates (.app
      (.lam (.binary .add (.get (.bound 0) "x") (.get (.bound 0) "x")))
      (.record [("x",.nat number),("unused",unused)])) (.nat (number+number)) := by
  let fields : List (String × Term) := [("x",.nat number),("unused",unused)]
  have field := Step.field fields "x" (.nat number) rfl
  have beta := Step.beta (.binary .add (.get (.bound 0) "x") (.get (.bound 0) "x")) (.record fields)
  have primitive := Step.primitive .add (.nat number) (.nat number) (.nat (number+number))
    (.natural _) (.natural _) rfl
  constructor
  · exact .next (by simpa [instantiate,Term.substitute,fields] using beta)
      (.next (.binaryLeft .add _ field)
        (.next (.binaryRight .add _ (.natural _) field) (.next primitive (.refl _))))
  · exact .natural _

/-- General tied Fix can return a ground target without demanding either
recursive self or inherited target. Both argument thunks stay suspended, while
the tied address is memoized in place with its retained unfolding origin. -/
 theorem fixed_constant_executor (inherited : Term) (number : Nat) :
    runBounded ⟨3,3⟩ 11 (initial (.fix (.lam (.lam (.nat number))) inherited)) =
    .finished (.natural number)
      ⟨#[.cached
          ⟨.app (.app (.lam (.lam (.nat number))) (.bound 0)) (inherited.rename Nat.succ),[0]⟩
          (.natural number),
        .suspended ⟨.bound 0,[0]⟩,
        .suspended ⟨inherited.rename Nat.succ,[0]⟩],.complete (.natural number),[]⟩ := by
  simp [runBounded,step,stepRaw,initial,Term.rename,
    Array.set!,Array.setIfInBounds]

 theorem fixed_constant_source (inherited : Term) (number : Nat) :
    Evaluates (.fix (.lam (.lam (.nat number))) inherited) (.nat number) := by
  constructor
  · have selfBeta := Step.beta (.lam (.nat number)) (.fix (.lam (.lam (.nat number))) inherited)
    have inheritedBeta := Step.beta (.nat number) inherited
    exact .next (.fix _ _) (.next (.application inherited (by
      simpa [instantiate,Term.substitute] using selfBeta)) (.next (by
        simpa [instantiate,Term.substitute] using inheritedBeta) (.refl _)))
  · exact .natural _

/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_enter_suspended' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_enter_suspended
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_cache_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_cache_update
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_enter_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_enter_cached
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_evaluate_application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_evaluate_application
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_closure_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_closure_call
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_evaluate_fix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_evaluate_fix
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_evaluate_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_evaluate_context
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_evaluate_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_evaluate_pair
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_evaluate_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_evaluate_bound
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_evaluate_immediate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_evaluate_immediate
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_object_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_object_access
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_specification_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_specification_call
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_primitive_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_primitive_return
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.allocateFields_realizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms allocateFields_realizes
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_evaluate_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_evaluate_record
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_field_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_field_return
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_evaluate_mix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_evaluate_mix
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_condition_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_condition_zero
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_complete_boolean_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms graph_complete_boolean_sound
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.closeTerm_beta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms closeTerm_beta
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_binary_left_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_binary_left_return
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_complete_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_complete_return
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.initial_fix_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initial_fix_graph
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.adequate_trace_execution' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms adequate_trace_execution
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.adequate_trace_completion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms adequate_trace_completion
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.shared_field_executor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shared_field_executor
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.shared_field_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms shared_field_source
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.fixed_constant_executor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fixed_constant_executor
/-- info: 'Minidregg.Theory.ObjectiveBendDemandAdequacy.fixed_constant_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fixed_constant_source

end Minidregg.Theory.ObjectiveBendDemandAdequacy
