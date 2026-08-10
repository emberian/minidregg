/-
# Theory.AcceptedCellEffectWitness -- the common effect authority has subjects

`Theory/AcceptedCellEffect.lean` is 792 lines and every theorem in it is
quantified over an `AcceptedCellEffect` the file never exhibits.  It is
constructed downstream -- `ComputationCellEffect.accept` in the BFV and
note-spend lanes -- but always from parameters that are themselves quantified,
so the recursion never bottoms out in built data.  Nothing in the tree closed
it.

That is the load-bearing carrier of the whole architecture: "one canonical
typed state transition, under one complete request-indexed authority" is a
sentence about this type.  A sentence about an empty type is not false, it is
worthless, and until this module nothing distinguished the two cases.

This closes it, standing on the two witnesses built alongside:
`CellStateWitness.honestPatch_accepted` supplies the `ValidatedPatch`, and
`TypedAuthorizationWitness.authorized` supplies the `Authorized`.  The
remaining fields -- the effect-digest and pre-root equations, mode evidence,
and the disclosure decision -- are discharged by construction and computation.

The effect is SEALED, which is not a convenience: `Release` is `PEmpty` here,
so `reveal` and `declassify` are unrepresentable and the accepted effect
carries no disclosure at all.  That is the shape the design intends, and the
teeth below check the two binding equations are real by exhibiting requests
that fail them.

Scope, exactly: this shows the common effect authority is satisfiable at built
parameters, with a permissive portal and a minimal schema.  It is not a claim
about any deployed portal, schema, or effect family, and it proves nothing
about privacy, cost, or physical settlement.
-/
import Theory.AcceptedCellEffect
import Theory.CellStateWitness
import Theory.TypedAuthorizationWitness

namespace Minidregg.Theory.AcceptedCellEffectWitness

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellStateWitness
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.TypedAuthorizationWitness

set_option autoImplicit false

/-! ## One built effect family -/

/-- The trivial lawful codec on a subsingleton. -/
def unitCodec : LawfulCodec Unit where
  encode := fun _ => []
  decode := fun _ => some ()
  decode_encode := fun _ => rfl

/-- One declaration, one outcome, one patch -- the patch being exactly the one
`CellStateWitness` proved validates.  The family is forced sealed: `Release`
and both authority carriers are empty, so no disclosure decision other than
`sealed` can be written. -/
def family : SemanticEffectFamily.{0, 0, 0, 0, 0, 0} schema materializer Unit where
  Declaration := Unit
  declarationCodec := unitCodec
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun _ _ => Unit
  effectDigest := fun _ => ⟨7⟩
  patch := fun _ _ => honestPatch
  nullifier := fun _ _ => none
  Release := fun _ _ => PEmpty
  DeclassificationAuthority := fun _ _ => PEmpty
  ReleaseAuthorization := fun _ _ release => release.elim
  DisclosureAllowed := fun _ _ decision => decision = .sealed

/-- Only `sealed` inhabits the decision type of this family, because `Release`
is empty.  Stated as a theorem so the "forced sealed" claim is checked rather
than asserted. -/
theorem disclosure_forced_sealed
    (decision : DisclosureDecision (family.Release () ())
      (family.DeclassificationAuthority () ())
      (family.ReleaseAuthorization () ())) :
    decision = .sealed := by
  cases decision with
  | sealed => rfl
  | reveal release _ => exact release.elim
  | declassify authority _ _ => exact authority.elim

/-! ## The accepted effect -/

/-- The `ValidatedPatch` obtained by running the validator in
`CellStateWitness`. -/
noncomputable def validatedPatch :
    ValidatedPatch materializer cell (family.patch () ()) :=
  honestPatch_accepted.choose

/-- **`AcceptedCellEffect` is inhabited.**  Every field is built: the
authority token comes from `TypedAuthorizationWitness`, the validated patch
from `CellStateWitness`, and the two binding equations hold by computation. -/
noncomputable def accepted :
    AcceptedCellEffect (portal := permissivePortal) (authState := authState)
      family request cell () () where
  authorization := authorized
  effectsDigestBound := rfl
  preRootBound := rfl
  modeEvidence := ()
  validated := validatedPatch
  disclosure := .sealed
  disclosureAllowed := rfl

theorem acceptedCellEffect_nonempty :
    Nonempty (AcceptedCellEffect (portal := permissivePortal)
      (authState := authState) family request cell () ()) :=
  ⟨accepted⟩

/-! ## Teeth: the two binding equations are real

The accepted effect binds the request to the family by two equations. If
either could be dropped, a caller could authorize one action and install
another. These exhibit requests that fail each one, so the equations are
refutations rather than field declarations. -/

/-- A request identical to the authorized one except that it quotes a
different effects digest. -/
def wrongEffectsRequest : Request .object :=
  { request with effectsDigest := ⟨99⟩ }

theorem wrongEffects_not_bound :
    wrongEffectsRequest.effectsDigest ≠ family.effectDigest () := by decide

/-- A request identical to the authorized one except that it quotes a stale
pre-state root. -/
def stalePreRootRequest : Request .object :=
  { request with preStateRoot := ⟨42⟩ }

theorem stalePreRoot_not_bound :
    stalePreRootRequest.preStateRoot ≠ cell.root := by decide

/-- And neither request can inhabit an accepted effect at this family and
cell: the equations are fields of the structure, so failing one makes the
whole token unrepresentable. -/
theorem no_accepted_of_wrongEffects :
    IsEmpty (AcceptedCellEffect (portal := permissivePortal)
      (authState := authState) family wrongEffectsRequest cell () ()) :=
  ⟨fun token => wrongEffects_not_bound token.effectsDigestBound⟩

theorem no_accepted_of_stalePreRoot :
    IsEmpty (AcceptedCellEffect (portal := permissivePortal)
      (authState := authState) family stalePreRootRequest cell () ()) :=
  ⟨fun token => stalePreRoot_not_bound token.preRootBound⟩

/-- The sealed effect carries no release, and that is a refutation too: the
accepted effect's disclosure decision cannot be anything else. -/
theorem accepted_is_sealed : accepted.disclosure = .sealed := rfl

#print axioms disclosure_forced_sealed
#print axioms acceptedCellEffect_nonempty
#print axioms wrongEffects_not_bound
#print axioms stalePreRoot_not_bound
#print axioms no_accepted_of_wrongEffects
#print axioms no_accepted_of_stalePreRoot
#print axioms accepted_is_sealed

end Minidregg.Theory.AcceptedCellEffectWitness
