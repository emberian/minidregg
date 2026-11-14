/-
# `Assurance/MemberPatchPoles.lean` — the member patch rule, executed

`Effect.memberPatch` (`Kernel/ResourceEffect.lean`) is the one rule of what thin consent shows
for a registered operation: its declaration states a member patch and the operation pins its
root. The poles, on the deployed declarations:

* *shown*: the two root-pinning reads (codes 3 and 7) state the empty patch and are shown it;
* *by name*: the content write (code 1) and the cited read (code 9) state none and are refused
  `unstated` (the cited read commutes and is displayed without a view; it never asks);
* *the root*: a ghost of the content read that commutes, stating the same member patch, is
  refused `commutes`: a member patch alone does not make an operation displayable;
* *premise*: the context a member patch reads is the signed part of the receiver's context.
-/
import Kernel.ResourceEffectRegistry

namespace Minidregg.Assurance.MemberPatchPoles
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Effects
open Minidregg.Theory.TypedAuthorization

def signer : MemberCtx := ⟨⟨7⟩, 3, .object, 41, ⟨5⟩⟩

/-- How a member patch answered: the length of the shown patch, or the refusal. -/
def answer {e : Effect} (shown : Except Effect.MemberRefusal (Minidregg.Theory.Store.Patch e.L)) :
    Except Effect.MemberRefusal Nat := shown.map List.length

instance : BEq (Except Effect.MemberRefusal Nat) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => decide (a = b)
    | _, _ => false

#guard answer ((effectAt 3).memberPatch signer () 0) == .ok 0
#guard answer ((effectAt 7).memberPatch signer () 0) == .ok 0
#guard answer ((effectAt 9).memberPatch signer [] 0) == .error .unstated
#guard answer ((effectAt 1).memberPatch signer ⟨[]⟩ 0) == .error .unstated
#guard (effectAt 9).spec.commutes [] == true

/-- The content read, declared commuting, with the member patch it states today. -/
def commutingReadGhost : Effect :=
  { readEffect with spec := { readSpec with commutes := fun _ => true } }

#guard commutingReadGhost.member.isSome
#guard answer (commutingReadGhost.memberPatch signer () 0) == .error .commutes
#guard answer (readEffect.memberPatch signer () 0) == .ok 0

end Minidregg.Assurance.MemberPatchPoles
