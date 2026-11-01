/-
A signing plan modulo the image it was read at. A plan is read at one verified image (its world
root and height); an append (a certify, another member's write) moves the image without changing
anything a signer approves. A re-check before key use or assembly compares plans through `imageFree`,
so an approval stays valid across a moved image while every signed byte must be unchanged.
-/
module

public import Compiler.NativeHostCodec

@[expose] public section

namespace Minidregg.Kernel.SigningPlanImage

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.NativeHostCodec

set_option autoImplicit false

/-- The plan with its image coordinates cleared. Nothing a signature covers is among them: a slot's
signed bytes are its header, and a header names the footprint and validUntil, never a root or a
height (`CredentialSignatureAdmission.header`). -/
def imageFree (plan : SigningPlan) : SigningPlan :=
  { plan with worldRoot := ⟨0⟩, height := 0 }

/-- Equal projections fix everything but the image: domain, semantics, the finalized draft and
every slot (role, index and signed header). -/
theorem imageFree_eq_fixes {p q : SigningPlan} (h : imageFree p = imageFree q) :
    p.domain = q.domain ∧ p.semantics = q.semantics ∧
    p.finalizedDraft = q.finalizedDraft ∧ p.slots = q.slots :=
  ⟨congrArg (fun x => x.domain) h, congrArg (fun x => x.semantics) h,
   congrArg (fun x => x.finalizedDraft) h, congrArg (fun x => x.slots) h⟩

/-- Satisfiable: the same plan read at any other image has the same projection. -/
theorem imageFree_moved (p : SigningPlan) (root : Digest) (height : Nat) :
    imageFree { p with worldRoot := root, height := height } = imageFree p := rfl

/-- Teeth: a changed slot list is a changed projection, whatever the images. -/
theorem imageFree_slot_change {p q : SigningPlan} (h : p.slots ≠ q.slots) :
    imageFree p ≠ imageFree q := fun e => h (imageFree_eq_fixes e).2.2.2

end Minidregg.Kernel.SigningPlanImage
