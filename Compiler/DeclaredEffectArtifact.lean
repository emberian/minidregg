/-
# Compiler.DeclaredEffectArtifact -- first-order typed effect projection

The semantic effect artifact is derived from the one typed declaration in
`Theory.EffectDeclaration`.  The declaration's `toWire` projection owns the
schema, resource kind, target, and constructor payload; `WireDeclaration.words`
owns their canonical first-order word.  No `Effects.EffectSpec` program or
handwritten operation encoder participates in this path.
-/
import Theory.EffectDeclaration

namespace Minidregg.Compiler.DeclaredEffectArtifact

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.EffectDeclaration

set_option autoImplicit false

/-- First-order data projected from one intrinsically typed effect declaration. -/
structure Artifact where
  schemaVersion : Nat
  resourceKind : Nat
  target : Nat
  words : List Nat
deriving DecidableEq, Repr

/-- Project the authoritative typed declaration through its existing wire form
and canonical word encoding. -/
def Artifact.ofDeclaration {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) : Artifact :=
  let wire := declaration.toWire
  { schemaVersion := wire.schemaVersion
    resourceKind := wire.resourceKind
    target := wire.target
    words := wire.words }

@[simp] theorem Artifact.ofDeclaration_words
    {kind : ResourceKind} {target : ResourceId kind}
    (declaration : Declaration target) :
    (Artifact.ofDeclaration declaration).words = declaration.toWire.words := by
  rfl

/-! ## Concrete v1 account move -/

def accountMoveSource : ResourceId .account := ⟨0⟩
def accountMoveDestination : ResourceId .account := ⟨1⟩
def accountMoveResource : Digest := ⟨0⟩
def accountMoveAmount : Int := 2

/-- Move two units of resource zero from account zero to account one.  This is
one typed authored declaration; patch, balance, digest, and wire data remain
derived by `Theory.EffectDeclaration`. -/
def accountMoveDeclaration : Declaration accountMoveSource where
  effects :=
    [.accountMove accountMoveSource accountMoveDestination
      accountMoveResource accountMoveAmount]

def accountMoveArtifact : Artifact :=
  Artifact.ofDeclaration accountMoveDeclaration

theorem accountMoveArtifact_exact :
    accountMoveArtifact.schemaVersion = 1 ∧
    accountMoveArtifact.resourceKind = 2 ∧
    accountMoveArtifact.target = 0 ∧
    accountMoveArtifact.words = [1, 2, 0, 1, 2, 0, 1, 0, 4] := by
  decide

end Minidregg.Compiler.DeclaredEffectArtifact
