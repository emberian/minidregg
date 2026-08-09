/-
# Compiler.DeclaredHyperedgeArtifact -- canonical flat joint-turn data

The executable `DeclaredHyperedge` replaces a call forest with one ordered,
flat family of incidences.  This module projects that authoritative Lean
declaration to first-order data.  It does not hash the data, serialize opaque
portal witnesses, or define an admission decision.

Each leg retains the complete derived request, the complete typed effect
artifact, and a caller-supplied commitment to its presentation bytes.  The
presentation commitment is deliberately an input because portal witness types
are abstract; a concrete controller must bind it to its registered codec.
-/

import Kernel.DeclaredHyperedge
import Compiler.DeclaredEffectArtifact

namespace Minidregg.Compiler.DeclaredHyperedgeArtifact

open Minidregg.Kernel.DeclaredHyperedge
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.CellState

set_option autoImplicit false

/-- Literal order of the existing sixteen-field request wire. -/
def requestWords (request : RequestWire) : List Nat :=
  [request.domain, request.semantics, request.federation, request.resourceKind,
   request.subject, request.subjectKeyEpoch, request.target, request.verb,
   request.argsDigest, request.effectsDigest, request.nonce, request.height,
   request.preStateRoot, request.policyId, request.policyEpoch, request.cost]

@[simp] theorem requestWords_length (request : RequestWire) :
    (requestWords request).length = 16 := rfl

/-- One incidence's complete public semantic description. -/
structure LegArtifact where
  request : RequestWire
  effect : DeclaredEffectArtifact.Artifact
  presentationRoot : Nat
  deriving DecidableEq, Repr

def LegArtifact.words (leg : LegArtifact) : List Nat :=
  requestWords leg.request ++
    [leg.effect.words.length] ++ leg.effect.words ++ [leg.presentationRoot]

def compositionModeTag : CompositionMode -> Nat
  | .disjoint => 1
  | .canonical => 2

/-- The complete ordered joint-turn header.  The incidence order is the
declaration's authoritative composition order, not an ambient enumeration. -/
structure Header where
  schemaVersion : Nat
  preRoot : Nat
  apex : Nat
  compositionMode : Nat
  legs : List LegArtifact
  deriving DecidableEq, Repr

def Header.words (header : Header) : List Nat :=
  [header.schemaVersion, header.preRoot, header.apex,
    header.compositionMode, header.legs.length] ++
  header.legs.flatMap fun leg => [leg.words.length] ++ leg.words

variable {portal : Portal}
variable {materializer : Materializer Minidregg.Theory.DeclaredTurn.effectSchema Digest}
variable {Incidence : Type} [Fintype Incidence] [DecidableEq Incidence]

def legArtifact
    {preRoot apex : Digest}
    (leg : Leg portal preRoot apex)
    (presentationRoot : Digest) : LegArtifact where
  request := encodeRequest ⟨leg.kind, leg.request⟩
  effect := DeclaredEffectArtifact.Artifact.ofDeclaration leg.effects
  presentationRoot := presentationRoot.value

/-- Sole projection from the semantic declaration. -/
def ofDeclaration
    (declaration : Declaration portal materializer Incidence)
    (presentationRoot : Incidence -> Digest) : Header where
  schemaVersion := 1
  preRoot := declaration.pre.root.value
  apex := declaration.apex.value
  compositionMode := compositionModeTag declaration.composition.mode
  legs := declaration.composition.order.map fun incidence =>
    legArtifact (declaration.legs incidence) (presentationRoot incidence)

@[simp] theorem ofDeclaration_preRoot
    (declaration : Declaration portal materializer Incidence)
    (presentationRoot : Incidence -> Digest) :
    (ofDeclaration declaration presentationRoot).preRoot =
      declaration.pre.root.value := rfl

@[simp] theorem ofDeclaration_apex
    (declaration : Declaration portal materializer Incidence)
    (presentationRoot : Incidence -> Digest) :
    (ofDeclaration declaration presentationRoot).apex = declaration.apex.value := rfl

/-- Every emitted request decodes to the exact dependent request owned by its
incidence.  Kind erasure occurs only in `RequestWire`; decoding restores it. -/
theorem legArtifact_request_decodes
    {preRoot apex : Digest}
    (leg : Leg portal preRoot apex)
    (presentationRoot : Digest) :
    decodeRequest (legArtifact leg presentationRoot).request =
      some ⟨leg.kind, leg.request⟩ := by
  exact decodeRequest_encodeRequest ⟨leg.kind, leg.request⟩

@[simp] theorem legArtifact_effect_exact
    {preRoot apex : Digest}
    (leg : Leg portal preRoot apex)
    (presentationRoot : Digest) :
    (legArtifact leg presentationRoot).effect =
      DeclaredEffectArtifact.Artifact.ofDeclaration leg.effects := rfl

@[simp] theorem ofDeclaration_leg_at
    (declaration : Declaration portal materializer Incidence)
    (presentationRoot : Incidence -> Digest)
    (index : Nat) (incidence : Incidence)
    (hat : declaration.composition.order[index]? = some incidence) :
    (ofDeclaration declaration presentationRoot).legs[index]? =
      some (legArtifact (declaration.legs incidence)
        (presentationRoot incidence)) := by
  simp [ofDeclaration, List.getElem?_map, hat]

/-- A shape-valid joint declaration emits exactly one leg per finite
incidence.  This prices the complete flat family in the public header. -/
theorem ofDeclaration_leg_count
    (declaration : Declaration portal materializer Incidence)
    (presentationRoot : Incidence -> Digest)
    (shape : declaration.ShapeValid) :
    (ofDeclaration declaration presentationRoot).legs.length =
      Fintype.card Incidence := by
  rw [ofDeclaration]
  simp only [List.length_map]
  have hfinset : declaration.composition.order.toFinset = Finset.univ := by
    ext incidence
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact shape.compositionValid.1.2 incidence
  calc
    declaration.composition.order.length =
        declaration.composition.order.toFinset.card := by
      exact (List.toFinset_card_of_nodup shape.compositionValid.1.1).symm
    _ = Finset.univ.card := by rw [hfinset]
    _ = Fintype.card Incidence := Finset.card_univ

#print axioms legArtifact_request_decodes
#print axioms ofDeclaration_leg_count

end Minidregg.Compiler.DeclaredHyperedgeArtifact
