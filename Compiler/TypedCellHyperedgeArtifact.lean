/-
# Compiler.TypedCellHyperedgeArtifact -- canonical flat joint-turn data

The typed hyperedge (`Kernel.TypedCellHyperedge`) replaces a call forest with
one ordered, flat family of accepted incidences over one cell.  This module
projects that authoritative Lean declaration to first-order data.  It does not
hash the data, serialize opaque portal witnesses, or define an admission
decision.

Each leg retains its complete request, its family's effect digest (which the
request's `effectsDigest` equals, `legArtifact_effectDigest_bound`), the
family's lawful bytes of its declaration (which decode back to it,
`legArtifact_declaration_decodes`), and a caller-supplied commitment to its
presentation bytes.  The presentation commitment is deliberately an input
because portal witness types are abstract; a concrete controller must bind it
to its registered codec.

This replaces `Compiler.DeclaredHyperedgeArtifact`, which projected the deleted
legacy carrier and could describe only `EffectDeclaration` effects.  The header
schema version is 3.
-/

import Kernel.TypedCellHyperedge
import Compiler.TypedAuthorizationRequestCodec

namespace Minidregg.Compiler.TypedCellHyperedgeArtifact

open Minidregg.Kernel.TypedCellHyperedge
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.AuthorizationDeclaration

set_option autoImplicit false

/-- The sole low request projection also supplies signing and transport bytes. -/
abbrev requestWords := TypedAuthorizationRequestCodec.requestWords

@[simp] theorem requestWords_length (request : RequestWire) :
    (requestWords request).length = 17 := rfl

/-- The emitted joint request and native signature adapter share this exact
source-owned signed request. The signer forwards `signedRequestBytes`; neither
consumer maintains its own field list. -/
theorem signedRequestBytes_exact_artifact (request : SomeRequest) :
    TypedAuthorizationRequestCodec.signedRequestBytes request =
      TypedAuthorizationRequestCodec.requestFrame ++
        (Tower256ConcreteBackend.StreamCodec.list Tower256ConcreteBackend.StreamCodec.nat).encode
          (requestWords (encodeRequest (TypedAuthorizationRequestCodec.planOf request))) := rfl

/-- One incidence's complete public semantic description. -/
structure LegArtifact where
  request : RequestWire
  effectDigest : Nat
  declarationBytes : List UInt8
  presentationRoot : Nat
  deriving DecidableEq, Repr

def LegArtifact.words (leg : LegArtifact) : List Nat :=
  requestWords leg.request ++ [leg.effectDigest, leg.declarationBytes.length] ++
    leg.declarationBytes.map UInt8.toNat ++ [leg.presentationRoot]

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

universe u v w y z

variable {L : Store.Layout.{u, v, w}} {M : CellState.Materializer L Digest}
variable {portal : Portal} {projection : AuthorizationProjection L}

def legArtifact {authState : AuthState} {pre : CellState.Materialized M}
    (leg : Leg.{u, v, w, y, z} portal authState pre)
    (presentationRoot : Digest) : LegArtifact where
  request := encodeRequest ⟨leg.kind, leg.request⟩
  effectDigest := (leg.family.effectDigest leg.declaration).value
  declarationBytes := leg.family.declarationCodec.encode leg.declaration
  presentationRoot := presentationRoot.value

/-- Sole projection from the semantic declaration. -/
def ofDeclaration {Incidence : Type z}
    (declaration : Minidregg.Kernel.TypedCellHyperedge.Declaration.{u, v, w, y, z} L M portal projection Incidence)
    (presentationRoot : Incidence -> Digest) : Header where
  schemaVersion := 3
  preRoot := declaration.pre.root.value
  apex := declaration.apex.value
  compositionMode := compositionModeTag declaration.composition.mode
  legs := declaration.composition.order.map fun incidence =>
    legArtifact (declaration.legs incidence) (presentationRoot incidence)

@[simp] theorem ofDeclaration_preRoot {Incidence : Type z}
    (declaration : Minidregg.Kernel.TypedCellHyperedge.Declaration.{u, v, w, y, z} L M portal projection Incidence)
    (presentationRoot : Incidence -> Digest) :
    (ofDeclaration declaration presentationRoot).preRoot =
      declaration.pre.root.value := rfl

@[simp] theorem ofDeclaration_apex {Incidence : Type z}
    (declaration : Minidregg.Kernel.TypedCellHyperedge.Declaration.{u, v, w, y, z} L M portal projection Incidence)
    (presentationRoot : Incidence -> Digest) :
    (ofDeclaration declaration presentationRoot).apex = declaration.apex.value := rfl

/-- Every emitted request decodes to the exact dependent request owned by its
incidence.  Kind erasure occurs only in `RequestWire`; decoding restores it. -/
theorem legArtifact_request_decodes {authState : AuthState} {pre : CellState.Materialized M}
    (leg : Leg.{u, v, w, y, z} portal authState pre)
    (presentationRoot : Digest) :
    decodeRequest (legArtifact leg presentationRoot).request =
      some ⟨leg.kind, leg.request⟩ :=
  decodeRequest_encodeRequest ⟨leg.kind, leg.request⟩

/-- The emitted effect digest is the one the leg's request commits to. -/
theorem legArtifact_effectDigest_bound {authState : AuthState}
    {pre : CellState.Materialized M}
    (leg : Leg.{u, v, w, y, z} portal authState pre)
    (presentationRoot : Digest) :
    (legArtifact leg presentationRoot).effectDigest = leg.request.effectsDigest.value := by
  simp [legArtifact]

/-- The emitted declaration bytes decode, under the leg's own family codec, to
the exact declaration the leg accepted. -/
theorem legArtifact_declaration_decodes {authState : AuthState}
    {pre : CellState.Materialized M}
    (leg : Leg.{u, v, w, y, z} portal authState pre)
    (presentationRoot : Digest) :
    leg.family.declarationCodec.decode (legArtifact leg presentationRoot).declarationBytes =
      some leg.declaration :=
  leg.family.declarationCodec.decode_encode leg.declaration

@[simp] theorem ofDeclaration_leg_at {Incidence : Type z}
    (declaration : Minidregg.Kernel.TypedCellHyperedge.Declaration.{u, v, w, y, z} L M portal projection Incidence)
    (presentationRoot : Incidence -> Digest)
    (index : Nat) (incidence : Incidence)
    (hat : declaration.composition.order[index]? = some incidence) :
    (ofDeclaration declaration presentationRoot).legs[index]? =
      some (legArtifact (declaration.legs incidence)
        (presentationRoot incidence)) := by
  simp [ofDeclaration, List.getElem?_map, hat]

/-- A shape-valid joint declaration emits exactly one leg per finite
incidence.  This prices the complete flat family in the public header. -/
theorem ofDeclaration_leg_count {Incidence : Type z} [Fintype Incidence]
    (declaration : Minidregg.Kernel.TypedCellHyperedge.Declaration.{u, v, w, y, z} L M portal projection Incidence)
    (presentationRoot : Incidence -> Digest)
    (shape : declaration.ShapeValid) :
    (ofDeclaration declaration presentationRoot).legs.length =
      Fintype.card Incidence := by
  classical
  rw [ofDeclaration]
  simp only [List.length_map]
  have hfinset : declaration.composition.order.toFinset = Finset.univ := by
    ext incidence
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact shape.orderComplete.2 incidence
  calc
    declaration.composition.order.length =
        declaration.composition.order.toFinset.card := by
      exact (List.toFinset_card_of_nodup shape.orderComplete.1).symm
    _ = Finset.univ.card := by rw [hfinset]
    _ = Fintype.card Incidence := Finset.card_univ

/-- info: 'Minidregg.Compiler.TypedCellHyperedgeArtifact.legArtifact_request_decodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms legArtifact_request_decodes
/-- info: 'Minidregg.Compiler.TypedCellHyperedgeArtifact.legArtifact_effectDigest_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms legArtifact_effectDigest_bound
/-- info: 'Minidregg.Compiler.TypedCellHyperedgeArtifact.ofDeclaration_leg_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ofDeclaration_leg_count
/-- info: 'Minidregg.Compiler.TypedCellHyperedgeArtifact.signedRequestBytes_exact_artifact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signedRequestBytes_exact_artifact

end Minidregg.Compiler.TypedCellHyperedgeArtifact
