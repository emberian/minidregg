/-
# Kernel.StoryLaw -- the table-to-law generator of a sealed story

A story (docs/PLACE.md §2.8) is a transition table a friend writes and then seals; after `story seal` the
client (`native/resource-client/src/story.rs`, `table_law`) installs one law on every player's cell,
generated from the table. This module is that generator in Lean (`law`), the embed of the client's
own output for the tale (between the markers, written by `scripts/gen-storylaw.py`, with the `rfl`
that the two agree), and the premise a receiver discharges (`StoryInstalled`, `checkInstalled`).
It lives in `Kernel` so a Host receiver may import it; the theorems about the law are in
`Assurance.StoryLaw` and `Assurance.StoryHistory`.
-/
module

public import Kernel.LawHistory

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Kernel.StoryLaw

open Minidregg.Pred (Pred State eval)
open Minidregg.Kernel.DeclaredResourceProjection (Values fieldName get)
set_option autoImplicit false

/-! ## §1. A table, as the law reads it -/

/-- An edge of the table: an exit or an act from scene `src` to scene `dst`; `needs` is the index
of the item that must already be held. The word a player types (`go north`, `act open`) is the
client's: the law sees only the two scenes. -/
structure Edge where
  src : Int
  dst : Int
  needs : Option Nat
deriving DecidableEq, Repr

/-- The part of a table the law depends on: its edges, and for each item (in the table's
order) the scene it lies in. Scene texts, the start and the end scenes are the client's. -/
structure Table where
  edges : List Edge
  items : List Int
deriving DecidableEq, Repr

/-- `carries/ITEM` of the table's `i`-th item. -/
def carry (i : Nat) : Nat := 2 + i

/-- The items, numbered from `k`. -/
def numbered : Nat → List Int → List (Nat × Int)
  | _, [] => []
  | k, s :: rest => (k, s) :: numbered (k + 1) rest

/-! ## §2. The law -/

/-- `not (verb == write)`: the guard every game clause carries (`LawLeaf.writeGuard`). -/
def writeGuard : Pred := .not (.eq "request/verb" 2)

/-- A game clause: one of `xs`, or the request is not a write. -/
def guard (xs : List Pred) : Pred := Pred.any (xs ++ [writeGuard])

def management : Pred := Pred.any [.eq "request/verb" 1, .eq "request/verb" 2]

def mover (S : Int) : Pred := guard [.eq "request/subject" S]

def turn : Pred := guard [.eq (fieldName 1 "delta") 1]

def edgeStep (e : Edge) : Pred :=
  Pred.all [.eq (fieldName 0 "before") e.src, .eq (fieldName 0 "after") e.dst]

def exits (t : Table) : Pred := guard ([.eq (fieldName 0 "delta") 0] ++ t.edges.map edgeStep)

def needsClause (e : Edge) (i : Nat) : Pred :=
  guard [.not (edgeStep e), .eq (fieldName (carry i) "before") 1]

def needsClauses (t : Table) : List Pred := t.edges.filterMap fun e => e.needs.map (needsClause e)

def here (i : Nat) (s : Int) : Pred :=
  guard [.eq (fieldName (carry i) "delta") 0,
    Pred.all [.eq (fieldName 0 "before") s, .eq (fieldName 0 "delta") 0]]

def once (i : Nat) : Pred :=
  guard [.eq (fieldName (carry i) "delta") 0,
    Pred.all [.eq (fieldName (carry i) "before") 0, .eq (fieldName (carry i) "after") 1]]

def progress (t : Table) : Pred :=
  guard ([.not (.eq (fieldName 0 "delta") 0)] ++
    (numbered 0 t.items).map fun p => .not (.eq (fieldName (carry p.1) "delta") 0))

/-- The clauses in the installed order (the order a refusal names the first failing one in). -/
def clauses (t : Table) (S : Int) : List Pred :=
  [management, mover S, turn, exits t] ++ needsClauses t ++
    (numbered 0 t.items).map (fun p => here p.1 p.2) ++
    (numbered 0 t.items).map (fun p => once p.1) ++ [progress t]

/-- **The sealed law of player `S`'s cell in a story with table `t`.** -/
def law (t : Table) (S : Int) : Pred := Pred.all (clauses t S)

/-! ## The tale: its generated law -/

-- BEGIN GENERATED (scripts/gen-storylaw.py)
/-- The tale's table, as the client parsed it: edges in (from, to) order, item scenes in item-name order. -/
def taleTable : Table := ⟨[⟨0, 1, none⟩, ⟨1, 2, none⟩, ⟨1, 3, some 0⟩, ⟨3, 4, none⟩], [1]⟩

/-- The client's law for player `S` of the tale, as `story seal` generates it. -/
def taleEmbedded (S : Int) : Pred :=
  Pred.all [
    Pred.any [
      .eq "request/verb" 1,
      .eq "request/verb" 2],
    Pred.any [
      .eq "request/subject" S,
      .not (.eq "request/verb" 2)],
    Pred.any [
      .eq "resource/field/1/delta" 1,
      .not (.eq "request/verb" 2)],
    Pred.any [
      .eq "resource/field/0/delta" 0,
      Pred.all [
        .eq "resource/field/0/before" 0,
        .eq "resource/field/0/after" 1],
      Pred.all [
        .eq "resource/field/0/before" 1,
        .eq "resource/field/0/after" 2],
      Pred.all [
        .eq "resource/field/0/before" 1,
        .eq "resource/field/0/after" 3],
      Pred.all [
        .eq "resource/field/0/before" 3,
        .eq "resource/field/0/after" 4],
      .not (.eq "request/verb" 2)],
    Pred.any [
      .not (Pred.all [
          .eq "resource/field/0/before" 1,
          .eq "resource/field/0/after" 3]),
      .eq "resource/field/2/before" 1,
      .not (.eq "request/verb" 2)],
    Pred.any [
      .eq "resource/field/2/delta" 0,
      Pred.all [
        .eq "resource/field/0/before" 1,
        .eq "resource/field/0/delta" 0],
      .not (.eq "request/verb" 2)],
    Pred.any [
      .eq "resource/field/2/delta" 0,
      Pred.all [
        .eq "resource/field/2/before" 0,
        .eq "resource/field/2/after" 1],
      .not (.eq "request/verb" 2)],
    Pred.any [
      .not (.eq "resource/field/0/delta" 0),
      .not (.eq "resource/field/2/delta" 0),
      .not (.eq "request/verb" 2)]]
-- END GENERATED

/-- **The client's generated law is this file's `law`** of the generated table. -/
theorem tale_embedded_is_law (S : Int) : taleEmbedded S = law taleTable S := by rfl
section Kernel
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Compiler

variable {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient}
  {ground : Ground deployment} {command : Command}

/-- The authenticated effective closure includes the sealed story law of `t` for player `S` as an active component. -/
def StoryInstalled (t : Table) (S : Int)
    {prepared : PreparedInvocation deployment profile ambient ground command}
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command) : Prop :=
  Minidregg.Kernel.LawHistory.ActiveComponent
    (policyConfig prepared tuple incidence) (law t S)

/-- Derive the installed-law assurance premise from the receiver's cached,
authenticated effective graph; no caller assertion or second resolver is used. -/
def checkInstalled (t : Table) (S : Int)
    {prepared : PreparedInvocation deployment profile ambient ground command}
    (tuple : PreparedTuple (plan prepared)) (incidence : Incidence command)
    (resolved : Minidregg.Compiler.ComposedPolicyAdmission.PreparedLaw
      (policyConfig prepared tuple incidence)) :
    Option (PLift (StoryInstalled t S tuple incidence)) :=
  Minidregg.Kernel.LawHistory.checkActiveComponent resolved (law t S)

end Kernel

end Minidregg.Kernel.StoryLaw
