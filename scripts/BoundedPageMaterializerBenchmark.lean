/-
# Bounded page materializer benchmark

This executable harness measures the actual lawful state codecs and Lean
cSHAKE roots for the concrete four-slot Hyperdocument content, event-history,
and authority/policy pages.  Each family is exercised at occupancies 1--4.

Every timed case first checks exact decode/reopen equality, exact materializer
root equality, the next-slot update result, and canonical lookup through the
family's real semantic projection.  These exercised-input checks are regression
evidence only.  Timings have no acceptance threshold and imply neither native
refinement nor a cryptographic claim.
-/
import Compiler.CredentialAuthorityPageMaterializer
import Compiler.HyperdocumentContentPageMaterializer
import Compiler.HyperdocumentEventPageMaterializer

namespace Minidregg.Bench.BoundedPageMaterializer

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def slotWhen {alpha : Type} (occupancy slot : Nat) (value : alpha) : Option alpha :=
  if slot ≤ occupancy then some value else none

namespace ContentCase

open Minidregg.Compiler.HyperdocumentContentPageMaterializer

def fourthElementId : ElementId := ⟨⟨103⟩⟩

def fourthElementRecord : ElementRecord :=
  { elementRecord with parent := some rootElement }

def entryAt : Nat -> Entry
  | 1 => .document sourceDocument documentRecord
  | 2 => .element rootElement elementRecord
  | 3 => .link forwardLinkId forwardLink
  | _ => .element fourthElementId fourthElementRecord

def page (occupancy : Nat) : Page where
  contentDomain := ⟨8000⟩
  document := sourceDocument
  pageNumber := 0
  slot0 := slotWhen occupancy 1 (entryAt 1)
  slot1 := slotWhen occupancy 2 (entryAt 2)
  slot2 := slotWhen occupancy 3 (entryAt 3)
  slot3 := slotWhen occupancy 4 (entryAt 4)

def state (occupancy : Nat) : LogicalState schema :=
  stateOfOption (some (page occupancy))

def bytes (occupancy : Nat) : List UInt8 :=
  stateCodec.encode (state occupancy)

def updateChecksum (occupancy : Nat) : Nat :=
  match (page (occupancy - 1)).admitInsert (entryAt occupancy) with
  | .error _ => 0
  | .ok post => post.1.entries.length

def updateExact (occupancy : Nat) : Bool :=
  match (page (occupancy - 1)).admitInsert (entryAt occupancy) with
  | .error _ => false
  | .ok post => decide (post.1 = page occupancy)

def lookupExact (occupancy : Nat) : Bool :=
  let canonical := (page occupancy).toCanonicalState
  match occupancy with
  | 1 =>
      match (show Option DocumentRecord from
        Hyperdocument.lookup canonical .documents sourceDocument) with
      | none => false
      | some found => found == documentRecord
  | 2 =>
      match (show Option ElementRecord from
        Hyperdocument.lookup canonical .elements rootElement) with
      | none => false
      | some found => found == elementRecord
  | 3 =>
      match (show Option LinkRecord from
        Hyperdocument.lookup canonical .links forwardLinkId) with
      | none => false
      | some found => found == forwardLink.toCanonical
  | _ =>
      match (show Option ElementRecord from
        Hyperdocument.lookup canonical .elements fourthElementId) with
      | none => false
      | some found => found == fourthElementRecord

def lookupChecksum (occupancy : Nat) : Nat :=
  if lookupExact occupancy then occupancy else 0

def reopenExact (occupancy : Nat) : Bool :=
  match stateCodec.decode (bytes occupancy) with
  | none => false
  | some reopened => decide (pageAt reopened = some (page occupancy))

def reopenChecksum (occupancy : Nat) : Nat :=
  match stateCodec.decode (bytes occupancy) with
  | none => 0
  | some reopened => (pageAt reopened).map (fun value => value.entries.length) |>.getD 0

def rootExact (occupancy : Nat) : Bool :=
  decide (
    rootBytes (bytes occupancy) =
      (CellState.materialize materializer (state occupancy)).root)

def semanticExact (occupancy : Nat) : Bool :=
  decide ((page occupancy).Valid) && updateExact occupancy &&
    lookupExact occupancy && reopenExact occupancy && rootExact occupancy

@[noinline] def variantPage (occupancy nonce : Nat) : Page :=
  { page occupancy with pageNumber := nonce }

@[noinline] def variantBytes (occupancy nonce : Nat) : List UInt8 :=
  stateCodec.encode (stateOfOption (some (variantPage occupancy nonce)))

@[noinline] def encodeWork (occupancy nonce : Nat) : Nat :=
  (variantBytes occupancy nonce).foldl
    (fun checksum byte => checksum + byte.toNat) 0

@[noinline] def rootWork (occupancy nonce : Nat) : Nat :=
  rootBytes (variantBytes occupancy nonce) |>.value |>.mod 1000003

@[noinline] def updateWork (occupancy nonce : Nat) : Nat :=
  match (variantPage (occupancy - 1) nonce).admitInsert (entryAt occupancy) with
  | .error _ => 0
  | .ok post => post.1.entries.length + post.1.pageNumber

@[noinline] def lookupWork (occupancy nonce : Nat) : Nat :=
  let selected := variantPage occupancy nonce
  let canonical := selected.toCanonicalState
  let found : Bool := match occupancy with
    | 1 => (Hyperdocument.lookup canonical .documents sourceDocument).isSome
    | 2 => (Hyperdocument.lookup canonical .elements rootElement).isSome
    | 3 => (Hyperdocument.lookup canonical .links forwardLinkId).isSome
    | _ => (Hyperdocument.lookup canonical .elements fourthElementId).isSome
  if found then selected.pageNumber + occupancy else 0

@[noinline] def reopenWork (occupancy nonce : Nat) : Nat :=
  match stateCodec.decode (variantBytes occupancy nonce) with
  | none => 0
  | some reopened =>
      (pageAt reopened).map
        (fun value => value.entries.length + value.pageNumber) |>.getD 0

end ContentCase

namespace EventCase

open Minidregg.Compiler.HyperdocumentEventPageMaterializer

def recordAt (index : Nat) : VersionEventRecord :=
  { exampleRecord with
    semanticVersion := index
    operation := ⟨⟨4004 + index⟩⟩
    requestId := ⟨6006 + index⟩
    effectId := ⟨7007 + index⟩ }

def entryAt (index : Nat) : Entry :=
  let record := recordAt index
  { key := deriveVersionEventId eventPreimageCodec eventDerivation record
    record := record }

def page (occupancy : Nat) : Page where
  historyDomain := exampleRecord.historyDomain
  document := exampleRecord.document
  pageNumber := 0
  slot0 := slotWhen occupancy 1 (entryAt 1)
  slot1 := slotWhen occupancy 2 (entryAt 2)
  slot2 := slotWhen occupancy 3 (entryAt 3)
  slot3 := slotWhen occupancy 4 (entryAt 4)

/-- The event materializer intentionally exposes a page representation rather
than a mutable container.  The benchmark update fills its first empty physical
slot, matching the page format without adding a second semantic admission API. -/
def insert? (prior : Page) (entry : Entry) : Option Page :=
  match prior.slot0 with
  | none => some { prior with slot0 := some entry }
  | some _ =>
      match prior.slot1 with
      | none => some { prior with slot1 := some entry }
      | some _ =>
          match prior.slot2 with
          | none => some { prior with slot2 := some entry }
          | some _ =>
              match prior.slot3 with
              | none => some { prior with slot3 := some entry }
              | some _ => none

def state (occupancy : Nat) : LogicalState schema :=
  stateOfOption (some (page occupancy))

def bytes (occupancy : Nat) : List UInt8 :=
  stateCodec.encode (state occupancy)

def updateExact (occupancy : Nat) : Bool :=
  decide (insert? (page (occupancy - 1)) (entryAt occupancy) =
    some (page occupancy))

def updateChecksum (occupancy : Nat) : Nat :=
  match insert? (page (occupancy - 1)) (entryAt occupancy) with
  | none => 0
  | some post => post.entries.length

def lookupExact (occupancy : Nat) : Bool :=
  match (show Option VersionEventRecord from
    (page occupancy).toSparseStore .events (entryAt occupancy).key) with
  | none => false
  | some found => found == recordAt occupancy

def lookupChecksum (occupancy : Nat) : Nat :=
  if lookupExact occupancy then occupancy else 0

def reopenExact (occupancy : Nat) : Bool :=
  match stateCodec.decode (bytes occupancy) with
  | none => false
  | some reopened => decide (pageAt reopened = some (page occupancy))

def reopenChecksum (occupancy : Nat) : Nat :=
  match stateCodec.decode (bytes occupancy) with
  | none => 0
  | some reopened => (pageAt reopened).map (fun value => value.entries.length) |>.getD 0

def rootExact (occupancy : Nat) : Bool :=
  decide (
    rootBytes (bytes occupancy) =
      (CellState.materialize materializer (state occupancy)).root)

def entryValid (occupancy : Nat) (entry : Entry) : Bool :=
  entry.record.historyDomain == (page occupancy).historyDomain &&
    entry.record.document == (page occupancy).document &&
    entry.record.parents == [] &&
    entry.key.digest == eventScheme.address entry.record.toCausalPreimage

def semanticValid (occupancy : Nat) : Bool :=
  (page occupancy).entries.all (entryValid occupancy) &&
    decide (((page occupancy).entries.map Entry.key).Nodup)

def semanticExact (occupancy : Nat) : Bool :=
  semanticValid occupancy && updateExact occupancy && lookupExact occupancy &&
    reopenExact occupancy && rootExact occupancy

@[noinline] def variantPage (occupancy nonce : Nat) : Page :=
  { page occupancy with pageNumber := nonce }

@[noinline] def variantBytes (occupancy nonce : Nat) : List UInt8 :=
  stateCodec.encode (stateOfOption (some (variantPage occupancy nonce)))

@[noinline] def encodeWork (occupancy nonce : Nat) : Nat :=
  (variantBytes occupancy nonce).foldl
    (fun checksum byte => checksum + byte.toNat) 0

@[noinline] def rootWork (occupancy nonce : Nat) : Nat :=
  rootBytes (variantBytes occupancy nonce) |>.value |>.mod 1000003

@[noinline] def updateWork (occupancy nonce : Nat) : Nat :=
  match insert? (variantPage (occupancy - 1) nonce) (entryAt occupancy) with
  | none => 0
  | some post => post.entries.length + post.pageNumber

@[noinline] def lookupWork (occupancy nonce : Nat) : Nat :=
  let selected := variantPage occupancy nonce
  let found := selected.toSparseStore .events (entryAt occupancy).key
  if found.isSome then selected.pageNumber + occupancy else 0

@[noinline] def reopenWork (occupancy nonce : Nat) : Nat :=
  match stateCodec.decode (variantBytes occupancy nonce) with
  | none => 0
  | some reopened =>
      (pageAt reopened).map
        (fun value => value.entries.length + value.pageNumber) |>.getD 0

end EventCase

namespace AuthorityCase

open Minidregg.Compiler.CredentialAuthorityPageMaterializer

def secondPolicy : PolicyId := ⟨43⟩
def secondRevocation : RevocationKey := .channel ⟨44⟩

def entryAt : Nat -> Entry
  | 1 => oldPolicy
  | 2 => activeRevocation
  | 3 => .policy secondPolicy 5 ⟨5500⟩
  | _ => .revocation secondRevocation true

def page (occupancy : Nat) : Page where
  authorityDomain := ⟨8200⟩
  pageNumber := 4
  slot0 := slotWhen occupancy 1 (entryAt 1)
  slot1 := slotWhen occupancy 2 (entryAt 2)
  slot2 := slotWhen occupancy 3 (entryAt 3)
  slot3 := slotWhen occupancy 4 (entryAt 4)

def state (occupancy : Nat) : LogicalState schema :=
  stateOfOption (some (page occupancy))

def bytes (occupancy : Nat) : List UInt8 :=
  stateCodec.encode (state occupancy)

def updateExact (occupancy : Nat) : Bool :=
  match (page (occupancy - 1)).admitInsert (entryAt occupancy) with
  | .error _ => false
  | .ok post => decide (post.1 = page occupancy)

def updateChecksum (occupancy : Nat) : Nat :=
  match (page (occupancy - 1)).admitInsert (entryAt occupancy) with
  | .error _ => 0
  | .ok post => post.1.entries.length

def lookupExact (occupancy : Nat) : Bool :=
  match occupancy with
  | 1 => decide ((page occupancy).policyAddressAt examplePolicy 2 = ⟨2200⟩)
  | 2 => decide (exampleRevocation ∈ (page occupancy).revoked)
  | 3 => decide ((page occupancy).policyAddressAt secondPolicy 5 = ⟨5500⟩)
  | _ => decide (secondRevocation ∈ (page occupancy).revoked)

def lookupChecksum (occupancy : Nat) : Nat :=
  if lookupExact occupancy then occupancy else 0

def reopenExact (occupancy : Nat) : Bool :=
  match stateCodec.decode (bytes occupancy) with
  | none => false
  | some reopened => decide (pageAt reopened = some (page occupancy))

def reopenChecksum (occupancy : Nat) : Nat :=
  match stateCodec.decode (bytes occupancy) with
  | none => 0
  | some reopened => (pageAt reopened).map (fun value => value.entries.length) |>.getD 0

def rootExact (occupancy : Nat) : Bool :=
  decide (
    rootBytes (bytes occupancy) =
      (CellState.materialize materializer (state occupancy)).root)

def semanticExact (occupancy : Nat) : Bool :=
  decide ((page occupancy).Valid) && updateExact occupancy &&
    lookupExact occupancy && reopenExact occupancy && rootExact occupancy

@[noinline] def variantPage (occupancy nonce : Nat) : Page :=
  { page occupancy with pageNumber := nonce }

@[noinline] def variantBytes (occupancy nonce : Nat) : List UInt8 :=
  stateCodec.encode (stateOfOption (some (variantPage occupancy nonce)))

@[noinline] def encodeWork (occupancy nonce : Nat) : Nat :=
  (variantBytes occupancy nonce).foldl
    (fun checksum byte => checksum + byte.toNat) 0

@[noinline] def rootWork (occupancy nonce : Nat) : Nat :=
  rootBytes (variantBytes occupancy nonce) |>.value |>.mod 1000003

@[noinline] def updateWork (occupancy nonce : Nat) : Nat :=
  match (variantPage (occupancy - 1) nonce).admitInsert (entryAt occupancy) with
  | .error _ => 0
  | .ok post => post.1.entries.length + post.1.pageNumber

@[noinline] def lookupWork (occupancy nonce : Nat) : Nat :=
  let selected := variantPage occupancy nonce
  let found : Bool := match occupancy with
    | 1 => selected.policyAddressAt examplePolicy 2 == ⟨2200⟩
    | 2 => decide (exampleRevocation ∈ selected.revoked)
    | 3 => selected.policyAddressAt secondPolicy 5 == ⟨5500⟩
    | _ => decide (secondRevocation ∈ selected.revoked)
  if found then selected.pageNumber + occupancy else 0

@[noinline] def reopenWork (occupancy nonce : Nat) : Nat :=
  match stateCodec.decode (variantBytes occupancy nonce) with
  | none => 0
  | some reopened =>
      (pageAt reopened).map
        (fun value => value.entries.length + value.pageNumber) |>.getD 0

end AuthorityCase

def samples : Nat := 7
def ordinaryRepetitions : Nat := 16
def rootRepetitions : Nat := 1

def repeatChecksum (operation : Nat -> Nat) : Nat -> Nat -> Nat
  | 0, accumulator => accumulator
  | repetitions + 1, accumulator =>
      repeatChecksum operation repetitions
        (accumulator + operation repetitions)

def requireSemantic (family : String) (occupancy : Nat) (exact : Bool) : IO Unit :=
  unless exact do
    throw <| IO.userError s!"semantic regression: {family} occupancy {occupancy}"

def runStage (family : String) (occupancy : Nat) (stage : String)
    (encodedBytes repetitions : Nat) (operation : Nat -> Nat) : IO Unit := do
  let sink ← IO.mkRef 0
  for sample in List.range samples do
    let started : Nat ← IO.monoNanosNow
    let checksum := repeatChecksum operation repetitions 0
    sink.set checksum
    let forcedChecksum ← sink.get
    let finished : Nat ← IO.monoNanosNow
    let elapsed := finished - started
    let operationsPerSecond :=
      if elapsed = 0 then 0 else repetitions * 1000000000 / elapsed
    let phase := if sample = 0 then "first-measured" else "repeated"
    IO.println s!"sample,minidregg/bounded-page-materializer/v1,{family},\
      {occupancy},{stage},{phase},{sample},{repetitions},{elapsed},\
      {operationsPerSecond},{encodedBytes},{forcedChecksum}"

def runContent (occupancy : Nat) : IO Unit := do
  requireSemantic "content" occupancy (ContentCase.semanticExact occupancy)
  let encoded := ContentCase.bytes occupancy
  runStage "content" occupancy "encode" encoded.length ordinaryRepetitions
    (ContentCase.encodeWork occupancy)
  runStage "content" occupancy "root" encoded.length rootRepetitions
    (ContentCase.rootWork occupancy)
  runStage "content" occupancy "insert" encoded.length ordinaryRepetitions
    (ContentCase.updateWork occupancy)
  runStage "content" occupancy "lookup_projection" encoded.length ordinaryRepetitions
    (ContentCase.lookupWork occupancy)
  runStage "content" occupancy "reopen" encoded.length ordinaryRepetitions
    (ContentCase.reopenWork occupancy)

def runEvent (occupancy : Nat) : IO Unit := do
  requireSemantic "event_history" occupancy (EventCase.semanticExact occupancy)
  let encoded := EventCase.bytes occupancy
  runStage "event_history" occupancy "encode" encoded.length ordinaryRepetitions
    (EventCase.encodeWork occupancy)
  runStage "event_history" occupancy "insert" encoded.length ordinaryRepetitions
    (EventCase.updateWork occupancy)
  runStage "event_history" occupancy "lookup_projection" encoded.length ordinaryRepetitions
    (EventCase.lookupWork occupancy)
  runStage "event_history" occupancy "reopen" encoded.length ordinaryRepetitions
    (EventCase.reopenWork occupancy)
  runStage "event_history" occupancy "root" encoded.length rootRepetitions
    (EventCase.rootWork occupancy)

def runAuthority (occupancy : Nat) : IO Unit := do
  requireSemantic "authority_policy" occupancy
    (AuthorityCase.semanticExact occupancy)
  let encoded := AuthorityCase.bytes occupancy
  runStage "authority_policy" occupancy "encode" encoded.length ordinaryRepetitions
    (AuthorityCase.encodeWork occupancy)
  runStage "authority_policy" occupancy "insert" encoded.length ordinaryRepetitions
    (AuthorityCase.updateWork occupancy)
  runStage "authority_policy" occupancy "lookup_projection" encoded.length
    ordinaryRepetitions
    (AuthorityCase.lookupWork occupancy)
  runStage "authority_policy" occupancy "reopen" encoded.length ordinaryRepetitions
    (AuthorityCase.reopenWork occupancy)
  runStage "authority_policy" occupancy "root" encoded.length rootRepetitions
    (AuthorityCase.rootWork occupancy)

def main : IO Unit := do
  IO.println "benchmark=minidregg/bounded-page-materializer/v1"
  IO.println s!"samples={samples}"
  IO.println s!"ordinary_repetitions={ordinaryRepetitions}"
  IO.println s!"root_repetitions={rootRepetitions}"
  IO.println "timing=IO.monoNanosNow; raw samples; no performance threshold"
  IO.println "record,schema,family,occupancy,stage,phase,sample,repetitions,elapsed_ns,ops_per_s,encoded_bytes,checksum"
  for occupancy in [1, 2, 3, 4] do
    runContent occupancy
    runEvent occupancy
    runAuthority occupancy
  IO.println "semantic_status=PASS"

end Minidregg.Bench.BoundedPageMaterializer

def main : IO Unit :=
  Minidregg.Bench.BoundedPageMaterializer.main
