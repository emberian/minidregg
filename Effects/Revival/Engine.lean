/-
# `Effects/Revival/Engine.lean` — the widened declaration, the registry, the dispatcher, the
engine and completeness keystones, STATED

§1-§5 of the statements (`docs/EFFECTS-REVIVAL.md`).  Candidate-side but kernel-free: it
imports only `Theory.Store`, `Theory.TypedAuthorization` and the stream codecs (`Theory.StreamCodec`), so it and its
proofs build on a small closure.  The live keystones over the deployed controller are in
`Kernel.EffectsRevival.Statements`, which imports this file.
-/
module

public import Theory.Store
public import Theory.TypedAuthorization
public import Theory.StreamCodec

@[expose] public section

namespace Minidregg.Effects.Revival

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false


/-! ## §1. `Substrate` — the guarded primitive algebra a declaration emits into. -/

/-- A state with guarded primitives: `step` is `none` exactly when the primitive's guard
fails at the state it meets.  `writes` is the syntactic footprint of one primitive and
`read` the observation at one location; `Framed` (below) is the substrate's frame law. -/
structure Substrate : Type 1 where
  State : Type
  Prim : Type
  step : Prim → State → Option State
  Loc : Type
  [locDecEq : DecidableEq Loc]
  Obs : Loc → Type
  read : State → (loc : Loc) → Obs loc
  writes : Prim → Finset Loc

attribute [instance] Substrate.locDecEq

namespace Substrate

variable (S : Substrate)

/-- A descriptor's replay: every primitive in order, each guard checked at the state its
prefix produced (`Patch.ValidFrom` + `Patch.run` for the store substrate). -/
def run : S.State → List S.Prim → Option S.State
  | s, [] => some s
  | s, p :: ps => match S.step p s with
    | none => none
    | some s' => run s' ps

/-- The syntactic write footprint of a descriptor. -/
def footprint (ps : List S.Prim) : Finset S.Loc :=
  ps.foldr (fun p acc => S.writes p ∪ acc) ∅

/-- The substrate's frame law: a primitive changes nothing outside its own footprint. -/
def Framed : Prop :=
  ∀ p s s', S.step p s = some s' → ∀ loc, loc ∉ S.writes p → S.read s' loc = S.read s loc

end Substrate

/-- The deployed substrate: `Theory.Store`'s guarded operations over a layout.  A primitive
runs only when `Op.Enabled` holds at the store it meets; its footprint is
`Op.writeAddress?`. -/
def storeSubstrate (L : Layout.{0, 0, 0}) : Substrate where
  State := Store L
  Prim := Store.Op L
  step op s := if op.Enabled s then some (op.apply s) else none
  Loc := Address L
  Obs a := Option (L.Value a.1)
  read s a := s a
  writes op := op.writeAddress?.toFinset

/-! ## §2. `EffectSpec` — the widened declaration. -/

/-- **One effect, one declaration.**  `Ctx` is what the effect consumes of its
transaction (for the live controller: author, operation id, height, source reads);
`O` is the operation payload, syntactic by construction because it carries a canonical
codec; `R` the refusals it may name.

* `sem` emits the descriptor (the guarded patch) or refuses by name.  The post state is the
  descriptor's replay, never a second authored computation.
* `rotate` is the kernel's own per-cell step appended to every admitted descriptor (the
  blinding ratchet, K-HIDE-ROTATE); `rotated` marks the locations it writes.
* `field` classifies locations into capability fields, `amount` their numeric weight (the
  footprint `fieldsCheck` judges); `frame` is the DECLARED set of fields an operation may
  write.
* `accepts`/`version` are the role and schema version the live header checks.
* `verb` is the authority demand (the verb a capability must allow); `view` is what the
  cell's committed law reads (`targetProjection`).  The law itself is the cell's, not the
  effect's.
* `commutes` marks the operations whose admission does not pin the whole cell: they are
  computed at the current cell whatever root the plan observed (an append-only content
  command, `ContentResource.Command.commutes`).  The dispatcher's freshness refusal is
  derived from it (`Handler.admits`); no handler states it by hand.  Default: nothing
  commutes. -/
structure EffectSpec (Ctx : Type) (S : Substrate) (O R : Type) where
  opStream : StreamCodec O
  refusalName : R → String
  accepts : ResourceKind → Bool
  version : Nat
  sem : Ctx → O → S.State → Except R (List S.Prim)
  rotate : Ctx → S.State → List S.Prim
  rotated : S.Loc → Bool
  field : S.Loc → CellField
  amount : (loc : S.Loc) → S.Obs loc → Int
  frame : O → Finset CellField
  verb : (kind : ResourceKind) → O → Verb kind
  view : O → S.State → S.State → List (String × Int)
  commutes : O → Bool := fun _ => false

/-- Every refusal the dispatcher can return.  `refused` carries the declaration's own
name for its refusal; the rest are the dispatcher's, each naming the code. -/
inductive DispatchRefusal where
  | unregistered (code : Nat)
  | malformed (code : Nat)
  | wrongRole (code : Nat)
  | refused (code : Nat) (name : String)
  | outOfFrame (code : Nat)
  | guardFailed (code : Nat)
  | unsupportedVersion (code : Nat)
  | staleTarget (code : Nat)
  /-- Any other refusal of the live controller, by its `Reject` name. -/
  | host (code : Nat) (name : String)
  deriving DecidableEq, Repr

namespace EffectSpec

variable {Ctx : Type} {S : Substrate} {O R : Type} (E : EffectSpec Ctx S O R)

/-- The full emitted descriptor: the operation's patch, then the kernel's rotate. -/
def emitted (ctx : Ctx) (op : O) (s : S.State) : Except R (List S.Prim) :=
  (E.sem ctx op s).map fun ps => ps ++ E.rotate ctx s

/-- Every unsealed location a descriptor writes lies in a declared field of `op`. -/
def InFrame (op : O) (ps : List S.Prim) : Prop :=
  ∀ loc ∈ S.footprint ps, E.rotated loc = false → E.field loc ∈ E.frame op

instance (op : O) (ps : List S.Prim) : Decidable (E.InFrame op ps) := by
  unfold InFrame; infer_instance

/-- **The derived, checked executor.**  The declaration's semantics, then the frame check
(loud: `outOfFrame`), then the replay with every guard (loud: `guardFailed`).  For a
`Complete` declaration both checks are unreachable (§5 completeness), as `invalidPatch` is
for the live content arm (`ContentResource.prepareCell_ok_of_run`). -/
def exec (code : Nat) (ctx : Ctx) (op : O) (s : S.State) : Except DispatchRefusal S.State :=
  match E.sem ctx op s with
  | .error r => .error (.refused code (E.refusalName r))
  | .ok ps =>
    if E.InFrame op (ps ++ E.rotate ctx s) then
      match S.run s (ps ++ E.rotate ctx s) with
      | none => .error (.guardFailed code)
      | some s' => .ok s'
    else .error (.outOfFrame code)

/-- **Completeness (the declaration's proof obligation).**  Every admitted operation stays
in its declared frame and its emitted descriptor replays: the dispatcher's two own
refusals never fire, so every refusal of a complete declaration is one of its own names. -/
def Complete : Prop :=
  ∀ ctx op s ps, E.sem ctx op s = .ok ps →
    E.InFrame op (ps ++ E.rotate ctx s) ∧ (S.run s (ps ++ E.rotate ctx s)).isSome

end EffectSpec

/-! ## §3. The registry and the one dispatcher. -/

/-- A registered declaration over a common cell universe `Cell`: its substrate, its
declaration, the role/version header it checks against the cell (generic per controller:
for the live controller, `selectTarget`'s role and cell law and `computeTarget`'s version,
in that order), whether the plan's observed root is the cell's (`fresh`; for the live
controller, `computeTarget`'s root comparison), and how its typed state is read from and
written back to a cell.  The header states no freshness refusal: `admits` derives it from
`fresh` and the declaration's `commutes`. -/
structure Handler (Ctx Cell : Type) : Type 1 where
  S : Substrate
  O : Type
  R : Type
  spec : EffectSpec Ctx S O R
  header : Ctx → Cell → Except DispatchRefusal Unit
  fresh : Ctx → Cell → Bool := fun _ _ => true
  select : Cell → Option S.State
  pack : S.State → Cell

/-- Sound: `select` and `pack` are inverse both ways (a selected cell IS the packing of
its selection, so nothing outside the selection can be rewritten unseen), and the
substrate is framed. -/
def Handler.Sound {Ctx Cell : Type} (e : Handler Ctx Cell) : Prop :=
  (∀ s, e.select (e.pack s) = some s) ∧
  (∀ cell s, e.select cell = some s → e.pack s = cell) ∧
  e.S.Framed

/-- The derived gate before selection: the handler's header, then freshness.  A stale
plan (`fresh` false) is refused `staleTarget` unless its operation commutes. -/
def Handler.admits {Ctx Cell : Type} (e : Handler Ctx Cell) (code : Nat) (ctx : Ctx) (op : e.O)
    (cell : Cell) : Except DispatchRefusal Unit :=
  match e.header ctx cell with
  | .error r => .error r
  | .ok () => if e.spec.commutes op || e.fresh ctx cell then .ok () else .error (.staleTarget code)

/-- One registered handler fired on a decoded operation and a cell: the gate, selection,
the derived executor, the packed post. -/
def Handler.fire {Ctx Cell : Type} (e : Handler Ctx Cell) (code : Nat) (ctx : Ctx) (op : e.O)
    (cell : Cell) : Except DispatchRefusal Cell :=
  match e.admits code ctx op cell with
  | .error r => .error r
  | .ok () =>
    match e.select cell with
    | none => .error (.wrongRole code)
    | some s => (e.spec.exec code ctx op s).map e.pack

/-- Lawful: sound and complete. -/
def Handler.Lawful {Ctx Cell : Type} (e : Handler Ctx Cell) : Prop :=
  e.Sound ∧ e.spec.Complete

/-- The open registry: wire code ↦ entry. -/
abbrev Registry (Ctx Cell : Type) : Type 1 := List (Nat × Handler Ctx Cell)

/-- **The dispatcher** — the only path from a wire code to an effect.  An unregistered
code refuses by name; a registered one decodes its operation with the entry's own codec,
selects its typed state, and runs the derived executor. -/
def dispatch {Ctx Cell : Type} (R : Registry Ctx Cell) (code : Nat) (bytes : List UInt8)
    (ctx : Ctx) (cell : Cell) : Except DispatchRefusal Cell :=
  match R.lookup code with
  | none => .error (.unregistered code)
  | some e =>
    match e.spec.opStream.toLawful.decode bytes with
    | none => .error (.malformed code)
    | some op => e.fire code ctx op cell

/-- The registry the Host dispatches through: codes unique (a shadowed duplicate would be
a silent twin), every entry lawful — the floor obligations as proof FIELDS. -/
structure LawfulRegistry (Ctx Cell : Type) : Type 1 where
  entries : Registry Ctx Cell
  nodup : (entries.map Prod.fst).Nodup
  /-- Codes are one octet: the payload tag on the wire (`payloadStream`'s tag byte). -/
  octet : ∀ entry ∈ entries, entry.1 < 256
  lawful : ∀ code e, entries.lookup code = some e → e.Lawful

/-! ## §4. `Dispatches` — a predicate on ANY candidate dispatcher. -/

/-- **What it means for `d` to dispatch through `R`**, while the codes in `legacy` are
still hand arms (the migration window; the end state is `legacy = []`).

* `noTwin` — no code is both registered and hand-armed (law 13 as a clause);
* `agreement` — on a registered code and EVERY cell, `d` IS the handler fired;
* `unregistered` — any other code refuses by name;
* `frame` — an admitted registered dispatch leaves every unsealed location outside the
  operation's declared fields unchanged. -/
structure Dispatches {Ctx Cell : Type} (R : Registry Ctx Cell) (legacy : List Nat)
    (d : Nat → List UInt8 → Ctx → Cell → Except DispatchRefusal Cell) : Prop where
  noTwin : ∀ code ∈ legacy, R.lookup code = none
  agreement : ∀ code e, R.lookup code = some e → ∀ (op : e.O) (ctx : Ctx) (cell : Cell),
    d code (e.spec.opStream.encode op) ctx cell = e.fire code ctx op cell
  unregistered : ∀ code, R.lookup code = none → code ∉ legacy →
    ∀ bytes ctx cell, d code bytes ctx cell = .error (.unregistered code)
  frame : ∀ code e, R.lookup code = some e → ∀ bytes ctx cell cell',
    d code bytes ctx cell = .ok cell' →
      ∃ (op : e.O) (s s' : e.S.State), e.spec.opStream.toLawful.decode bytes = some op ∧
        e.select cell = some s ∧ e.select cell' = some s' ∧
        ∀ loc, e.spec.rotated loc = false → e.spec.field loc ∉ e.spec.frame op →
          e.S.read s' loc = e.S.read s loc

/-! ## §5. The engine keystone, the completeness keystone, and their poles. -/

/-- **ENGINE KEYSTONE.**  Over sound entries, the one dispatcher dispatches through its
registry with no hand arms. -/
def EngineKeystone (Ctx Cell : Type) : Prop :=
  ∀ R : Registry Ctx Cell, (∀ code e, R.lookup code = some e → e.Sound) →
    Dispatches R [] (dispatch R)

/-- **COMPLETENESS KEYSTONE.**  Through a lawful registry, every refusal of a well-encoded
operation on a packed state whose gate (header and freshness) passes is one of the entry's
own declared names. -/
def CompletenessKeystone (Ctx Cell : Type) : Prop :=
  ∀ (L : LawfulRegistry Ctx Cell) code e, L.entries.lookup code = some e →
    ∀ (op : e.O) (ctx : Ctx) (s : e.S.State) (r : DispatchRefusal),
      e.admits code ctx op (e.pack s) = .ok () →
      dispatch L.entries code (e.spec.opStream.encode op) ctx (e.pack s) = .error r →
        ∃ x : e.R, r = .refused code (e.spec.refusalName x)

/-! ### The pole data: a two-field toy cell and two entries. -/

/-- Two RAM fields, `false` and `true`, each holding a number. -/
@[reducible] def toyLayout : Layout.{0, 0, 0} where
  Namespace := Bool
  Key := fun _ => Unit
  Value := fun _ => Nat
  discipline := fun _ => .ram

abbrev ToyStore := Store toyLayout
abbrev ToySubstrate := storeSubstrate toyLayout

def toyEmpty : ToyStore := 0

/-- Field `b` set to `n`: an allocation where it is absent, a guarded write where present. -/
def toyWrite (b : Bool) (n : Nat) (s : ToyStore) : List (Store.Op toyLayout) :=
  match s ⟨b, ()⟩ with
  | none => [.allocate b () n]
  | some v => [.write b () v n]

inductive ToyRefusal where
  | tooLarge
  deriving DecidableEq, Repr

def toyRefusalName : ToyRefusal → String
  | .tooLarge => "tooLarge"

/-- The toy entries' verb: each kind's ordinary write verb. -/
def toyVerb : (kind : ResourceKind) → Verb kind
  | .object => .mutateObject
  | .account => .transfer
  | .program => .installProgram

/-- Field `false` is `slot 0`, field `true` is `slot 1`. -/
def toyField (loc : Address toyLayout) : CellField := if loc.1 then .slot 1 else .slot 0

/-- Entry A (code 0): set field `false` to `n`, refusing `tooLarge` above 9.  Declared
frame `{slot 0}`; it never leaves it. -/
def entryASpec : EffectSpec Unit ToySubstrate Nat ToyRefusal where
  opStream := StreamCodec.nat
  refusalName := toyRefusalName
  accepts := fun _ => true
  version := 1
  sem := fun _ n s => if 9 < n then .error .tooLarge else .ok (toyWrite false n s)
  rotate := fun _ _ => []
  rotated := fun _ => false
  field := toyField
  amount := fun _ _ => 0
  frame := fun _ => {.slot 0}
  verb := fun kind _ => toyVerb kind
  view := fun _ _ _ => []

/-- Entry B (code 1): `true` writes field `true` (in its declared frame `{slot 1}`),
`false` writes field `false` — OUT of its frame.  The dispatcher must refuse the latter. -/
def entryBSpec : EffectSpec Unit ToySubstrate Bool ToyRefusal where
  opStream := StreamCodec.bool
  refusalName := toyRefusalName
  accepts := fun _ => true
  version := 1
  sem := fun _ b s => .ok (toyWrite b 1 s)
  rotate := fun _ _ => []
  rotated := fun _ => false
  field := toyField
  amount := fun _ _ => 0
  frame := fun _ => {.slot 1}
  verb := fun kind _ => toyVerb kind
  view := fun _ _ _ => []

/-- The ghost of entry A: it reads the same operation as `n + 1`. -/
def ghostASpec : EffectSpec Unit ToySubstrate Nat ToyRefusal :=
  { entryASpec with sem := fun _ n s => if 9 < n then .error .tooLarge else .ok (toyWrite false (n + 1) s) }

def toyEntry {O R : Type} (spec : EffectSpec Unit ToySubstrate O R) : Handler Unit ToyStore where
  S := ToySubstrate
  O := O
  R := R
  spec := spec
  header := fun _ _ => .ok ()
  select c := some c
  pack s := s

/-- **The two-entry pole.** -/
def toyPole : Registry Unit ToyStore := [(0, toyEntry entryASpec), (1, toyEntry entryBSpec)]

/-- The pole with entry A's reading replaced by its ghost. -/
def toyGhostPole : Registry Unit ToyStore := [(0, toyEntry ghostASpec), (1, toyEntry entryBSpec)]

/-- A fail-open dispatcher: an unregistered code falls through to entry A. -/
def toyFailOpen (code : Nat) (bytes : List UInt8) (ctx : Unit) (cell : ToyStore) :
    Except DispatchRefusal ToyStore :=
  match toyPole.lookup code with
  | none => dispatch toyPole 0 bytes ctx cell
  | some _ => dispatch toyPole code bytes ctx cell

/-- An unframed dispatcher: the derived executor without its frame check (a witness, never
shipped — the house pattern of `execHand`). -/
def dispatchUnframed {Ctx Cell : Type} (R : Registry Ctx Cell) (code : Nat)
    (bytes : List UInt8) (ctx : Ctx) (cell : Cell) : Except DispatchRefusal Cell :=
  match R.lookup code with
  | none => .error (.unregistered code)
  | some e =>
    match e.spec.opStream.toLawful.decode bytes with
    | none => .error (.malformed code)
    | some op =>
      match e.admits code ctx op cell with
      | .error r => .error r
      | .ok () =>
      match e.select cell with
      | none => .error (.wrongRole code)
      | some s =>
        match e.spec.sem ctx op s with
        | .error r => .error (.refused code (e.spec.refusalName r))
        | .ok ps =>
          match e.S.run s (ps ++ e.spec.rotate ctx s) with
          | none => .error (.guardFailed code)
          | some s' => .ok (e.pack s')

/-! ### The engine keystone's ATLAS fields. -/

/-- **Satisfiable.**  The pole dispatches through itself, admits entry A's `5` (field
`false` becomes 5), and refuses entry B's out-of-frame `false` by name. -/
def EngineSatisfiable : Prop :=
  Dispatches toyPole [] (dispatch toyPole) ∧
  dispatch toyPole 0 (StreamCodec.nat.encode 5) () toyEmpty =
    .ok (Store.set toyEmpty ⟨false, ()⟩ (some (5 : Nat))) ∧
  dispatch toyPole 1 (StreamCodec.bool.encode false) () toyEmpty = .error (.outOfFrame 1)

/-- **Teeth.**  `Dispatches toyPole` refutes: a dispatcher whose reading of code 0 differs
(agreement bites), a fail-open dispatcher (unregistered bites), a dispatcher without the
frame check (frame bites on entry B), and a code both registered and hand-armed (noTwin
bites). -/
def EngineTeeth : Prop :=
  ¬ Dispatches toyPole [] (dispatch toyGhostPole) ∧
  ¬ Dispatches toyPole [] toyFailOpen ∧
  ¬ Dispatches toyPole [] (dispatchUnframed toyPole) ∧
  ¬ Dispatches toyPole [1] (dispatch toyPole)

/-- **Premise inhabitation.**  The keystone's premise holds of the pole. -/
def EnginePremise : Prop :=
  ∀ code e, toyPole.lookup code = some e → e.Sound

/-! ### The completeness keystone's ATLAS fields. -/

/-- **Satisfiable.**  Entry A is lawful, and through the registry of entry A alone its
refusal surfaces under its own name. -/
def CompletenessSatisfiable : Prop :=
  (toyEntry entryASpec).Lawful ∧
  dispatch [(0, toyEntry entryASpec)] 0 (StreamCodec.nat.encode 12) () toyEmpty =
    .error (.refused 0 "tooLarge")

/-- **Teeth.**  Entry B is not lawful: its out-of-frame operation (refused `outOfFrame`
in `EngineSatisfiable`) keeps it out of every `LawfulRegistry`. -/
def CompletenessTeeth : Prop := ¬ (toyEntry entryBSpec).Lawful

/-- **Premise inhabitation.**  A lawful registry exists: entry A's. -/
def CompletenessPremise : Prop :=
  ∃ L : LawfulRegistry Unit ToyStore, L.entries = [(0, toyEntry entryASpec)]

/-! ### The derived freshness gate's ATLAS fields. -/

/-- Entry A on a cell whose plan is stale (`fresh` false), its operations declared
commuting or not. -/
def staleToyEntry (commuting : Bool) : Handler Unit ToyStore :=
  { toyEntry { entryASpec with commutes := fun _ => commuting } with fresh := fun _ _ => false }

/-- **Satisfiable and teeth of the gate.**  On a stale plan, a non-commuting operation is
refused `staleTarget` by the dispatcher itself, and a commuting one is dispatched exactly as
on a fresh plan (entry A's `5` lands): staleness bites only where the declaration says the
operation does not commute. -/
def FreshnessGate : Prop :=
  dispatch [(0, staleToyEntry false)] 0 (StreamCodec.nat.encode 5) () toyEmpty =
    .error (.staleTarget 0) ∧
  dispatch [(0, staleToyEntry true)] 0 (StreamCodec.nat.encode 5) () toyEmpty =
    dispatch toyPole 0 (StreamCodec.nat.encode 5) () toyEmpty

/-! ## §6. One dispatch source by construction, and registry extension.

**One source.**  `noTwin` alone only says a supplied legacy list is disjoint from the
registry; it cannot see a hand arm that still exists beside a registered code (two equal
implementations are extensionally indistinguishable).  `composeDispatch R legacy` is the
only shape the host dispatcher may have: the registry decides every registered code and the
legacy arm sees ONLY codes the registry lacks, so a hand arm for a registered code is
unreachable by construction.  The structural half of the rule is not a `Prop`: at each
migration step the legacy arm's input type loses the migrated constructor (the `Payload`
inductive drops `content`), so the old arm no longer typechecks, and a build census checks
that the replaced computation has no remaining production caller (docs/EFFECTS-REVIVAL.md §8).

**Extension.**  Adding entries must not change what any old code means: every byte string
under an old code is decoded, interpreted and executed exactly as before (`Extends`,
`ExtensionPreserves`).  Accepting a previously unregistered code is an intentional
compatibility change; `SafeExtension` makes the policy explicit: a retired code is never
rebound. -/

/-- The host dispatcher's one permitted shape. -/
def composeDispatch {Ctx Cell : Type} (R : Registry Ctx Cell)
    (legacy : Nat → List UInt8 → Ctx → Cell → Except DispatchRefusal Cell) :
    Nat → List UInt8 → Ctx → Cell → Except DispatchRefusal Cell :=
  fun code bytes ctx cell =>
    match R.lookup code with
    | none => legacy code bytes ctx cell
    | some _ => dispatch R code bytes ctx cell

/-- `d` has the one permitted shape over `R`. -/
def OneSource {Ctx Cell : Type} (R : Registry Ctx Cell)
    (d : Nat → List UInt8 → Ctx → Cell → Except DispatchRefusal Cell) : Prop :=
  ∃ legacy, d = composeDispatch R legacy

/-- **The legacy census** (pass 27): the hand arms' own input type has no constructor at a
registered code.  This is what shows deletion: when a code migrates, the legacy input type
must lose its constructor before the census is provable.  (`OneSource` below is only its
extensional shadow: any dispatcher agreeing with `dispatch R` on registered codes satisfies
it.) -/
def LegacyDisjoint {P Ctx Cell : Type} (tagOf : P → Nat) (R : Registry Ctx Cell) : Prop :=
  ∀ p : P, tagOf p ∉ R.map Prod.fst

/-- A toy legacy input type: one payload, at tag 2. -/
inductive ToyLegacy where
  | other
  deriving DecidableEq

def toyLegacyTag : ToyLegacy → Nat
  | .other => 2

/-- **Census satisfiable**: the toy legacy type has no constructor at the pole's codes. -/
def LegacyCensusSatisfiable : Prop := LegacyDisjoint toyLegacyTag toyPole

/-- **Census teeth**: a legacy type that still carries a registered code (tag 0) fails it. -/
def LegacyCensusTeeth : Prop := ¬ LegacyDisjoint (fun (_ : Unit) => 0) toyPole

/-- **One-source satisfiable**: the pole's own dispatcher is one-source (legacy refuses). -/
def OneSourceSatisfiable : Prop := OneSource toyPole (dispatch toyPole)

/-- **One-source teeth**: a dispatcher that reads registered code 0 by another arm (the
ghost) is not one-source over the pole, whatever its legacy arm. -/
def OneSourceTeeth : Prop := ¬ OneSource toyPole (dispatch toyGhostPole)

/-- `R'` extends `R`: every old code keeps its handler. -/
def Extends {Ctx Cell : Type} (R R' : Registry Ctx Cell) : Prop :=
  ∀ code e, R.lookup code = some e → R'.lookup code = some e

/-- **EXTENSION KEYSTONE.**  Under an extension, every byte string under an old code is
dispatched exactly as before: decoding, header, selection, interpretation and execution,
acceptances and refusals alike. -/
def ExtensionPreserves (Ctx Cell : Type) : Prop :=
  ∀ R R' : Registry Ctx Cell, Extends R R' → ∀ code, R.lookup code ≠ none →
    ∀ bytes ctx cell, dispatch R' code bytes ctx cell = dispatch R code bytes ctx cell

/-- The explicit policy for newly accepted codes: an extension that never rebinds a
retired code. -/
def SafeExtension {Ctx Cell : Type} (R R' : Registry Ctx Cell) (retired : List Nat) : Prop :=
  Extends R R' ∧ ∀ code ∈ retired, R'.lookup code = none

/-- **Extension satisfiable**: the pole extends entry A's registry, adding code 1. -/
def ExtensionSatisfiable : Prop := SafeExtension [(0, toyEntry entryASpec)] toyPole []

/-- **Extension teeth**: rebinding an old code is not an extension (the ghost pole
rebinds code 0), and a safe extension may not rebind a retired code. -/
def ExtensionTeeth : Prop :=
  ¬ Extends toyPole toyGhostPole ∧ ¬ SafeExtension [(0, toyEntry entryASpec)] toyPole [1]

/-! ### Prefix consumption (review gap 3).

A registered operation is not a whole wire message.  The deployed target decoder reads the
payload's tag octet, then the payload, then the target's later fields (`targetStream` is a
product with `payloadStream` in its middle).  So the registry is also read as a PREFIX: one
octet, the entry's own `decodePrefix`, and the suffix handed back untouched to the enclosing
decoder.  An extension must preserve that reading on every old code too, not only the
dispatch of a whole operation (`ExtensionPreserves`). -/

/-- A candidate prefix reader: bytes ↦ the code, the operation's bytes, the suffix. -/
abbrev PrefixReader := List UInt8 → Option (Nat × List UInt8 × List UInt8)

/-- The registry's prefix reader: the tag octet, then the entry's own prefix decoder; the
operation's bytes are its canonical encoding. -/
def readPrefix {Ctx Cell : Type} (R : Registry Ctx Cell) : PrefixReader
  | [] => none
  | tag :: rest =>
    match R.lookup tag.toNat with
    | none => none
    | some e => (e.spec.opStream.decodePrefix rest).map fun decoded =>
        (tag.toNat, e.spec.opStream.encode decoded.1, decoded.2)

/-- `read` reads `R` as a prefix.
* `consume`: after a registered code's octet, exactly one operation's encoding is consumed
  and every suffix is handed back untouched;
* `refuse`: an octet at no registered code is refused, never read by another entry;
* `canonical`: whatever it accepts is a registered code's octet, one operation's encoding
  and the suffix, nothing else. -/
structure ConsumesPrefix {Ctx Cell : Type} (R : Registry Ctx Cell) (read : PrefixReader) :
    Prop where
  consume : ∀ code e, R.lookup code = some e → code < 256 → ∀ (op : e.O) (suffix : List UInt8),
    read (UInt8.ofNat code :: (e.spec.opStream.encode op ++ suffix)) =
      some (code, e.spec.opStream.encode op, suffix)
  refuse : ∀ (tag : UInt8) rest, R.lookup tag.toNat = none → read (tag :: rest) = none
  canonical : ∀ bytes code opBytes suffix, read bytes = some (code, opBytes, suffix) →
    ∃ e, R.lookup code = some e ∧ code < 256 ∧ (∃ op : e.O, opBytes = e.spec.opStream.encode op) ∧
      bytes = UInt8.ofNat code :: (opBytes ++ suffix)

/-- **PREFIX KEYSTONE.**  `readPrefix R` reads every registry as a prefix, and an extension
reads every old code's prefix exactly as before (the bytes consumed and the suffix handed
back alike). -/
def PrefixKeystone (Ctx Cell : Type) : Prop :=
  (∀ R : Registry Ctx Cell, ConsumesPrefix R (readPrefix R)) ∧
  (∀ R R' : Registry Ctx Cell, Extends R R' → ∀ code, R.lookup code ≠ none → code < 256 →
    ∀ rest, readPrefix R' (UInt8.ofNat code :: rest) = readPrefix R (UInt8.ofNat code :: rest))

/-- A reader that decodes the operation from ALL the remaining bytes (a top-level decode
where a prefix decode belongs): it hands the enclosing decoder no suffix. -/
def readWhole {Ctx Cell : Type} (R : Registry Ctx Cell) : PrefixReader
  | [] => none
  | tag :: rest =>
    match R.lookup tag.toNat with
    | none => none
    | some e => (e.spec.opStream.toLawful.decode rest).map fun op =>
        (tag.toNat, e.spec.opStream.encode op, [])

/-- A fail-open reader: an octet at no registered code is read by entry A's decoder. -/
def readFailOpen : PrefixReader
  | [] => none
  | tag :: rest =>
    match toyPole.lookup tag.toNat with
    | none => readPrefix toyPole (0 :: rest)
    | some _ => readPrefix toyPole (tag :: rest)

/-- The pole with code 1 rebound to entry A's codec (a natural number where a boolean was). -/
def toyRebindPole : Registry Unit ToyStore := [(0, toyEntry entryASpec), (1, toyEntry entryASpec)]

/-- **Prefix satisfiable**: the pole is read as a prefix, and code 0's `5` followed by a
suffix `[7]` consumes exactly `5`'s encoding and hands back `[7]`. -/
def PrefixSatisfiable : Prop :=
  ConsumesPrefix toyPole (readPrefix toyPole) ∧
  readPrefix toyPole (0 :: (StreamCodec.nat.encode 5 ++ [7])) = some (0, StreamCodec.nat.encode 5, [7])

/-- **Prefix teeth**: a reader that consumes the whole rest fails `consume`; a fail-open
reader fails `refuse`; and rebinding code 1's codec (not an extension) changes what an old
code's prefix reads. -/
def PrefixTeeth : Prop :=
  ¬ ConsumesPrefix toyPole (readWhole toyPole) ∧
  ¬ ConsumesPrefix toyPole readFailOpen ∧
  readPrefix toyRebindPole (1 :: StreamCodec.bool.encode true) ≠
    readPrefix toyPole (1 :: StreamCodec.bool.encode true)

end Minidregg.Effects.Revival
