/-
# Kernel.TurnGen -- a seeded generator of intents and presented turns (HP-6 SIM)

HP-DESIGN §4 / §5.2 HP-6.  A pure, deterministic generator over a small deployed
World: a splitmix64 stream from a seed, and one `Step` per call, read off the
Host's current World and receiver snapshot (the generator is an honest client
that reads before it writes, and a dishonest one that does not).

Two step shapes:

* `Step.intent` -- a `DataIntent` for the Host path of today: the receiver's
  `DurableDataIntent.execute`, then `Turn.ofIntent` against the Host's World, then
  `World.admit`.  Honest classes: a content birth, a field write/free, a send (an
  append to an event history under a read guard of a content cell), a call (fresh
  nullifiers, a fee, a write), an upgrade (a ROM program birth and the content
  field that points at it), a retirement, a claim-only read.  Invalid classes: a
  stale pre-root, a stale read guard, a respent nullifier, a duplicated nullifier,
  a retry of an accepted intent, a transaction-id conflict, a fee past the
  meter, an undecodable post image, a kind change, a ROM rewrite, an append-only
  rewrite, a write of a retired id, an empty intent.
* `Step.probe` -- a Turn presented as it is (HP-3's request shape): a turn
  derived against an OLDER World (a stale client), or an honest turn with one
  field broken so each `World.Reject` constructor is reachable.  Probes are
  decided on both sides and never committed.

Bounds: `Kernel/Bounds.lean` (HP-1) is not on the mirror at this base; the sizes
here are literal and small (`Sizes`), and `sizes_within_design` names the
design bounds (HP-DESIGN §6) they sit under.  SWITCH: import `Kernel.Bounds` and
state `sizes_within_design` against its constants when HP-1 lands.
-/
import Kernel.TurnLog

namespace Minidregg.Kernel.TurnGen

open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Theory.ResourceCost (Lane Charge)
open Minidregg.Kernel.World
open Minidregg.Kernel.DeployedBridge
open Minidregg.Kernel.DeployedHistory
open Minidregg.Kernel.TurnOfIntent
open Minidregg.Kernel.TurnLog
open Minidregg.Kernel.DurableReceiver (IntentRecord Seed)
open Minidregg.Kernel.DurableDataIntent
  (DataIntent DataWrite ReadGuard StableNullifier StableEvent DataSnapshot)
open Minidregg.Compiler

set_option autoImplicit false

/-! ## Sizes (literal until HP-1 lands) -/

/-- The generator's sizes. -/
structure Sizes where
  /-- Live generated cells the generator keeps around (births stop past it). -/
  cells : Nat
  /-- Field keys per content cell. -/
  fields : Nat
  /-- Nullifiers per call. -/
  nullifiers : Nat
  /-- The seed's `feeDebit` allowance; calls spend 1..3 of it. -/
  fee : Nat
  deriving Repr

/-- The merge-gate size. -/
def Sizes.small : Sizes := { cells := 10, fields := 4, nullifiers := 2, fee := 600 }

/-- HP-DESIGN §6 bounds this generator sits under (SWITCH to `Kernel.Bounds`). -/
def designLegsPerTurnMax : Nat := 256
def designCellsTouchedMax : Nat := 512
def designNullifiersPerTurnMax : Nat := 64

/-- A generated turn touches at most two written cells, one guard, one absence
pin and the mutations' extra leg or create; it carries at most `nullifiers + 1`
nullifiers. -/
def Sizes.legsMax (s : Sizes) : Nat := s.cells + 4
def Sizes.nullifiersMax (s : Sizes) : Nat := s.nullifiers + 1

theorem sizes_within_design :
    Sizes.small.legsMax ≤ designLegsPerTurnMax ∧
      Sizes.small.legsMax + 2 ≤ designCellsTouchedMax ∧
      Sizes.small.nullifiersMax ≤ designNullifiersPerTurnMax := by decide

/-! ## The stream -/

/-- splitmix64. -/
structure Rng where
  state : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- The stream of a seed starts at the seed's MIXED value: seeding with a linear
function of the seed made seed n+1's stream seed n's shifted by one draw
(measured: seeds 2 and 3 gave the same counts). -/
def Rng.ofSeed (seed : Nat) : Rng := ⟨(Rng.next ⟨UInt64.ofNat seed ^^^ 0x2545F4914F6CDD1D⟩).1⟩

/-- The roots the deployed receiver binds. -/
abbrev RB : List UInt8 → Digest := ResourceBirthCodec.rootBytes

/-- What the generator remembers between steps. -/
structure GenState where
  rng : Rng
  /-- Fresh-name counter: transaction ids, cell ids, nullifiers, event keys. -/
  tick : Nat := 0
  /-- Every seeded or generated cell id, oldest first. -/
  ids : List CellId
  /-- Nullifiers of accepted intents, newest first (≤ 16). -/
  spent : List StableNullifier := []
  /-- Accepted intents, newest first (≤ 16). -/
  accepted : List (DataIntent RB) := []
  /-- Recent Host Worlds, newest first (≤ 4), for stale clients. -/
  past : List DWorld := []

abbrev GenM := StateM GenState

def below (n : Nat) : GenM Nat := do
  let g ← get
  let (x, r) := g.rng.next
  set { g with rng := r }
  return if n = 0 then 0 else x.toNat % n

def pick {α : Type} (xs : List α) : GenM (Option α) := do
  if xs.isEmpty then return none
  let i ← below xs.length
  return xs[i]?

def fresh : GenM Nat := modifyGet fun g => (g.tick, { g with tick := g.tick + 1 })

/-! ## Cells of three kinds -/

/-- Little-endian two bytes. -/
def natBytes (n : Nat) : List UInt8 := [UInt8.ofNat (n % 256), UInt8.ofNat (n / 256 % 256)]

/-- Cell ids: the seed's two at `seedBase`, generated ones from `cellBase`. -/
def seedBase : Nat := 1000
def cellBase : Nat := 1000000

abbrev CStore := Store Theory.Hyperdocument.layout
abbrev EStore := Store HyperdocumentEventLog.Sparse.layout
abbrev PStore := Store NockProgramCodec.layout

def principal : Theory.Hyperdocument.PrincipalRef :=
  { subject := ⟨1⟩, capabilityKind := .object, capabilityId := ⟨1⟩ }

def fieldAddr (k : Nat) : Address Theory.Hyperdocument.layout :=
  ⟨.fields, ({ owner := .document ⟨⟨7⟩⟩, name := ⟨k⟩ } : Theory.Hyperdocument.FieldKey)⟩

def fieldRec (v : Nat) : Theory.Hyperdocument.FieldRecord :=
  { valueType := .natural, value := (v : Nat), merge := .exclusive, writtenBy := principal,
    writtenAt := ⟨⟨v⟩⟩ }

def eventAddr (n : Nat) : Address HyperdocumentEventLog.Sparse.layout :=
  ⟨.events, (⟨⟨n⟩⟩ : Theory.Hyperdocument.VersionEventId)⟩

def eventRec (n : Nat) : Theory.Hyperdocument.VersionEventRecord :=
  { historyDomain := ⟨1⟩, document := ⟨⟨7⟩⟩, schema := { schemaId := ⟨2⟩, version := 1 },
    semanticVersion := n, operation := ⟨⟨n⟩⟩, parents := [], preStateRoot := ⟨n⟩,
    postStateRoot := ⟨n + 1⟩, requestId := ⟨n⟩, effectId := ⟨n⟩, author := principal }

def program (n : Nat) : NockProgramCodec.Program :=
  { evaluator := ⟨1⟩, jam := natBytes n,
    abi := { version := 1, sample := [], outputs := [], libraries := [], fuel := n + 1 },
    params := [] }

def contentCell (s : CStore) : Cell deployedR := ⟨.content, s⟩
def eventCell (s : EStore) : Cell deployedR := ⟨.eventHistory, s⟩
def programCell (n : Nat) : Cell deployedR :=
  ⟨.nockProgram, NockProgramCodec.stateOfOption (some (program n))⟩

def contentOf (w : DWorld) (c : CellId) : Option CStore :=
  (w.cells c).bind fun cell => cell.storeAt .content

def eventsOf (w : DWorld) (c : CellId) : Option EStore :=
  (w.cells c).bind fun cell => cell.storeAt .eventHistory

def isKind (w : DWorld) (k : deployedR.Kind) (c : CellId) : Bool :=
  match w.cells c with
  | some cell => decide (cell.kind = k)
  | none => false

/-- The image bytes of a cell slot. -/
def bytesOfCell (cell : Cell deployedR) : List UInt8 := encodeCell (some cell)

/-- The retired image. -/
def retiredBytes : List UInt8 :=
  ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry .retired

/-! ## The synthetic genesis -/

/-- A content cell with field 0 set and an empty event history, the `feeDebit`
lane at `sz.fee` and every other lane plentiful. -/
def genesisSeed (sz : Sizes) : Seed :=
  { absentBytes := encodeCell none
    cells :=
      [(⟨seedBase⟩, bytesOfCell (contentCell (Store.set 0 (fieldAddr 0) (some (fieldRec 1))))),
       (⟨seedBase + 1⟩, bytesOfCell (eventCell 0))]
    available := fun l => if l = .feeDebit then sz.fee else 1000000000 }

def GenState.init (seed : Nat) : GenState :=
  { rng := Rng.ofSeed seed, ids := [seedBase, seedBase + 1] }

/-! ## Intents -/

/-- The step the generator emits. -/
inductive Step where
  | intent (cls : String) (i : DataIntent RB)
  | probe (cls : String) (t : DTurn deployedR Digest)

def Step.cls : Step → String
  | .intent c _ => c
  | .probe c _ => c

/-- An honest write: the pre-root is the one the receiver holds. -/
def honestWrite (snap : DataSnapshot RB) (c : CellId) (post : List UInt8) : DataWrite :=
  { cellId := ⟨c⟩, expectedPre := snap.model.roots ⟨c⟩, exactPost := RB post,
    canonicalPostBytes := post }

def honestGuard (snap : DataSnapshot RB) (c : CellId) : ReadGuard :=
  { cellId := ⟨c⟩, expectedRoot := snap.model.roots ⟨c⟩ }

def event (n : Nat) : StableEvent :=
  { codecVersion := 1, domain := ⟨5⟩, eventId := ⟨n⟩, canonicalBytes := natBytes n }

def nullifier (n : Nat) : StableNullifier :=
  { codecVersion := 1, domain := ⟨3⟩, nullifierId := ⟨n⟩, canonicalBytes := natBytes n }

/-- Bind an intent and set its storage lane to what the derived turn writes
(what every deployed receiver charges, `DeployedCharge.storageCharge`); `fee` on
`feeDebit`, nothing else. -/
def assemble (w : DWorld) (tx : Nat) (writes : List DataWrite) (guards : List ReadGuard)
    (nulls : List StableNullifier) (fee : Nat) : Option (DataIntent RB) := do
  let pre ← (IntentRecord.mk ⟨tx⟩ writes guards nulls 0 (event tx) none).bind? RB
  let t := turnOf bridge history (fun c => w.cells c) pre
  let storage := storageOf history t.creates t.legs t.event
  return { pre with exactCharge := fun l =>
    if l = .storageBytes then storage else if l = .feeDebit then fee else 0 }

/-- The context a step is generated against. -/
structure View where
  world : DWorld
  snap : DataSnapshot RB
  height : Nat

def live (v : View) (k : deployedR.Kind) : GenM (List CellId) := do
  return (← get).ids.filter (isKind v.world k)

def retiredIds (v : View) : GenM (List CellId) := do
  return (← get).ids.filter fun c => (v.world.retired c).isSome

def newCell : GenM CellId := do
  let n ← fresh
  modify fun g => { g with ids := g.ids ++ [cellBase + n] }
  return cellBase + n

/-- A content birth with one or two fields. -/
def birth (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let c ← newCell
  let k ← below sz.fields
  let x ← below 1000
  let s : CStore := Store.set (Store.set 0 (fieldAddr 0) (some (fieldRec x)))
    (fieldAddr k) (some (fieldRec (x + 1)))
  let tx ← fresh
  return assemble v.world tx [honestWrite v.snap c (bytesOfCell (contentCell s))] [] [] 0

/-- The post store of a field change on `s`: set a fresh value, or free a set field. -/
def fieldChange (sz : Sizes) (s : CStore) : GenM CStore := do
  let k ← below sz.fields
  let x ← below 1000
  match s (fieldAddr k) with
  | some r =>
      let r : Theory.Hyperdocument.FieldRecord := r
      if (← below 3) = 0 then return Store.set s (fieldAddr k) none
      let r' := fieldRec (x + 2000)
      return if r = r' then Store.set s (fieldAddr k) none else Store.set s (fieldAddr k) (some r')
  | none => return Store.set s (fieldAddr k) (some (fieldRec x))

/-- A field write of a live content cell. -/
def writeField (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let some c ← pick (← live v .content) | birth sz v
  let some s := contentOf v.world c | birth sz v
  let s' ← fieldChange sz s
  let tx ← fresh
  return assemble v.world tx [honestWrite v.snap c (bytesOfCell (contentCell s'))] [] [] 0

/-- A send: append one event to a live history, guarding a content cell. -/
def send (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let some e ← pick (← live v .eventHistory) | birth sz v
  let some s := eventsOf v.world e | birth sz v
  let n ← fresh
  let s' : EStore := Store.set s (eventAddr n) (some (eventRec n))
  let guards := match (← pick (← live v .content)) with
    | some c => [honestGuard v.snap c]
    | none => []
  let tx ← fresh
  return assemble v.world tx [honestWrite v.snap e (bytesOfCell (eventCell s'))] guards [] 0

/-- A call with a grant: fresh nullifiers, a fee, a field write. -/
def call (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let some c ← pick (← live v .content) | birth sz v
  let some s := contentOf v.world c | birth sz v
  let s' ← fieldChange sz s
  let k := 1 + (← below sz.nullifiers)
  let mut ns := []
  for _ in [0:k] do ns := nullifier (← fresh) :: ns
  let fee := 1 + (← below 3)
  let tx ← fresh
  return assemble v.world tx [honestWrite v.snap c (bytesOfCell (contentCell s'))] [] ns fee

/-- An upgrade: a program birth (ROM) and the content field that names it. -/
def upgrade (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let some c ← pick (← live v .content) | birth sz v
  let some s := contentOf v.world c | birth sz v
  let p ← newCell
  let s' : CStore := Store.set s (fieldAddr 0) (some (fieldRec p))
  let tx ← fresh
  return assemble v.world tx
    [honestWrite v.snap p (bytesOfCell (programCell p)),
     honestWrite v.snap c (bytesOfCell (contentCell s'))] [] [] 0

/-- A retirement of a live content cell (its leg empties it). -/
def retire (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let cs ← live v .content
  if cs.length < 2 then return ← birth sz v
  let some c ← pick cs | birth sz v
  let tx ← fresh
  return assemble v.world tx [honestWrite v.snap c retiredBytes] [] [] 0

/-- A claim-only read: a fresh nullifier under a read guard, no writes. -/
def claim (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let some c ← pick (← live v .content) | birth sz v
  let n ← fresh
  let tx ← fresh
  return assemble v.world tx [] [honestGuard v.snap c] [nullifier n] 1

/-! ## Invalid intents -/

def staleDigest (n : Nat) : Digest := ⟨n * 7919 + 3⟩

/-- A write whose pre-root is not the held one. -/
def stalePre (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let some i ← writeField sz v | return none
  let ws := i.writes.map fun w => { w with expectedPre := staleDigest w.cellId.value }
  return assemble v.world i.transactionId.value ws i.readGuards i.nullifiers (i.exactCharge .feeDebit)

/-- A send whose read guard is not the held root. -/
def staleGuard (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let some i ← send sz v | return none
  if i.readGuards.isEmpty then return some i
  let gs := i.readGuards.map fun g => { g with expectedRoot := staleDigest g.cellId.value }
  return assemble v.world i.transactionId.value i.writes gs i.nullifiers 0

/-- A call that spends an already spent nullifier. -/
def respend (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let some n ← pick (← get).spent | call sz v
  let some i ← call sz v | return none
  return assemble v.world i.transactionId.value i.writes i.readGuards (n :: i.nullifiers.drop 1)
    (i.exactCharge .feeDebit)

/-- A call that names one nullifier twice. -/
def dupNull (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let some i ← call sz v | return none
  match i.nullifiers with
  | n :: _ =>
      return assemble v.world i.transactionId.value i.writes i.readGuards [n, n] (i.exactCharge .feeDebit)
  | [] => return some i

/-- The retry of an accepted intent, exactly. -/
def retry (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  match ← pick (← get).accepted with
  | some i => return some i
  | none => writeField sz v

/-- An accepted intent's transaction id over a different write. -/
def conflict (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let some old ← pick (← get).accepted | writeField sz v
  let some i ← writeField sz v | return none
  return assemble v.world old.transactionId.value i.writes i.readGuards i.nullifiers 0

/-- A fee past what the meter holds. -/
def overBudget (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let some i ← call sz v | return none
  return assemble v.world i.transactionId.value i.writes i.readGuards i.nullifiers
    (v.world.meter .feeDebit + 1 + (← below 3))

/-- A post image no codec reads. -/
def undecodable (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let some c ← pick (← live v .content) | birth sz v
  let tx ← fresh
  return assemble v.world tx [honestWrite v.snap c [68, 82, 2, 1, 255, 255]] [] [] 0

/-- An event history's image written over a content cell. -/
def kindChange (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let some c ← pick (← live v .content) | birth sz v
  let tx ← fresh
  return assemble v.world tx [honestWrite v.snap c (bytesOfCell (eventCell 0))] [] [] 0

/-- A ROM program rewritten. -/
def romRewrite (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let some p ← pick (← live v .nockProgram) | upgrade sz v
  let tx ← fresh
  return assemble v.world tx [honestWrite v.snap p (bytesOfCell (programCell (p + 1)))] [] [] 0

/-- An append-only event record rewritten. -/
def appendRewrite (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let some e ← pick (← live v .eventHistory) | send sz v
  let some s := eventsOf v.world e | send sz v
  let some n ← pick ((List.range (← get).tick).filter fun n => (s (eventAddr n)).isSome) | send sz v
  let s' : EStore := Store.set s (eventAddr n) (some (eventRec (n + 1)))
  let tx ← fresh
  return assemble v.world tx [honestWrite v.snap e (bytesOfCell (eventCell s'))] [] [] 0

/-- A write of a retired id. -/
def retiredWrite (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let some c ← pick (← retiredIds v) | retire sz v
  let tx ← fresh
  return assemble v.world tx [honestWrite v.snap c (bytesOfCell (contentCell 0))] [] [] 0

/-- A claim asserting a live content cell absent: its read guard's root is
the absent slot's.  The pin of the absent slot's digest is asserted absence,
so the World refuses it as `guardFailed` (and the receiver's preflight). -/
def absentClaimPresent (sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let some c ← pick (← live v .content) | birth sz v
  let n ← fresh
  let tx ← fresh
  return assemble v.world tx [] [{ cellId := ⟨c⟩, expectedRoot := RB (encodeCell none) }]
    [nullifier n] 1

/-- A claim asserting a never-born cell present: its read guard's root is a
content cell's. -/
def presentClaimAbsent (_sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let n ← fresh
  let tx ← fresh
  return assemble v.world tx []
    [{ cellId := ⟨cellBase + 999999⟩, expectedRoot := RB (bytesOfCell (contentCell 0)) }]
    [nullifier n] 1

/-- No writes, no nullifiers. -/
def emptyIntent (_sz : Sizes) (v : View) : GenM (Option (DataIntent RB)) := do
  let tx ← fresh
  return assemble v.world tx [] [] [] 0

/-! ## Presented turns (probes) -/

/-- An honest intent's turn derived against an OLDER World: a stale client. -/
def staleTurn (sz : Sizes) (v : View) : GenM (Option (DTurn deployedR Digest)) := do
  let some old ← pick (← get).past | return none
  let ov : View := { v with world := old }
  let some i ← (if (← below 2) = 0 then writeField sz ov else send sz ov) | return none
  return (Turn.ofIntent bridge history old i).toOption

/-- An honest turn with one field broken, so a named `Reject` is reachable. -/
def mutated (sz : Sizes) (v : View) : GenM (Option (String × DTurn deployedR Digest)) := do
  let some i ← writeField sz v | return none
  let some t := (Turn.ofIntent bridge history v.world i).toOption | return none
  let contents ← live v .content
  let others := contents.filter fun c => c ∉ t.legs.map Leg.cell
  let gone ← retiredIds v
  let spent := (← get).spent
  let accepted := (← get).accepted
  let absentId := cellBase + 999999
  let coin ← below 2
  let n ← below 12
  let named : Option (String × DTurn deployedR Digest) :=
    if n = 0 then some ("empty", { t with legs := [], creates := [], retires := [], pins := [] })
    else if n = 1 then some ("dup-leg", { t with legs := t.legs ++ t.legs.take 1 })
    else if n = 2 then
      (match others.head?, coin with
      | some c, 0 => some ("absent-present", { t with pins := t.pins ++ [(c, history.cellDigest none)] })
      | _, _ => some ("present-absent",
          { t with pins := t.pins ++ [(absentId, history.cellDigest (some (contentCell 0)))] }))
    else if n = 3 then
      (match gone.head? with
      | some c => some ("absent-retired", { t with pins := t.pins ++ [(c, history.cellDigest none)] })
      | none => some ("missing-cell", { t with legs := t.legs ++ [⟨absentId, .content, []⟩] }))
    else if n = 4 then
      (match others.find? (fun c => (contentOf v.world c).any fun s => s ≠ 0) with
      | some c => some ("retire-nonempty", { t with retires := t.retires ++ [c] })
      | none => some ("dup-retire", { t with retires := [absentId, absentId] }))
    else if n = 5 then some ("missing-room",
      { t with creates := (absentId, contentCell 0, some (absentId + 1)) :: t.creates })
    else if n = 6 then some ("window", if v.height = 0 then { t with notBefore := 3 }
      else { t with validUntil := some (v.height - 1) })
    else if n = 7 then some ("charge",
      { t with charge := fun l => if l = .storageBytes then t.charge l + 1 else t.charge l })
    else if n = 8 then
      (match spent.head? with
      | some k => some ("spent", { t with nullifiers := [bridge.key k] })
      | none => some ("dup-null", { t with nullifiers := [⟨1⟩, ⟨1⟩] }))
    else if n = 9 then
      (match accepted.head? with
      | some old => some ("replay", { t with txId := old.transactionId })
      | none => some ("empty", { t with legs := [], creates := [], retires := [], pins := [] }))
    else if n = 10 then some ("image-not-rom", { t with creates :=
      (absentId, contentCell (Store.set 0 (fieldAddr 0) (some (fieldRec 1))), none) :: t.creates })
    else
      (match others.head? with
      | some c => some ("kind-mismatch", { t with legs := t.legs ++ [⟨c, .eventHistory, []⟩] })
      | none => some ("dup-create", { t with
          creates := [(absentId, contentCell 0, none), (absentId, contentCell 0, none)] }))
  -- Every mutation but `charge` keeps the charge rule (storage = the patch bytes), so the
  -- named refusal is the one the mutation aims at and not `chargeMismatch`.
  return named.map fun (c, t') =>
    if c = "charge" then (c, t') else
      (c, { t' with charge := fun l => if l = .storageBytes then patchBytes history t' else t'.charge l })

/-! ## One step -/

/-- The fallback probe: a turn that does nothing (`Reject.emptyTurn`). -/
def emptyTurn : DTurn deployedR Digest :=
  { txId := ⟨0⟩, creates := [], legs := [], retires := [], event := event 0 }

/-- The class table: weight, name, generator. -/
def intentClasses (sz : Sizes) : List (Nat × String × (View → GenM (Option (DataIntent RB)))) :=
  [ (10, "birth", birth sz), (20, "write", writeField sz), (10, "send", send sz),
    (8, "call", call sz), (4, "upgrade", upgrade sz), (3, "retire", retire sz),
    (5, "claim", claim sz),
    (3, "stale-pre", stalePre sz), (3, "stale-guard", staleGuard sz), (3, "respend", respend sz),
    (2, "dup-null", dupNull sz), (3, "retry", retry sz), (2, "conflict", conflict sz),
    (2, "over-budget", overBudget sz), (2, "undecodable", undecodable sz),
    (2, "kind-change", kindChange sz), (1, "rom-rewrite", romRewrite sz),
    (1, "append-rewrite", appendRewrite sz), (1, "retired-write", retiredWrite sz),
    (1, "empty", emptyIntent sz),
    (2, "absent-claim-present", absentClaimPresent sz),
    (2, "present-claim-absent", presentClaimAbsent sz) ]

/-- Probe weights: 6 stale turns, 9 mutations, out of 100 with the intents' 85. -/
def probeWeight : Nat := 15

def choose {α : Type} : List (Nat × α) → Nat → Option α
  | [], _ => none
  | (w, a) :: rest, n => if n < w then some a else choose rest (n - w)

/-- One step against the Host's view.  Births stop once `sz.cells` generated
cells are live. -/
def next (sz : Sizes) (v : View) : GenM Step := do
  let x ← below 100
  if x < probeWeight then
    if x < 6 then
      if let some t ← staleTurn sz v then return .probe "stale-turn" t
    if let some (c, t) ← mutated sz v then return .probe c t
  let liveN := ((← get).ids.filter fun c => (v.world.cells c).isSome).length
  let table := (intentClasses sz).map fun (w, c, f) =>
    (if c = "birth" ∧ liveN ≥ sz.cells then 0 else w, (c, f))
  let total := (table.map Prod.fst).sum
  let some (c, f) := choose table (← below total) | return .probe "none" emptyTurn
  match ← f v with
  | some i => return .intent c i
  | none =>
      match ← birth sz v with
      | some i => return .intent "birth" i
      | none => return .probe "none" emptyTurn

/-- Remember an accepted intent (for retries, conflicts and respends) and the
World it was admitted at (for stale clients). -/
def note (i : DataIntent RB) (before : DWorld) : GenM Unit :=
  modify fun g =>
    { g with
      accepted := (i :: g.accepted).take 16
      spent := (i.nullifiers ++ g.spent).take 16
      past := (before :: g.past).take 4 }

end Minidregg.Kernel.TurnGen
