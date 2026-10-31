/-
# Kernel.DeployedTurnCompact -- the persisted Turn: digest guards, no old values (FD-1 R4b / FD-2)

ROOT 10-14: the log entry is the Turn, persisted with DIGEST GUARDS and
old-value elision.  Every leg `Turn.ofIntent` derives is `legPatch k s s'`
(guards of the unchanged present addresses, then one change op per changed
address) from the store `s` the cell holds once the turn's creates have run.
Such a leg is persisted as

  cell · kind tag · `rootBytes` of the held cell (the guard, 32 bytes) · the
  changed addresses with their NEW values only.

The follower decodes it AGAINST ITS WORLD (`decodeTurnAt w`): the held store is
read from `w`, its root is compared with the stored digest (a mismatch is a
failed guard: `none`), and the leg is rebuilt as `legPatch k s (applyChanges s
changes)`.  Any other leg is persisted verbatim (`encodeLeg`).

* `applyChanges_changesOf` -- the changes rebuild `s'` exactly.
* `decodeTurnAt_encodeTurnAt` -- on the world it was written against, the
  compact entry decodes to exactly the turn: the follower admits what the
  writer admitted, byte for byte (`encodeTurn` of it, hence its journal digest).
* `decodeLegAt_other` -- if a persisted leg decodes against DIFFERENT held
  cells to a different leg, the operation exhibits two different canonical cell
  byte strings with one `rootBytes` (a cSHAKE256 collision on concrete inputs):
  the digest guard is exactly as strong as that hash.
-/
module

public import Kernel.DeployedTurnCodec
public import Kernel.Bounds
public import Theory.AssertAxioms

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

namespace Minidregg.Kernel.DeployedTurnCompact

open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.World
open Minidregg.Kernel.DeployedBridge
open Minidregg.Kernel.DeployedHistory
open Minidregg.Kernel.DeployedTurnCodec
open Minidregg.Kernel.TurnOfIntent
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent (TransactionId StableEvent)

set_option autoImplicit false

/-! ## Store changes -/

section Changes

variable {L : Layout.{0, 0, 0}}

/-- A change: an address and its new value (`none` = freed). -/
abbrev Change (L : Layout.{0, 0, 0}) := Σ a : Address L, Option (L.Value a.1)

/-- The changed addresses of `as` from `s` to `s'`, with their new values. -/
def changesOf (as : List (Address L)) (s s' : Store L) : List (Change L) :=
  as.filterMap fun a => if s a = s' a then none else some ⟨a, s' a⟩

/-- Apply changes in order. -/
def applyChanges (s : Store L) (cs : List (Change L)) : Store L :=
  cs.foldl (fun st c => st.set c.1 c.2) s

private theorem applyChanges_go (s s' : Store L) :
    ∀ (l : List (Address L)) (t : Store L), l.Nodup →
      (∀ a, a ∉ l → t a = s' a) → (∀ a ∈ l, t a = s a) →
      applyChanges t (changesOf l s s') = s'
  | [], t, _, out, _ => by
      apply DFinsupp.ext
      intro a
      exact out a (by simp)
  | x :: rest, t, nd, out, inn => by
      have ndr := (List.nodup_cons.mp nd).2
      have hx := (List.nodup_cons.mp nd).1
      by_cases e : s x = s' x
      · have hc : changesOf (x :: rest) s s' = changesOf rest s s' := by
          simp [changesOf, e]
        rw [hc]
        refine applyChanges_go s s' rest t ndr (fun a ha => ?_) (fun a ha => inn a (by simp [ha]))
        by_cases hax : a = x
        · subst hax; rw [inn a (by simp), e]
        · exact out a (by simp [hax, ha])
      · have hc : changesOf (x :: rest) s s' = ⟨x, s' x⟩ :: changesOf rest s s' := by
          simp [changesOf, e]
        rw [hc]
        show applyChanges (t.set x (s' x)) (changesOf rest s s') = s'
        refine applyChanges_go s s' rest _ ndr (fun a ha => ?_) (fun a ha => ?_)
        · by_cases hax : a = x
          · subst hax; simp
          · rw [Store.set_ne _ _ _ _ hax]; exact out a (by simp [hax, ha])
        · have hax : a ≠ x := fun h => hx (h ▸ ha)
          rw [Store.set_ne _ _ _ _ hax]; exact inn a (by simp [ha])

/-- **The changes rebuild the post store exactly**, from any address list that
covers both supports. -/
theorem applyChanges_changesOf {as : List (Address L)} {s s' : Store L} (nd : as.Nodup)
    (cover : ∀ a, s a ≠ none ∨ s' a ≠ none → a ∈ as) :
    applyChanges s (changesOf as s s') = s' :=
  applyChanges_go s s' as s nd
    (fun a ha => by
      by_cases h1 : s a = none
      · by_cases h2 : s' a = none
        · rw [h1, h2]
        · exact absurd (cover a (Or.inr h2)) ha
      · exact absurd (cover a (Or.inl h1)) ha)
    (fun _ _ => rfl)

end Changes

/-! ## The compact leg -/

/-- A change's bytes: the read-op carrier `read ns key value` (its op stream). -/
def changeBytes (k : deployedR.Kind) (c : Change (deployedR.layout k)) : List UInt8 :=
  encodeOp k (.read c.1.1 c.1.2 c.2)

def decodeChange (k : deployedR.Kind) (bytes : List UInt8) : Option (Change (deployedR.layout k)) :=
  match full (opStream k) bytes with
  | some (.read ns key value) => some ⟨⟨ns, key⟩, value⟩
  | _ => none

theorem decodeChange_changeBytes (k : deployedR.Kind) (c : Change (deployedR.layout k)) :
    decodeChange k (changeBytes k c) = some c := by
  obtain ⟨⟨ns, key⟩, value⟩ := c
  have h := full_encode (opStream k) (.read ns key value)
  rw [opStream_encode] at h
  simp [decodeChange, changeBytes, h]

/-- The held cells once the turn's creates have run (legs run after creates). -/
def heldAfter (w : World deployedR TransactionId Digest) (t : DTurn deployedR Digest)
    (c : CellId) : Option (Cell deployedR) :=
  match t.creates.find? (fun x => x.1 == c) with
  | some x => some x.2.1
  | none => w.cells c

/-- The store a leg runs from, at the leg's kind. -/
def heldStore (held : CellId → Option (Cell deployedR)) (leg : Leg deployedR) :
    Option (Store (deployedR.layout leg.kind)) :=
  (held leg.cell).bind fun cell => cell.storeAt leg.kind

/-- Whether a leg is the derived shape `legPatch k s (run s patch)` from its
held store (compared on canonical op bytes; `encodeOp` is injective). -/
def compactable (held : CellId → Option (Cell deployedR)) (leg : Leg deployedR) : Bool :=
  match heldStore held leg with
  | none => false
  | some s =>
    leg.patch.map (encodeOp leg.kind) ==
      (bridge.codec.legPatch leg.kind s (Patch.run s leg.patch)).map (encodeOp leg.kind)

/-- The persisted leg: tag 0 + compact form, or tag 1 + `encodeLeg`. -/
def encodeLegAt (held : CellId → Option (Cell deployedR)) (leg : Leg deployedR) : List UInt8 :=
  match heldStore held leg with
  | some s =>
    if compactable held leg then
      let s' := Patch.run s leg.patch
      [0] ++ StreamCodec.nat.encode leg.cell ++ [CanonicalCellRegistry.Kind.tag leg.kind] ++
        digestStream.encode (cellRoot (some ⟨leg.kind, s⟩)) ++
        (StreamCodec.list bytesStream).encode
          ((changesOf (bridge.codec.cover leg.kind s s') s s').map (changeBytes leg.kind))
    else [1] ++ encodeLeg leg
  | none => [1] ++ encodeLeg leg

/-- Decode a persisted leg against the held cells; a digest mismatch is `none`. -/
def decodeLegAt (held : CellId → Option (Cell deployedR)) : List UInt8 → Option (Leg deployedR)
  | 0 :: bytes => do
    let (cell, b1) ← StreamCodec.nat.decodePrefix bytes
    match b1 with
    | [] => none
    | tag :: b2 =>
      let k ← CanonicalCellRegistry.kindAtTag tag
      let (digest, b3) ← digestStream.decodePrefix b2
      let raw ← full (StreamCodec.list bytesStream) b3
      let changes ← raw.mapM (decodeChange k)
      let s ← (held cell).bind fun c => c.storeAt k
      if cellRoot (some ⟨k, s⟩) = digest then
        some ⟨cell, k, bridge.codec.legPatch k s (applyChanges s changes)⟩
      else none
  | 1 :: bytes => full legStream bytes
  | _ => none

theorem mapM_decodeChange (k : deployedR.Kind) (cs : List (Change (deployedR.layout k))) :
    (cs.map (changeBytes k)).mapM (decodeChange k) = some cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih => simp [List.mapM_cons, decodeChange_changeBytes, ih]

theorem encodeOps_injective (k : deployedR.Kind) {p q : Patch (deployedR.layout k)}
    (h : p.map (encodeOp k) = q.map (encodeOp k)) : p = q := by
  have hp := decodeOps_encode k p
  have hq := decodeOps_encode k q
  rw [h] at hp
  rw [hp] at hq
  exact Option.some.inj hq

set_option backward.isDefEq.respectTransparency false in
theorem decodeLegAt_encodeLegAt (held : CellId → Option (Cell deployedR)) (leg : Leg deployedR) :
    decodeLegAt held (encodeLegAt held leg) = some leg := by
  have verbatim : decodeLegAt held ([1] ++ encodeLeg leg) = some leg := by
    simp only [List.singleton_append, decodeLegAt]
    exact (legStream_encode leg) ▸ full_encode legStream leg
  unfold encodeLegAt
  cases hs : heldStore held leg with
  | none => exact verbatim
  | some s =>
    dsimp only
    by_cases hc : compactable held leg = true
    · rw [if_pos hc]
      obtain ⟨cell, k, patch⟩ := leg
      have hpatch : patch = bridge.codec.legPatch k s (Patch.run s patch) := by
        unfold compactable at hc
        rw [hs] at hc
        exact encodeOps_injective k (by simpa using hc)
      have hheld : ((held cell).bind fun c => c.storeAt k) = some s := hs
      simp only [List.singleton_append, List.append_assoc, decodeLegAt,
        StreamCodec.decodePrefix_encode, List.cons_append, List.nil_append,
        CanonicalCellRegistry.kindAtTag_tag, full_encode, mapM_decodeChange, hheld]
      cases hcell : held cell with
      | none => simp [hcell] at hheld
      | some c =>
        simp only [hcell, Option.bind_some] at hheld
        simp only [bind, Option.bind, CanonicalCellRegistry.kindAtTag_tag,
          StreamCodec.decodePrefix_encode, full_encode, mapM_decodeChange, hcell, hheld]
        rw [applyChanges_changesOf (bridge.codec.cover_nodup k s _)
          (fun a h => bridge.codec.mem_cover a h)]
        simp only [↓reduceIte]
        rw [← hpatch]
    · rw [if_neg hc]
      exact verbatim

set_option backward.isDefEq.respectTransparency false in
/-- **A digest guard is a guard, up to one exhibited collision.**  If a
persisted leg, decoded against DIFFERENT held cells, yields a leg other than
the one written, then the operation itself exhibits two DIFFERENT canonical
cell byte strings of the leg's kind with the same `rootBytes`: a collision of
the deployed per-cell root (cSHAKE256), on two concrete inputs, not a
disjunct over an infinite type. -/
theorem decodeLegAt_other (held held' : CellId → Option (Cell deployedR)) (leg leg' : Leg deployedR)
    (decoded : decodeLegAt held' (encodeLegAt held leg) = some leg') (other : leg' ≠ leg) :
    ∃ s s' : Store (deployedR.layout leg.kind),
      encodeCell (some ⟨leg.kind, s⟩) ≠ encodeCell (some ⟨leg.kind, s'⟩) ∧
      ResourceBirthCodec.rootBytes (encodeCell (some ⟨leg.kind, s⟩)) =
        ResourceBirthCodec.rootBytes (encodeCell (some ⟨leg.kind, s'⟩)) := by
  have verbatim : decodeLegAt held' ([1] ++ encodeLeg leg) = some leg := by
    simp only [List.singleton_append, decodeLegAt]
    exact (legStream_encode leg) ▸ full_encode legStream leg
  unfold encodeLegAt at decoded
  cases hs : heldStore held leg with
  | none =>
    rw [hs] at decoded
    exact absurd (Option.some.inj (verbatim.symm.trans decoded)).symm other
  | some s =>
    rw [hs] at decoded
    dsimp only at decoded
    by_cases hc : compactable held leg = true
    · rw [if_pos hc] at decoded
      obtain ⟨cell, k, patch⟩ := leg
      have hpatch : patch = bridge.codec.legPatch k s (Patch.run s patch) := by
        unfold compactable at hc
        rw [hs] at hc
        exact encodeOps_injective k (by simpa using hc)
      simp only [List.singleton_append, List.append_assoc, decodeLegAt,
        StreamCodec.decodePrefix_encode, List.cons_append, List.nil_append] at decoded
      simp only [bind, Option.bind, CanonicalCellRegistry.kindAtTag_tag,
        StreamCodec.decodePrefix_encode, full_encode, mapM_decodeChange] at decoded
      cases hcell : held' cell with
      | none => simp [hcell] at decoded
      | some c =>
        cases hst : c.storeAt k with
        | none => simp [hcell, hst] at decoded
        | some s' =>
          simp only [hcell, hst] at decoded
          by_cases hd : cellRoot (some ⟨k, s'⟩) = cellRoot (some ⟨k, s⟩)
          · simp only [hd, ↓reduceIte, Option.some.injEq] at decoded
            by_cases es : s' = s
            · subst es
              rw [applyChanges_changesOf (bridge.codec.cover_nodup k s' _)
                (fun a h => bridge.codec.mem_cover a h)] at decoded
              exact absurd (by rw [← decoded, ← hpatch]) other
            · refine ⟨s, s', fun same => es ?_, hd.symm⟩
              have h1 := bridge_decode_total_on_registry (some ⟨k, s⟩)
              have h2 := bridge_decode_total_on_registry (some ⟨k, s'⟩)
              rw [same, h2] at h1
              have := Option.some.inj (Option.some.inj h1)
              exact eq_of_heq (Cell.mk.inj this).2
          · simp [hd] at decoded
    · rw [if_neg hc] at decoded
      exact absurd (Option.some.inj (verbatim.symm.trans decoded)).symm other

/-! ## The persisted turn -/

/-- Held cells after a list of creates over a world. -/
def heldOf (w : World deployedR TransactionId Digest)
    (creates : List (CellId × Cell deployedR × Option CellId)) (c : CellId) :
    Option (Cell deployedR) :=
  match creates.find? (fun x => x.1 == c) with
  | some x => some x.2.1
  | none => w.cells c

/-- **The persisted turn**: `encodeTurn`'s layout, with each leg persisted by
`encodeLegAt` against the cells it runs from. -/
def encodeTurnAt (w : World deployedR TransactionId Digest) (t : DTurn deployedR Digest) :
    List UInt8 :=
  (StreamCodec.product (StreamCodec.list StreamCodec.nat) (StreamCodec.list bytesStream)).encode
    (t.absent,
      [digestStream.encode t.txId,
       (StreamCodec.list bytesStream).encode (t.creates.map createBytes),
       (StreamCodec.list bytesStream).encode (t.legs.map (encodeLegAt (heldOf w t.creates))),
       (StreamCodec.list StreamCodec.nat).encode t.retires,
       DurableReceiverCodec.eventStream.encode t.event,
       (StreamCodec.list digestStream).encode t.nullifiers,
       DurableReceiverCodec.chargeStream.encode t.charge,
       (StreamCodec.option DurableReceiverCodec.subjectStream).encode t.subject,
       StreamCodec.nat.encode t.keyEpoch,
       (StreamCodec.option digestStream).encode t.capability,
       StreamCodec.nat.encode t.notBefore,
       (StreamCodec.option StreamCodec.nat).encode t.validUntil,
       (StreamCodec.list (StreamCodec.product StreamCodec.nat digestStream)).encode t.pins,
       DurableReceiverCodec.chargeStream.encode t.credit])

/-- Decode a persisted turn against the follower's world. -/
def decodeTurnAt (w : World deployedR TransactionId Digest) (bytes : List UInt8) :
    Option (DTurn deployedR Digest) := do
  let (absent, fields) ← full (StreamCodec.product (StreamCodec.list StreamCodec.nat)
    (StreamCodec.list bytesStream)) bytes
  match fields with
  | [fTx, fCreates, fLegs, fRetires, fEvent, fNull, fCharge, fSubject, fEpoch, fCap,
      fBefore, fUntil, fPins, fCredit] =>
    let txId ← full digestStream fTx
    let createsRaw ← full (StreamCodec.list bytesStream) fCreates
    let creates ← createsRaw.mapM decodeCreate
    let legsRaw ← full (StreamCodec.list bytesStream) fLegs
    let legs ← legsRaw.mapM (decodeLegAt (heldOf w creates))
    let retires ← full (StreamCodec.list StreamCodec.nat) fRetires
    let event ← full DurableReceiverCodec.eventStream fEvent
    let nullifiers ← full (StreamCodec.list digestStream) fNull
    let charge ← full DurableReceiverCodec.chargeStream fCharge
    let subject ← full (StreamCodec.option DurableReceiverCodec.subjectStream) fSubject
    let keyEpoch ← full StreamCodec.nat fEpoch
    let capability ← full (StreamCodec.option digestStream) fCap
    let notBefore ← full StreamCodec.nat fBefore
    let validUntil ← full (StreamCodec.option StreamCodec.nat) fUntil
    let pins ← full (StreamCodec.list (StreamCodec.product StreamCodec.nat digestStream)) fPins
    let credit ← full DurableReceiverCodec.chargeStream fCredit
    some { txId, creates, legs, retires, event, nullifiers, charge, subject, keyEpoch,
           capability, notBefore, validUntil, absent, pins, credit }
  | _ => none

theorem mapM_decodeLegAt (held : CellId → Option (Cell deployedR)) (legs : List (Leg deployedR)) :
    (legs.map (encodeLegAt held)).mapM (decodeLegAt held) = some legs := by
  induction legs with
  | nil => rfl
  | cons leg rest ih => simp [List.mapM_cons, decodeLegAt_encodeLegAt, ih]

/-- **`decodeTurnAt_encodeTurnAt`**: against the world it was written at, the
persisted turn decodes to exactly the turn. -/
theorem decodeTurnAt_encodeTurnAt (w : World deployedR TransactionId Digest)
    (t : DTurn deployedR Digest) : decodeTurnAt w (encodeTurnAt w t) = some t := by
  have hc : (t.creates.map createBytes).mapM decodeCreate = some t.creates :=
    mapM_decodeCreate t.creates
  unfold decodeTurnAt encodeTurnAt
  rw [full_encode]
  simp only [bind, Option.bind, full_encode, hc, mapM_decodeLegAt]

/-! ## The log-entry decoder: bounded, refusing by name (HP-1) -/

/-- Why a persisted entry is not a turn. -/
inductive EntryRefusal where
  /-- The entry, or the turn it decodes to, is past a static bound (`Kernel.Bounds`). -/
  | overBound (name : Bounds.Name) (value limit : Nat)
  /-- The bytes do not decode against this world. -/
  | undecodable
  deriving DecidableEq, Repr

def EntryRefusal.ofBound : Bounds.Refusal → EntryRefusal
  | .overBound name value limit => .overBound name value limit

/-- The cells a turn touches: its creates, legs, retires and absence pins. -/
def touched (t : DTurn deployedR Digest) : Nat :=
  t.creates.length + t.legs.length + t.retires.length + t.absent.length

/-- The bounds a decoded turn is held to. -/
def turnBounds (t : DTurn deployedR Digest) : List (Bounds.Name × Nat) :=
  [(.legsPerTurn, t.legs.length), (.nullifiersPerTurn, t.nullifiers.length),
    (.cellsTouched, touched t)]

/-- Whether the writer's entry for `t` at `w` is within every bound. -/
def entryWithinBounds (w : World deployedR TransactionId Digest) (t : DTurn deployedR Digest) : Bool :=
  decide ((encodeTurnAt w t).length ≤ Bounds.turnBytesMax) &&
    (turnBounds t).all fun p => decide (p.2 ≤ p.1.limit)

/-- **The log-entry decoder.** An entry past `turnBytesMax` is refused by that
name before a byte of it is decoded; a turn past `legsPerTurnMax`,
`nullifiersPerTurnMax` or `cellsTouchedMax` is refused whole. A refusal returns
no part of a turn. -/
def decodeEntry (w : World deployedR TransactionId Digest) (bytes : List UInt8) :
    Except EntryRefusal (DTurn deployedR Digest) := do
  (Bounds.check .turnBytes bytes.length).mapError EntryRefusal.ofBound
  let some t := decodeTurnAt w bytes | throw .undecodable
  (Bounds.checkAll (turnBounds t)).mapError EntryRefusal.ofBound
  return t

/-- An entry one byte (or more) past `turnBytesMax` is refused by that name. -/
theorem decodeEntry_overBytes (w : World deployedR TransactionId Digest) {bytes : List UInt8}
    (past : Bounds.turnBytesMax < bytes.length) :
    decodeEntry w bytes = .error (.overBound .turnBytes bytes.length Bounds.turnBytesMax) := by
  have h : Bounds.check .turnBytes bytes.length =
      .error (.overBound .turnBytes bytes.length Bounds.turnBytesMax) :=
    Bounds.check_refuses (name := .turnBytes) past
  simp [decodeEntry, h, Except.mapError, EntryRefusal.ofBound, bind, Except.bind]

/-- **`withinBounds_accepts` at the decoder (no false refusal)**: the writer's
entry for a turn within every bound decodes, against the world it was written at,
to exactly that turn. -/
theorem decodeEntry_encodeTurnAt (w : World deployedR TransactionId Digest)
    (t : DTurn deployedR Digest) (within : entryWithinBounds w t = true) :
    decodeEntry w (encodeTurnAt w t) = .ok t := by
  simp only [entryWithinBounds, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at within
  obtain ⟨bytes, counts⟩ := within
  have hb := Bounds.check_accepts (name := .turnBytes) bytes
  have hc := Bounds.withinBounds_accepts (turnBounds t) counts
  simp [decodeEntry, hb, hc, decodeTurnAt_encodeTurnAt, Except.mapError, bind, Except.bind, pure,
    Except.pure]

/-- An accepted entry is a decoded turn within every bound (the check is not vacuous). -/
theorem decodeEntry_ok {w : World deployedR TransactionId Digest} {bytes : List UInt8}
    {t : DTurn deployedR Digest} (h : decodeEntry w bytes = .ok t) :
    decodeTurnAt w bytes = some t ∧ bytes.length ≤ Bounds.turnBytesMax ∧
      ∀ p ∈ turnBounds t, p.2 ≤ p.1.limit := by
  by_cases hb : bytes.length ≤ Bounds.turnBytesMax
  · unfold decodeEntry at h
    rw [Bounds.check_accepts (name := .turnBytes) hb] at h
    cases hd : decodeTurnAt w bytes with
    | none => simp [hd, Except.mapError, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    | some t' =>
      cases hc : Bounds.checkAll (turnBounds t') with
      | error r => simp [hd, hc, Except.mapError, bind, Except.bind] at h
      | ok u =>
        simp [hd, hc, Except.mapError, bind, Except.bind, pure, Except.pure] at h
        subst h
        exact ⟨rfl, hb, Bounds.checkAll_ok _ (by cases u; exact hc)⟩
  · rw [decodeEntry_overBytes w (Nat.lt_of_not_le hb)] at h
    cases h

#assert_axioms decodeEntry_overBytes decodeEntry_encodeTurnAt decodeEntry_ok

#assert_axioms applyChanges_changesOf
#assert_axioms decodeLegAt_encodeLegAt
#assert_axioms decodeTurnAt_encodeTurnAt
#assert_axioms decodeLegAt_other

end Minidregg.Kernel.DeployedTurnCompact
