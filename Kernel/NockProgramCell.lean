/-
# Kernel.NockProgramCell — the program's sample, and the program cell's reads

`sampleOf` is NOCK §2.3's subject: the kernel, not the runner, builds the noun
a program is slammed with, from the command's projected participant slots and
the program's `Abi`. Layout (the one `nock-run --sample-json` builds, so a runner
and the kernel agree byte for byte):

    [[height caller room] ~[['target/0' id0] … ['target/n' idn] [key0 v0] … [keym vm]]]

The context triple is the ABI's to choose (v3, K-RUN-PIN): under `live` it is
the kernel's own (the admission height, the signer, the room), so a claim is good
for one height; under `pinned` it is `[0 0 0]`, so the sample is a function of the
named slots and the target ids alone (`sampleOf_pinned_of_fields`) and one claim
stays admissible for as long as those slots hold their values. The layout is the
same in both, so one program runs under either.

The target entries are the command's target cell ids in the signed target
order: two sheets given to one program yield different samples
(`sampleOf_targets_injective`), which the §2.3 draft could not tell apart. The
slot entries follow `Abi.sample` in order; a missing slot, or a negative value in
a `nat` slot, refuses (`none`) rather than defaulting — absence is not zero.

The reads (`checkProgram`, `showProgram`, `sampleFor`) are what host ops 131,
118, 119 serve. The WRITE is the ordinary resource birth (`storage: "nock"`).
-/
import Compiler.NockProgramCodec
import Compiler.CanonicalCellRegistry

namespace Minidregg.Kernel.NockProgramCell

open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.NockProgramCodec

set_option autoImplicit false

/-! ## The sample -/

/-- What the kernel knows about a run besides the observed values. `room` is an
atom (0 = no room), as `forge.hoon`'s `room=@` and the runner read it. -/
structure Context where
  height : Nat
  caller : Nat
  room : Nat
  deriving DecidableEq, Repr

/-- Hoon `@t`: UTF-8 bytes, least significant first. -/
def cordValue : List UInt8 → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * cordValue rest

def cord (s : String) : Noun := .atom (cordValue s.toUTF8.toList)

/-- A null-terminated Nock list. -/
def nockList : List Noun → Noun
  | [] => .atom 0
  | x :: rest => .cell x (nockList rest)

/-! ## Nouns as atoms (N11's state encoding; the `noun` slot type) -/

def natBytesAux : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else (n % 256).toUInt8 :: natBytesAux fuel (n / 256)

/-- Little-endian minimal bytes of an atom. -/
def natBytes (n : Nat) : List UInt8 := natBytesAux n n

/-- The jam of a noun as an atom (Urbit's `jam` is an atom). -/
def jamAtom (n : Noun) : Nat := cordValue (Noun.jam n)

/-- The noun whose jam is the atom `a`, refused unless re-jamming gives `a` back. -/
def ofJamAtom (a : Nat) : Option Noun :=
  match Noun.cue (natBytes a) with
  | some n => if jamAtom n = a then some n else none
  | none => none

theorem ofJamAtom_sound {a : Nat} {n : Noun} (h : ofJamAtom a = some n) : jamAtom n = a := by
  unfold ofJamAtom at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

/-- A bit stream that ends in a one. -/
def EndsTrue (bits : List Bool) : Prop := ∃ init, bits = init ++ [true]

theorem EndsTrue.cons {bits : List Bool} (b : Bool) (h : EndsTrue bits) : EndsTrue (b :: bits) := by
  obtain ⟨init, rfl⟩ := h; exact ⟨b :: init, rfl⟩

theorem EndsTrue.append_left {bits : List Bool} (pre : List Bool) (h : EndsTrue bits) :
    EndsTrue (pre ++ bits) := by
  obtain ⟨init, rfl⟩ := h; exact ⟨pre ++ init, by simp⟩

/-- The top bit of a positive atom's `bitLen` bits is a one. -/
theorem natBits_bitLen_endsTrue {n : Nat} (h : n ≠ 0) :
    EndsTrue (Noun.natBits (Noun.bitLen n) n) := by
  have pos := Noun.bitLen_pos h
  have lo := Noun.two_pow_bitLen_le h
  have hi := Noun.lt_two_pow_bitLen n
  obtain ⟨k, hk⟩ : ∃ k, Noun.bitLen n = k + 1 := ⟨Noun.bitLen n - 1, by omega⟩
  rw [hk] at lo hi ⊢
  simp only [Nat.add_sub_cancel] at lo
  have one : n / 2 ^ k = 1 := by
    have p : 0 < 2 ^ k := Nat.two_pow_pos k
    have a : 1 ≤ n / 2 ^ k := (Nat.le_div_iff_mul_le p).2 (by omega)
    have b : n / 2 ^ k < 2 := (Nat.div_lt_iff_lt_mul p).2 (by rw [Nat.pow_succ] at hi; omega)
    omega
  refine ⟨Noun.natBits k n, ?_⟩
  rw [Noun.natBits_add k 1 n, one]
  rfl

theorem mat_endsTrue (n : Nat) : EndsTrue (Noun.mat n) := by
  unfold Noun.mat
  split
  · exact ⟨[], rfl⟩
  · rename_i h
    have := (natBits_bitLen_endsTrue h).append_left
      (List.replicate (Noun.bitLen (Noun.bitLen n)) false ++
        true :: Noun.natBits (Noun.bitLen (Noun.bitLen n) - 1) (Noun.bitLen n))
    simpa [List.append_assoc] using this

/-- Every jam stream ends in a one: an atom's or a back-reference's `mat`, or a
cell's tail. -/
theorem jamAux_endsTrue : ∀ (n : Noun) (m : Noun.JamTable) (pos : Nat),
    EndsTrue (Noun.jamAux n m pos).1
  | .atom a, m, pos => by
    unfold Noun.jamAux
    split
    · split
      · exact (mat_endsTrue a).cons false
      · exact ((mat_endsTrue _).cons true).cons true
    · exact (mat_endsTrue a).cons false
  | .cell h t, m, pos => by
    unfold Noun.jamAux
    split
    · exact ((mat_endsTrue _).cons true).cons true
    · exact (((jamAux_endsTrue t _ _).append_left _).cons false).cons true

/-- A byte list whose last byte is not zero (vacuous for `[]`). -/
def LastNonzero (bytes : List UInt8) : Prop := ∀ init b, bytes = init ++ [b] → b ≠ 0

theorem toBytesAux_lastNonzero : ∀ (k : Nat) (bits : List Bool), EndsTrue bits →
    bits.length ≤ 8 * k → LastNonzero (Noun.toBytesAux k bits) ∧ Noun.toBytesAux k bits ≠ []
  | 0, bits, ends, len => by
    obtain ⟨init, rfl⟩ := ends; simp at len
  | k + 1, bits, ends, len => by
    have ne : bits ≠ [] := by obtain ⟨init, rfl⟩ := ends; simp
    have hlt : Noun.ofBits (bits.take 8) < 256 := by
      have := Noun.ofBits_lt (bits.take 8)
      have h8 : (bits.take 8).length ≤ 8 := by simp
      calc Noun.ofBits (bits.take 8) < 2 ^ (bits.take 8).length := this
        _ ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) h8
    simp only [Noun.toBytesAux, ne, if_false]
    refine ⟨?_, by simp⟩
    by_cases short : bits.length ≤ 8
    · have hd : bits.drop 8 = [] := List.drop_eq_nil_of_le short
      have tail : Noun.toBytesAux k [] = [] := by cases k <;> simp [Noun.toBytesAux]
      rw [hd, tail, List.take_of_length_le short]
      intro init b same
      have hb : b = (Noun.ofBits bits).toUInt8 := by
        cases init with
        | nil => simp at same; exact same.symm
        | cons x rest => simp at same
      subst hb
      obtain ⟨pre, rfl⟩ := ends
      have pos : 0 < Noun.ofBits (pre ++ [true]) := by
        rw [Noun.ofBits_append]; simp [Noun.ofBits, Nat.two_pow_pos]
      rw [List.take_of_length_le short] at hlt
      intro zero
      have := Noun.toUInt8_toNat_of_lt hlt
      rw [zero] at this
      simp at this; omega
    · have ends' : EndsTrue (bits.drop 8) := by
        obtain ⟨pre, rfl⟩ := ends
        refine ⟨pre.drop 8, ?_⟩
        rw [List.drop_append_of_le_length (by simp at short; omega)]
      obtain ⟨ih, ihne⟩ := toBytesAux_lastNonzero k (bits.drop 8) ends' (by simp; omega)
      intro init b same
      cases init with
      | nil => simp at same; exact absurd same.2 ihne
      | cons x rest =>
        simp only [List.cons_append, List.cons.injEq] at same
        exact ih rest b same.2

theorem jam_lastNonzero (n : Noun) : LastNonzero (Noun.jam n) :=
  (toBytesAux_lastNonzero (Noun.jamBits n).length (Noun.jamBits n) (jamAux_endsTrue n [] 0)
    (by omega)).1

theorem LastNonzero.tail {b : UInt8} {rest : List UInt8} (h : LastNonzero (b :: rest)) :
    LastNonzero rest := by
  intro init c same; exact h (b :: init) c (by simp [same])

theorem cordValue_pos : ∀ {bytes : List UInt8}, LastNonzero bytes → bytes ≠ [] →
    0 < cordValue bytes
  | [], _, ne => absurd rfl ne
  | b :: rest, h, _ => by
    simp only [cordValue]
    cases rest with
    | nil =>
      have : b ≠ 0 := h [] b rfl
      have : b.toNat ≠ 0 := fun z => this (UInt8.toNat_inj.mp (by simpa using z))
      simp [cordValue]; omega
    | cons c more =>
      have := cordValue_pos h.tail (by simp)
      omega

theorem length_le_cordValue : ∀ {bytes : List UInt8}, LastNonzero bytes →
    bytes.length ≤ cordValue bytes
  | [], _ => by simp [cordValue]
  | b :: rest, h => by
    simp only [cordValue, List.length_cons]
    cases rest with
    | nil =>
      have := cordValue_pos h (by simp)
      simpa [cordValue] using this
    | cons c more =>
      have ih := length_le_cordValue h.tail
      have pos := cordValue_pos h.tail (by simp)
      omega

theorem natBytesAux_cordValue : ∀ {bytes : List UInt8}, LastNonzero bytes →
    ∀ fuel, bytes.length ≤ fuel → natBytesAux fuel (cordValue bytes) = bytes
  | [], _, fuel, _ => by cases fuel <;> simp [natBytesAux, cordValue]
  | b :: rest, h, fuel + 1, len => by
    have pos := cordValue_pos h (by simp)
    have hb : b.toNat < 256 := b.toNat_lt
    have hmod : cordValue (b :: rest) % 256 = b.toNat := by
      simp only [cordValue]; omega
    have hdiv : cordValue (b :: rest) / 256 = cordValue rest := by
      simp only [cordValue]; omega
    simp only [natBytesAux, Nat.pos_iff_ne_zero.mp pos, if_false, hmod, hdiv,
      natBytesAux_cordValue h.tail fuel (by simp at len; omega)]
    simp

/-- **The jam atom reads back** (closes N11's open converse of
`ofJamAtom_sound`): every noun's jam atom decodes to that noun. So a noun stored
as its jam atom — a door's state, a `noun` output — is never refused when read. -/
theorem ofJamAtom_jamAtom (n : Noun) : ofJamAtom (jamAtom n) = some n := by
  have back : natBytes (jamAtom n) = Noun.jam n :=
    natBytesAux_cordValue (jam_lastNonzero n) _ (length_le_cordValue (jam_lastNonzero n))
  simp [ofJamAtom, back, Noun.cue_jam]

def encodeValue : SlotType → Int → Option Noun
  | .nat, .ofNat n => some (.atom n)
  | .nat, .negSucc _ => none
  | .int, z => some z.toNoun
  | .noun, .ofNat a => ofJamAtom a
  | .noun, .negSucc _ => none

def targetKey (i : Nat) : String := targetPrefix ++ toString i

/-- `['target/i' id]` for each command target, in command order. -/
def targetEntries : Nat → List Nat → List Noun
  | _, [] => []
  | i, id :: rest => .cell (cord (targetKey i)) (.atom id) :: targetEntries (i + 1) rest

/-- `[key value]` for each ABI sample slot, in ABI order. -/
def sampleSlots (read : Nat → String → Option Int) : List SampleSlot → Option (List Noun)
  | [] => some []
  | slot :: rest =>
    match read slot.target slot.slot with
    | none => none
    | some value =>
      match encodeValue slot.type value with
      | none => none
      | some noun => (sampleSlots read rest).map (.cell (cord slot.key) noun :: ·)

def contextNoun (ctx : Context) : Noun :=
  .cell (.atom ctx.height) (.cell (.atom ctx.caller) (.atom ctx.room))

/-- The context the sample carries: the kernel's own under `live`; the constants
`[0 0 0]` under `pinned` (K-RUN-PIN), whatever the height, signer or room. -/
def contextOf : ContextMode → Context → Context
  | .live, ctx => ctx
  | .pinned, _ => ⟨0, 0, 0⟩

/-- The sample. `targets` are the command's target cell ids in command order;
`read i slot` is the projected participant slot `slot` of target `i`. -/
def sampleOf (abi : Abi) (ctx : Context) (targets : List Nat)
    (read : Nat → String → Option Int) : Option Noun :=
  if abi.sample.all (fun slot => decide (slot.target < targets.length)) then
    (sampleSlots read abi.sample).map fun slots =>
      .cell (contextNoun (contextOf abi.context ctx)) (nockList (targetEntries 0 targets ++ slots))
  else none

theorem encodeValue_injective {type : SlotType} {a b : Int} {n : Noun}
    (ha : encodeValue type a = some n) (hb : encodeValue type b = some n) : a = b := by
  cases type with
  | nat =>
    cases a <;> cases b <;> simp [encodeValue] at ha hb
    subst ha; cases hb; rfl
  | int =>
    simp only [encodeValue, Option.some.injEq] at ha hb
    exact Noun.toNoun_injective (ha.trans hb.symm)
  | noun =>
    cases a <;> cases b <;> simp only [encodeValue, reduceCtorEq] at ha hb
    rw [← ofJamAtom_sound ha, ← ofJamAtom_sound hb]

theorem sampleSlots_cons {read : Nat → String → Option Int} {slot : SampleSlot}
    {rest : List SampleSlot} {nouns : List Noun}
    (h : sampleSlots read (slot :: rest) = some nouns) :
    ∃ v n tail, read slot.target slot.slot = some v ∧ encodeValue slot.type v = some n ∧
      sampleSlots read rest = some tail ∧ nouns = .cell (cord slot.key) n :: tail := by
  simp only [sampleSlots] at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · cases h
    · rename_i n hn
      cases hr : sampleSlots read rest with
      | none => rw [hr] at h; cases h
      | some tail =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq] at h
        exact ⟨v, n, tail, hv, hn, rfl, h.symm⟩

theorem sampleSlots_length {read : Nat → String → Option Int} :
    ∀ {slots : List SampleSlot} {nouns : List Noun},
      sampleSlots read slots = some nouns → nouns.length = slots.length
  | [], nouns, h => by simp [sampleSlots] at h; subst h; rfl
  | slot :: rest, nouns, h => by
    obtain ⟨_, _, tail, _, _, hr, rfl⟩ := sampleSlots_cons h
    simp [sampleSlots_length hr]

theorem sampleSlots_injective {read read' : Nat → String → Option Int} :
    ∀ {slots : List SampleSlot} {nouns : List Noun},
      sampleSlots read slots = some nouns → sampleSlots read' slots = some nouns →
        ∀ slot ∈ slots, read slot.target slot.slot = read' slot.target slot.slot
  | [], _, _, _ => by simp
  | slot :: rest, nouns, h, h' => by
    obtain ⟨v, n, tail, hv, he, hr, rfl⟩ := sampleSlots_cons h
    obtain ⟨v', n', tail', hv', he', hr', same⟩ := sampleSlots_cons h'
    simp only [List.cons.injEq, Noun.cell.injEq, true_and] at same
    obtain ⟨hn, ht⟩ := same
    subst hn
    subst ht
    have hvv : v = v' := encodeValue_injective he he'
    intro s member
    rcases List.mem_cons.mp member with head | tail
    · subst head; rw [hv, hv', hvv]
    · exact sampleSlots_injective hr hr' s tail

theorem nockList_injective : ∀ {a b : List Noun}, nockList a = nockList b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [nockList] at h
  | _ :: _, [], h => by simp [nockList] at h
  | x :: xs, y :: ys, h => by
    simp only [nockList, Noun.cell.injEq] at h
    rw [h.1, nockList_injective h.2]

theorem targetEntries_length : ∀ (i : Nat) (ids : List Nat),
    (targetEntries i ids).length = ids.length
  | _, [] => rfl
  | i, _ :: rest => by simp [targetEntries, targetEntries_length (i + 1) rest]

theorem targetEntries_injective : ∀ {i : Nat} {a b : List Nat},
    targetEntries i a = targetEntries i b → a = b
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => by simp [targetEntries] at h
  | _, _ :: _, [], h => by simp [targetEntries] at h
  | i, x :: xs, y :: ys, h => by
    simp only [targetEntries, List.cons.injEq, Noun.cell.injEq, Noun.atom.injEq, true_and] at h
    rw [h.1, targetEntries_injective h.2]

/-- **`sampleOf_injective`** (NOCK §3.3): one sample noun determines the
context it carries, the target ids, and every value the ABI reads. Distinct
targets or distinct slot values give distinct nouns. -/
theorem sampleOf_injective {abi : Abi} {ctx ctx' : Context} {targets targets' : List Nat}
    {read read' : Nat → String → Option Int} {n : Noun}
    (h : sampleOf abi ctx targets read = some n) (h' : sampleOf abi ctx' targets' read' = some n) :
    contextOf abi.context ctx = contextOf abi.context ctx' ∧ targets = targets' ∧
      ∀ slot ∈ abi.sample, read slot.target slot.slot = read' slot.target slot.slot := by
  unfold sampleOf at h h'
  split at h
  · split at h'
    · cases hs : sampleSlots read abi.sample with
      | none => rw [hs] at h; cases h
      | some slots =>
        cases hs' : sampleSlots read' abi.sample with
        | none => rw [hs'] at h'; cases h'
        | some slots' =>
          rw [hs] at h
          rw [hs'] at h'
          simp only [Option.map_some, Option.some.injEq] at h h'
          have same := h.trans h'.symm
          simp only [contextNoun, Noun.cell.injEq, Noun.atom.injEq] at same
          obtain ⟨⟨hh, hc, hr⟩, rest⟩ := same
          have lists := nockList_injective rest
          have lens : slots.length = slots'.length := by
            rw [sampleSlots_length hs, sampleSlots_length hs']
          obtain ⟨ht, hl⟩ := List.append_inj' lists lens
          subst hl
          refine ⟨?_, targetEntries_injective ht, sampleSlots_injective hs hs'⟩
          revert hh hc hr
          cases contextOf abi.context ctx; cases contextOf abi.context ctx'
          intro hh hc hr; simp_all
    · cases h'
  · cases h

/-- Under `live`, the sample determines the kernel's own context (height, signer,
room): K-RAN's statement, unchanged. -/
theorem sampleOf_injective_live {abi : Abi} {ctx ctx' : Context} {targets targets' : List Nat}
    {read read' : Nat → String → Option Int} {n : Noun} (live : abi.context = .live)
    (h : sampleOf abi ctx targets read = some n) (h' : sampleOf abi ctx' targets' read' = some n) :
    ctx = ctx' ∧ targets = targets' ∧
      ∀ slot ∈ abi.sample, read slot.target slot.slot = read' slot.target slot.slot := by
  have := sampleOf_injective h h'
  rw [live] at this
  exact this

theorem sampleOf_targets_injective {abi : Abi} {ctx : Context} {targets targets' : List Nat}
    {read read' : Nat → String → Option Int} {n : Noun}
    (h : sampleOf abi ctx targets read = some n) (h' : sampleOf abi ctx targets' read' = some n) :
    targets = targets' :=
  (sampleOf_injective h h').2.1

/-- **`sampleOf_deterministic`**: the sample is a function of the context, the
target ids and the values at the ABI's slots, and of nothing else a reader
could vary. -/
theorem sampleOf_deterministic (abi : Abi) (ctx : Context) (targets : List Nat)
    {read read' : Nat → String → Option Int}
    (agree : ∀ slot ∈ abi.sample, read slot.target slot.slot = read' slot.target slot.slot) :
    sampleOf abi ctx targets read = sampleOf abi ctx targets read' := by
  have slots : ∀ (list : List SampleSlot),
      (∀ slot ∈ list, read slot.target slot.slot = read' slot.target slot.slot) →
        sampleSlots read list = sampleSlots read' list := by
    intro list
    induction list with
    | nil => intro _; rfl
    | cons slot rest ih =>
      intro same
      simp only [sampleSlots, same slot (List.mem_cons_self ..),
        ih (fun s m => same s (List.mem_cons_of_mem _ m))]
  unfold sampleOf
  rw [slots abi.sample agree]

/-- **`sampleOf_pinned_of_fields`** (K-RUN-PIN): a pinned program's sample is
a function of the values at the ABI's named slots (and the command's target ids):
two states that agree on the named slots give the same sample at ANY two
contexts — any heights, any signers, any rooms. -/
theorem sampleOf_pinned_of_fields {abi : Abi} (pinned : abi.context = .pinned)
    (ctx ctx' : Context) (targets : List Nat) {read read' : Nat → String → Option Int}
    (agree : ∀ slot ∈ abi.sample, read slot.target slot.slot = read' slot.target slot.slot) :
    sampleOf abi ctx targets read = sampleOf abi ctx' targets read' := by
  rw [sampleOf_deterministic abi ctx targets agree]
  unfold sampleOf
  rw [pinned]
  rfl

/-- **`live_unchanged`** (K-RUN-PIN): a `live` program's sample is K-RAN's,
byte for byte — the kernel's context, the target entries, the ABI's slots. -/
theorem live_unchanged {abi : Abi} (live : abi.context = .live) (ctx : Context)
    (targets : List Nat) (read : Nat → String → Option Int) :
    sampleOf abi ctx targets read =
      if abi.sample.all (fun slot => decide (slot.target < targets.length)) then
        (sampleSlots read abi.sample).map fun slots =>
          .cell (.cell (.atom ctx.height) (.cell (.atom ctx.caller) (.atom ctx.room)))
            (nockList (targetEntries 0 targets ++ slots))
      else none := by
  unfold sampleOf
  rw [live]
  rfl

/-! ### Two states, decided

One ABI slot `n` reads field 2 of target 0. The two reads agree on field 2 and
differ on field 3, which the ABI does not name; the two contexts differ in
height and signer. Pinned: one sample. Live: two. -/

def twoStateAbi (context : ContextMode) : Abi :=
  { version := abiVersion, arm := 2, fuel := 100, libraries := [], context := context,
    sample := [{ target := 0, slot := "f/2", key := "n", type := .nat }], outputs := [] }

def stateA : Nat → String → Option Int := fun _ s => if s = "f/2" then some 41 else some 1
def stateB : Nat → String → Option Int := fun _ s => if s = "f/2" then some 41 else some 7

theorem pole_pinned_two_states :
    sampleOf (twoStateAbi .pinned) ⟨16, 7, 0⟩ [11] stateA =
      sampleOf (twoStateAbi .pinned) ⟨23, 9, 0⟩ [11] stateB := by decide +kernel

theorem pole_live_two_states :
    sampleOf (twoStateAbi .live) ⟨16, 7, 0⟩ [11] stateA ≠
      sampleOf (twoStateAbi .live) ⟨23, 9, 0⟩ [11] stateB := by decide +kernel

theorem sampleOf_absent_refused (abi : Abi) (ctx : Context) (targets : List Nat)
    (read : Nat → String → Option Int) (slot : SampleSlot) (named : slot ∈ abi.sample)
    (absent : read slot.target slot.slot = none) :
    sampleOf abi ctx targets read = none := by
  have none_of : ∀ (list : List SampleSlot), slot ∈ list → sampleSlots read list = none := by
    intro list
    induction list with
    | nil => intro m; cases m
    | cons head rest ih =>
      intro m
      simp only [sampleSlots]
      rcases List.mem_cons.mp m with same | later
      · subst same; simp [absent]
      · split
        · rfl
        · split
          · rfl
          · simp [ih later]
  unfold sampleOf
  split
  · simp [none_of abi.sample named]
  · rfl

theorem sampleOf_foreign_target_refused (abi : Abi) (ctx : Context) (targets : List Nat)
    (read : Nat → String → Option Int) (slot : SampleSlot) (named : slot ∈ abi.sample)
    (beyond : targets.length ≤ slot.target) :
    sampleOf abi ctx targets read = none := by
  unfold sampleOf
  have : abi.sample.all (fun slot => decide (slot.target < targets.length)) = false := by
    rw [List.all_eq_false]
    exact ⟨slot, named, by simp; omega⟩
  simp [this]

/-- The sample the kernel hands a runner is canonical jam bytes. -/
theorem sample_jam_canonical (n : Noun) : Noun.canonical (Noun.jam n) = true :=
  Noun.canonical_jam n

/-! ## Reads served to the client (ops 131–133) -/

/-- Op 131: what a birth of these bytes would meet, against the live store. -/
inductive CheckVerdict where
  | malformed
  | refused (reason : Refusal)
  | admissible (program : Program) (id : Digest) (code : Digest) (cellId : Nat) (present : Bool)

def checkProgram (domain : Digest) (directory : Directory Nat CanonicalCellRegistry.registry)
    (program : Program) : CheckVerdict :=
  match check program with
  | .error reason => .refused reason
  | .ok () =>
    if CanonicalCellRegistry.librariesPresent domain directory program then
      let id := programId program
      .admissible program id (codeDigest program.jam)
        (CanonicalCellRegistry.programCellId domain program)
        (CanonicalCellRegistry.loadProgram domain directory id).isSome
    else .refused .missingLibrary

/-- Op 133: the canonical sample jam for a stored program. `values` are
`(target index, slot, value)` triples; a duplicate `(index, slot)` refuses. -/
inductive SampleVerdict where
  | missingProgram
  | ambiguousValues
  | refused
  | sample (jam : List UInt8)

def readOf (values : List (Nat × String × Int)) (i : Nat) (slot : String) : Option Int :=
  (values.find? fun v => v.1 = i ∧ v.2.1 = slot).map fun v => v.2.2

def sampleFor (domain : Digest) (directory : Directory Nat CanonicalCellRegistry.registry)
    (id : Digest) (ctx : Context) (targets : List Nat) (values : List (Nat × String × Int)) :
    SampleVerdict :=
  match CanonicalCellRegistry.loadProgram domain directory id with
  | none => .missingProgram
  | some program =>
    if (values.map fun v => (v.1, v.2.1)).Nodup then
      match sampleOf program.abi ctx targets (readOf values) with
      | none => .refused
      | some noun => .sample (Noun.jam noun)
    else .ambiguousValues

end Minidregg.Kernel.NockProgramCell

/-- info: 'Minidregg.Kernel.NockProgramCell.sampleOf_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.sampleOf_injective
/-- info: 'Minidregg.Kernel.NockProgramCell.sampleOf_injective_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.sampleOf_injective_live
/-- info: 'Minidregg.Kernel.NockProgramCell.sampleOf_pinned_of_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.sampleOf_pinned_of_fields
/-- info: 'Minidregg.Kernel.NockProgramCell.live_unchanged' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.live_unchanged
/-- info: 'Minidregg.Kernel.NockProgramCell.pole_pinned_two_states' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.pole_pinned_two_states
/-- info: 'Minidregg.Kernel.NockProgramCell.pole_live_two_states' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.pole_live_two_states
/-- info: 'Minidregg.Kernel.NockProgramCell.ofJamAtom_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.ofJamAtom_sound
/-- info: 'Minidregg.Kernel.NockProgramCell.ofJamAtom_jamAtom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.ofJamAtom_jamAtom
/-- info: 'Minidregg.Kernel.NockProgramCell.sampleOf_targets_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.sampleOf_targets_injective
/-- info: 'Minidregg.Kernel.NockProgramCell.sampleOf_deterministic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.sampleOf_deterministic
/-- info: 'Minidregg.Kernel.NockProgramCell.sampleOf_absent_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.sampleOf_absent_refused
/-- info: 'Minidregg.Kernel.NockProgramCell.sampleOf_foreign_target_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.NockProgramCell.sampleOf_foreign_target_refused
