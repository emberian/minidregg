/-
# Kernel.PrivateRoomKeys -- the `keys` cell of a private room (PRIVACY §3.1, row 7)

A private room `R` keeps its room key `k_R^e` off the node: each member's client
holds it, and the node holds only WRAPS -- `k_R^e` encrypted to one member's
X25519 key (`native/resource-client/src/roomkey.rs`). The wraps live in one
content cell born `--in R`, the room's `keys` cell, partitioned by atom id:

* a WRAP of epoch `e` for member `m`, addressed to the member's encryption key
  of generation `g`, is the atom `wrapAtomId e g m = (e + 1)·2^96 + g·2^64 + m`
  (high half `≥ 2^32`); its payload is that public key, the wrap, and the
  founder-signed epoch certificate and delivery;
* the RELEASE record of that wrap, written by the founder one turn EARLIER, is
  the atom `((2^30 + 1 + e) << 96) | g << 64 | m`: a founder-signed commitment to
  the wrap's exact bytes (the client writes the wrap only after reading this
  record back unchanged);
* member `m`'s ENCRYPTION-KEY RECORD is the atom `m` itself (high half `0`); its
  payload is the member's current key epoch and X25519 public key.  The member
  creates it and later edits it, after each signing-key rotation
  (`mini rotate-key` publishes it to every private room the member is in).

The generation `g` is the key epoch of the record a wrap was addressed to (`0`
for a key given at invite time, before any record).  So a member who rotated
can be RE-WRAPPED at an epoch it already holds a wrap at: the re-wrap is a
fresh atom id.  A second wrap to the SAME key is the same id, which the content
controller refuses (`second_wrap_same_generation_refused`).

The kernel cannot read a wrap and checks nothing about one. What it does check
is this cell's law, `keysLaw`, over the write's projection (the request, the
action counts, and the range of the high and low 64-bit halves of the atom ids
the write creates or edits, `ContentResource.project`):

* only the founder writes wraps (`keysLaw_refuses_nonfounder_wrap`), only by
  creating atoms: no wrap edit (`keysLaw_refuses_wrap_edit`), no tombstone
  (`keysLaw_refuses_tombstone`), nothing but atoms (`keysLaw_refuses_non_atom`);
  release records fall in the same founder-only region; so the set of wraps
  and releases only grows;
* each subject writes only ITS OWN encryption-key record: one action, creating
  or editing the atom whose id is the writer's subject number
  (`keysLaw_admits_own_record`, `keysLaw_refuses_foreign_record`); the founder
  cannot write a member's record either;
* reads, delegation, law installs and revocations are left to capabilities
  (`keysLaw_admits_reads`): who may read the wraps is who may observe under R.

What the law does NOT decide, and who does.  Which epoch is current, that a
wrap is the founder's, that a re-wrap is addressed to the member's CURRENT
record, and that the record's key really is the member's: the law sees ids,
never payloads.  The clients decide, from out-of-band PINS: every certificate,
wrap and release must verify under the founder key each client pinned, the
certificates form one chain whose head each client retains and never lets go
backwards, and the founder wraps only to a record that verifies under the
signing key it pinned from the member's own declaration
(`docs/PRIVATE-ROOMS-DESIGN.txt`). The member's client opens the wrap
whose public key matches a secret in its keyring.  The client protocol's
outcome is stated as a model below (`rotation_preserves_room_access`, with
its poles): a theorem of the model, not of the Rust.

Every member may read every wrap and every record. That is the cheaper choice
and it is the deployed one: per-address observation is not on this tree (PRIVACY
row 10, K-FIELDS-OBSERVE), and a wrap is useless without its member's X25519
secret -- its key-encryption key is cSHAKE256 of the X25519 shared secret, the
room, the epoch, the member, the ephemeral key and the member's public key, so
it opens for exactly one secret. That last sentence is a cryptographic
assumption (X25519 + XChaCha20-Poly1305), stated, not proved here.

`no_wrap_for_kicked` (a kicked member gets no wrap at the next epoch) is a
client invariant; `future_unreadable` is IND-CPA of the primitives. Both are
said in PRIVACY §3.1; neither is dressed as a theorem.

The deployed law is the JSON template
`deploy/shell/templates/room/private/law.keys.json` (the client installs that
file, with `@FOUNDER` replaced, through `include_str!`). The Host parses it to
the `Pred` below; this file states what that `Pred` decides.
-/
import Kernel.StreamResource
import Kernel.ContentResource
import Theory.AssertAxioms

namespace Minidregg.Kernel.PrivateRoomKeys

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- The request-verb codes that never write a cell: observe, delegate, install
a law, revoke (`CredentialAuthorityEntryCodec.verbTag`). -/
def readTags : List Int :=
  [Int.ofNat (CredentialAuthorityEntryCodec.verbTag Verb.observeObject),
   Int.ofNat (CredentialAuthorityEntryCodec.verbTag Verb.delegateObject),
   Int.ofNat (CredentialAuthorityEntryCodec.verbTag Verb.installPolicy),
   Int.ofNat (CredentialAuthorityEntryCodec.verbTag Verb.revokeCapability)]

theorem readTags_eq : readTags = [1, 3, 4, 5] := rfl

/-! ## Atom identifiers -/

/-- The wrap of epoch `epoch` for `member`, addressed to its key of generation `gen`. -/
def wrapAtomId (epoch gen member : Nat) : Nat := (epoch + 1) * 2 ^ 96 + gen * 2 ^ 64 + member

/-- Member `member`'s encryption-key record. -/
def recordAtomId (member : Nat) : Nat := member

theorem wrapAtomId_halves (epoch gen member : Nat)
    (memberBound : member < 2 ^ 64) :
    ContentResource.atomHigh (wrapAtomId epoch gen member) = (epoch + 1) * 2 ^ 32 + gen ∧
      ContentResource.atomLow (wrapAtomId epoch gen member) = member := by
  unfold ContentResource.atomHigh ContentResource.atomLow wrapAtomId
  constructor
  · rw [show (epoch + 1) * 2 ^ 96 + gen * 2 ^ 64 + member =
        member + 2 ^ 64 * ((epoch + 1) * 2 ^ 32 + gen) by ring]
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt memberBound, zero_add]
  · rw [show (epoch + 1) * 2 ^ 96 + gen * 2 ^ 64 + member =
        member + 2 ^ 64 * ((epoch + 1) * 2 ^ 32 + gen) by ring]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt memberBound]

/-- A wrap is never in the record region: its high half is at least `2^32`. -/
theorem wrapAtomId_high_ne_zero (epoch gen member : Nat)
    (memberBound : member < 2 ^ 64) :
    ContentResource.atomHigh (wrapAtomId epoch gen member) ≠ 0 := by
  rw [(wrapAtomId_halves epoch gen member memberBound).1]
  positivity

/-- A record is in the record region, at its member's subject number. -/
theorem recordAtomId_halves (member : Nat) (memberBound : member < 2 ^ 64) :
    ContentResource.atomHigh (recordAtomId member) = 0 ∧
      ContentResource.atomLow (recordAtomId member) = member := by
  unfold ContentResource.atomHigh ContentResource.atomLow recordAtomId
  exact ⟨Nat.div_eq_of_lt memberBound, Nat.mod_eq_of_lt memberBound⟩

/-- One wrap per `(epoch, generation, member)`, and a re-wrap at a new
generation is a different atom. -/
theorem wrapAtomId_injective {epoch gen member epoch' gen' member' : Nat}
    (genBound : gen < 2 ^ 32) (memberBound : member < 2 ^ 64)
    (genBound' : gen' < 2 ^ 32) (memberBound' : member' < 2 ^ 64)
    (same : wrapAtomId epoch gen member = wrapAtomId epoch' gen' member') :
    epoch = epoch' ∧ gen = gen' ∧ member = member' := by
  have h := wrapAtomId_halves epoch gen member memberBound
  have h' := wrapAtomId_halves epoch' gen' member' memberBound'
  rw [same] at h
  have lows : member = member' := h.2.symm.trans h'.2
  have highs : (epoch + 1) * 2 ^ 32 + gen = (epoch' + 1) * 2 ^ 32 + gen' := h.1.symm.trans h'.1
  have word : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  rw [word] at highs genBound genBound'
  exact ⟨by omega, by omega, lows⟩

/-- **A second wrap to the same key is refused.**  The same `(epoch,
generation, member)` is the same atom id, and the content controller refuses
to allocate a present atom (`duplicateAddress`) before any law runs. -/
theorem second_wrap_same_generation_refused (progress : ContentResource.Progress)
    (epoch gen member : Nat) (value : Hyperdocument.AtomRecord)
    (present : progress.1 ⟨.atoms, ⟨⟨wrapAtomId epoch gen member⟩⟩⟩ ≠ none) :
    ContentResource.allocate progress .atoms ⟨⟨wrapAtomId epoch gen member⟩⟩ value =
      .error .duplicateAddress := by
  simp [ContentResource.allocate, present]

/-! ## The law -/

/-- The law a private room's `keys` cell is born with. -/
def keysLaw (founder : SubjectId) : Minidregg.Pred.Pred :=
  Minidregg.Pred.Pred.any
    [.memberOf "request/verb" readTags,
     -- the founder writes wraps: creates only, every touched id above the record region
     Minidregg.Pred.Pred.all
       [.eq "request/subject" (Int.ofNat founder.value),
        .eq "content/atom-edits" 0,
        .eq "content/tombstones" 0,
        .eqSlots "content/operations" "content/atom-creates",
        .not (.eq "content/atoms/high-min" 0)],
     -- a subject writes its own encryption-key record: one create or edit, at its own number
     Minidregg.Pred.Pred.all
       [.eq "content/operations" 1,
        .eq "content/tombstones" 0,
        .eq "content/atoms/high-max" 0,
        .eqSlots "content/atoms/low-min" "request/subject",
        .eqSlots "content/atoms/low-max" "request/subject"]]

/-- A write by anyone but the founder that touches the wrap region is refused:
no member writes a wrap. -/
theorem keysLaw_refuses_nonfounder_wrap (founder : SubjectId) (old new : Minidregg.Pred.State)
    (verb : Int) (writes : new.get "request/verb" = some verb) (isWrite : verb ∉ readTags)
    (other : new.get "request/subject" ≠ some (Int.ofNat founder.value))
    (wrapRegion : new.get "content/atoms/high-max" ≠ some 0) :
    Minidregg.Pred.eval (keysLaw founder) old new = false := by
  simp [keysLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith_any, Minidregg.Pred.evalWith_all,
    Minidregg.Pred.evalWith, writes, wrapRegion]
  exact ⟨isWrite, fun self => absurd self other⟩

/-- Nobody -- the founder included -- writes another subject's encryption-key
record: a write touching the record region at an id that is not the writer's
own subject number is refused. -/
theorem keysLaw_refuses_foreign_record (founder : SubjectId) (old new : Minidregg.Pred.State)
    (verb : Int) (writes : new.get "request/verb" = some verb) (isWrite : verb ∉ readTags)
    (subject : Int) (signer : new.get "request/subject" = some subject)
    (recordRegion : new.get "content/atoms/high-min" = some 0)
    (foreign : new.get "content/atoms/low-min" ≠ some subject) :
    Minidregg.Pred.eval (keysLaw founder) old new = false := by
  simp [keysLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith_any, Minidregg.Pred.evalWith_all,
    Minidregg.Pred.evalWith, writes, recordRegion, signer]
  refine ⟨isWrite, ?_⟩
  intro _ _ _
  cases low : new.get "content/atoms/low-min" with
  | none => simp
  | some value =>
      have : value ≠ subject := fun same => foreign (by rw [low, same])
      simp [this]

/-- No wrap is ever edited: an edit touching the wrap region is refused. -/
theorem keysLaw_refuses_wrap_edit (founder : SubjectId) (old new : Minidregg.Pred.State)
    (verb : Int) (writes : new.get "request/verb" = some verb) (isWrite : verb ∉ readTags)
    (edits : new.get "content/atom-edits" ≠ some 0)
    (wrapRegion : new.get "content/atoms/high-max" ≠ some 0) :
    Minidregg.Pred.eval (keysLaw founder) old new = false := by
  simp [keysLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith_any, Minidregg.Pred.evalWith_all,
    Minidregg.Pred.evalWith, writes, edits, wrapRegion]
  exact isWrite

/-- Nor tombstoned, wrap or record: the set of wraps, and so the room's epoch, only grows. -/
theorem keysLaw_refuses_tombstone (founder : SubjectId) (old new : Minidregg.Pred.State)
    (verb : Int) (writes : new.get "request/verb" = some verb) (isWrite : verb ∉ readTags)
    (tombstones : new.get "content/tombstones" ≠ some 0) :
    Minidregg.Pred.eval (keysLaw founder) old new = false := by
  simp [keysLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith_any, Minidregg.Pred.evalWith_all,
    Minidregg.Pred.evalWith, writes, tombstones]
  exact isWrite

/-- Outside a subject's own record, a write carrying any action other than an
atom creation is refused. -/
theorem keysLaw_refuses_non_atom (founder : SubjectId) (old new : Minidregg.Pred.State)
    (verb : Int) (writes : new.get "request/verb" = some verb) (isWrite : verb ∉ readTags)
    (operations creates : Int) (ops : new.get "content/operations" = some operations)
    (atoms : new.get "content/atom-creates" = some creates) (other : operations ≠ creates)
    (notRecord : new.get "content/atoms/high-max" ≠ some 0) :
    Minidregg.Pred.eval (keysLaw founder) old new = false := by
  simp [keysLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith_any, Minidregg.Pred.evalWith_all,
    Minidregg.Pred.evalWith, writes, ops, atoms, other, notRecord]
  exact isWrite

/-- The founder's write that only creates wrap-region atoms is admitted. -/
theorem keysLaw_admits_founder_wraps (founder : SubjectId) (old new : Minidregg.Pred.State)
    (self : new.get "request/subject" = some (Int.ofNat founder.value))
    (noEdit : new.get "content/atom-edits" = some 0)
    (noTombstone : new.get "content/tombstones" = some 0)
    (count : Int) (ops : new.get "content/operations" = some count)
    (atoms : new.get "content/atom-creates" = some count)
    (high : Int) (lowest : new.get "content/atoms/high-min" = some high) (wrapRegion : high ≠ 0) :
    Minidregg.Pred.eval (keysLaw founder) old new = true := by
  simp [keysLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith_any, Minidregg.Pred.evalWith_all,
    Minidregg.Pred.evalWith, self, noEdit, noTombstone, ops, atoms, lowest, wrapRegion]

/-- A subject's one-action write of its own record (create or edit) is admitted. -/
theorem keysLaw_admits_own_record (founder : SubjectId) (old new : Minidregg.Pred.State)
    (subject : Int) (signer : new.get "request/subject" = some subject)
    (one : new.get "content/operations" = some 1)
    (noTombstone : new.get "content/tombstones" = some 0)
    (recordRegion : new.get "content/atoms/high-max" = some 0)
    (lowest : new.get "content/atoms/low-min" = some subject)
    (highest : new.get "content/atoms/low-max" = some subject) :
    Minidregg.Pred.eval (keysLaw founder) old new = true := by
  simp [keysLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith_any, Minidregg.Pred.evalWith_all,
    Minidregg.Pred.evalWith, signer, one, noTombstone, recordRegion, lowest, highest]

/-- Reads, delegations, law installs and revocations pass: capabilities decide them. -/
theorem keysLaw_admits_reads (founder : SubjectId) (old new : Minidregg.Pred.State)
    (verb : Int) (reads : new.get "request/verb" = some verb) (isRead : verb ∈ readTags) :
    Minidregg.Pred.eval (keysLaw founder) old new = true := by
  simp [keysLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith_any, Minidregg.Pred.evalWith,
    reads]
  exact Or.inl isRead

/-! ## Both poles on concrete projections (the premises are satisfiable)

Founder 7, member 12.  A wrap at epoch 1, generation 2, for member 12 has high
half `2·2^32 + 2 = 8589934594`; a record has high half 0. -/

def wrapHigh : Int := 8589934594

/-- A member (subject 12) writing one wrap atom into founder 7's keys cell. -/
def memberWrap : Minidregg.Pred.State :=
  ⟨[("request/verb", 2), ("request/subject", 12), ("content/operations", 1),
    ("content/atom-creates", 1), ("content/atom-edits", 0), ("content/tombstones", 0),
    ("content/atoms/high-min", wrapHigh), ("content/atoms/high-max", wrapHigh),
    ("content/atoms/low-min", 12), ("content/atoms/low-max", 12)]⟩

/-- The founder writing two wrap atoms (a rotation for two remaining members). -/
def founderRotation : Minidregg.Pred.State :=
  ⟨[("request/verb", 2), ("request/subject", 7), ("content/operations", 2),
    ("content/atom-creates", 2), ("content/atom-edits", 0), ("content/tombstones", 0),
    ("content/atoms/high-min", wrapHigh), ("content/atoms/high-max", wrapHigh),
    ("content/atoms/low-min", 7), ("content/atoms/low-max", 12)]⟩

/-- The founder RE-WRAPPING epoch 1 for member 12, who rotated: generation 3,
a fresh atom beside the generation-2 wrap. -/
def founderRewrap : Minidregg.Pred.State :=
  ⟨[("request/verb", 2), ("request/subject", 7), ("content/operations", 1),
    ("content/atom-creates", 1), ("content/atom-edits", 0), ("content/tombstones", 0),
    ("content/atoms/high-min", wrapHigh + 1), ("content/atoms/high-max", wrapHigh + 1),
    ("content/atoms/low-min", 12), ("content/atoms/low-max", 12)]⟩

/-- The founder tombstoning a wrap (an edit with `tombstone := true`). -/
def founderTombstone : Minidregg.Pred.State :=
  ⟨[("request/verb", 2), ("request/subject", 7), ("content/operations", 1),
    ("content/atom-creates", 0), ("content/atom-edits", 1), ("content/tombstones", 1),
    ("content/atoms/high-min", wrapHigh), ("content/atoms/high-max", wrapHigh),
    ("content/atoms/low-min", 12), ("content/atoms/low-max", 12)]⟩

/-- Member 12 creating its own encryption-key record. -/
def memberRecord : Minidregg.Pred.State :=
  ⟨[("request/verb", 2), ("request/subject", 12), ("content/operations", 1),
    ("content/atom-creates", 1), ("content/atom-edits", 0), ("content/tombstones", 0),
    ("content/atoms/high-min", 0), ("content/atoms/high-max", 0),
    ("content/atoms/low-min", 12), ("content/atoms/low-max", 12)]⟩

/-- Member 12 editing its own record after a rotation. -/
def memberRecordEdit : Minidregg.Pred.State :=
  ⟨[("request/verb", 2), ("request/subject", 12), ("content/operations", 1),
    ("content/atom-creates", 0), ("content/atom-edits", 1), ("content/tombstones", 0),
    ("content/atoms/high-min", 0), ("content/atoms/high-max", 0),
    ("content/atoms/low-min", 12), ("content/atoms/low-max", 12)]⟩

/-- Member 13 writing member 12's record. -/
def foreignRecord : Minidregg.Pred.State :=
  ⟨[("request/verb", 2), ("request/subject", 13), ("content/operations", 1),
    ("content/atom-creates", 1), ("content/atom-edits", 0), ("content/tombstones", 0),
    ("content/atoms/high-min", 0), ("content/atoms/high-max", 0),
    ("content/atoms/low-min", 12), ("content/atoms/low-max", 12)]⟩

/-- The founder writing member 12's record (squatting the key a wrap would go to). -/
def founderSquat : Minidregg.Pred.State :=
  ⟨[("request/verb", 2), ("request/subject", 7), ("content/operations", 1),
    ("content/atom-creates", 1), ("content/atom-edits", 0), ("content/tombstones", 0),
    ("content/atoms/high-min", 0), ("content/atoms/high-max", 0),
    ("content/atoms/low-min", 12), ("content/atoms/low-max", 12)]⟩

/-- A member reading the keys cell. -/
def memberRead : Minidregg.Pred.State :=
  ⟨[("request/verb", 1), ("request/subject", 12)]⟩

theorem member_wrap_refused : Minidregg.Pred.eval (keysLaw ⟨7⟩) memberWrap memberWrap = false := by
  decide

theorem founder_rotation_admitted :
    Minidregg.Pred.eval (keysLaw ⟨7⟩) founderRotation founderRotation = true := by
  decide

theorem founder_rewrap_admitted :
    Minidregg.Pred.eval (keysLaw ⟨7⟩) founderRewrap founderRewrap = true := by
  decide

theorem founder_tombstone_refused :
    Minidregg.Pred.eval (keysLaw ⟨7⟩) founderTombstone founderTombstone = false := by
  decide

theorem member_record_admitted :
    Minidregg.Pred.eval (keysLaw ⟨7⟩) memberRecord memberRecord = true := by
  decide

theorem member_record_edit_admitted :
    Minidregg.Pred.eval (keysLaw ⟨7⟩) memberRecordEdit memberRecordEdit = true := by
  decide

theorem foreign_record_refused :
    Minidregg.Pred.eval (keysLaw ⟨7⟩) foreignRecord foreignRecord = false := by
  decide

theorem founder_squat_refused :
    Minidregg.Pred.eval (keysLaw ⟨7⟩) founderSquat founderSquat = false := by
  decide

theorem member_read_admitted : Minidregg.Pred.eval (keysLaw ⟨7⟩) memberRead memberRead = true := by
  decide

/-! ## The projection carries the partition

The law's region tests read `ContentResource.project`'s `content/atoms/...`
slots.  A write creating one wrap lands above the record region; a write
creating one record lands in it at the writer's number. -/

theorem project_wrap_high (before after : ContentResource.ContentStore) (epoch gen member : Nat)
    (kind : Hyperdocument.AtomKind) (payload : List UInt8)
    (memberBound : member < 2 ^ 64) :
    ("content/atoms/high-min", Int.ofNat ((epoch + 1) * 2 ^ 32 + gen)) ∈
      ContentResource.project before after
        ⟨[.createAtom ⟨⟨wrapAtomId epoch gen member⟩⟩ kind payload]⟩ := by
  have halves := wrapAtomId_halves epoch gen member memberBound
  have lowest : ContentResource.touchedMin ContentResource.atomHigh
      ⟨[.createAtom ⟨⟨wrapAtomId epoch gen member⟩⟩ kind payload]⟩ =
        Int.ofNat ((epoch + 1) * 2 ^ 32 + gen) := by
    simp [ContentResource.touchedMin, ContentResource.touchedAtoms, halves.1]
  rw [← lowest]
  simp [ContentResource.project]

theorem project_record_region (before after : ContentResource.ContentStore) (member : Nat)
    (kind : Hyperdocument.AtomKind) (payload : List UInt8) (memberBound : member < 2 ^ 64) :
    ("content/atoms/high-max", (0 : Int)) ∈ ContentResource.project before after
        ⟨[.createAtom ⟨⟨recordAtomId member⟩⟩ kind payload]⟩ ∧
      ("content/atoms/low-min", Int.ofNat member) ∈ ContentResource.project before after
        ⟨[.createAtom ⟨⟨recordAtomId member⟩⟩ kind payload]⟩ := by
  have halves := recordAtomId_halves member memberBound
  have highest : ContentResource.touchedMax ContentResource.atomHigh
      ⟨[.createAtom ⟨⟨recordAtomId member⟩⟩ kind payload]⟩ = 0 := by
    simp [ContentResource.touchedMax, ContentResource.touchedAtoms, halves.1]
  have lowest : ContentResource.touchedMin ContentResource.atomLow
      ⟨[.createAtom ⟨⟨recordAtomId member⟩⟩ kind payload]⟩ = Int.ofNat member := by
    simp [ContentResource.touchedMin, ContentResource.touchedAtoms, halves.2]
  constructor
  · rw [← highest]; simp [ContentResource.project]
  · rw [← lowest]; simp [ContentResource.project]

/-! ## A member's signing-key rotation, in the client protocol (a model)

The member's X25519 key is derived from its signing seed, so a signing-key
rotation changes it.  The client protocol that keeps the member in its rooms:

1. `rotate-key` keeps the OLD encryption secret in the member's KEYRING before
   the seed is overwritten (`ring' = new :: ring`), and publishes the new
   public key as the member's record in every private room (`register`);
2. the founder's next room rotation wraps the new epoch to each kept member's
   RECORDED key (`rewrap`), not to the key stored beside the member's last wrap;
3. the member opens a wrap with whichever keyring secret it is addressed to
   (`opens`).

`pub` is X25519 scalar multiplication; `opens` says a wrap opens for exactly
the secrets whose public half it is addressed to -- the cryptographic
assumption of the module doc, taken here as the definition.  These are
theorems of this model of the Rust client (`roomkey.rs`, `key_rotation.rs`),
not of the Rust. -/

namespace Rotation

structure Wrap where
  epoch : Nat
  member : Nat
  gen : Nat
  encPub : Nat
  deriving DecidableEq, Repr

/-- `member` opens `epoch` with keyring `ring`: some wrap for it at that epoch
is addressed to the public half of a secret in the ring. -/
def opens (pub : Nat → Nat) (ring : List Nat) (wraps : List Wrap) (member epoch : Nat) : Bool :=
  wraps.any fun w => w.epoch == epoch && w.member == member && ring.any fun s => pub s == w.encPub

/-- The member's record after it rotates to key epoch `keyEpoch` with public key `encPub`. -/
def register (registry : Nat → Nat × Nat) (member keyEpoch encPub : Nat) : Nat → Nat × Nat :=
  fun m => if m = member then (keyEpoch, encPub) else registry m

/-- The founder's rotation to `epoch + 1`: one wrap per kept member, to its record. -/
def rewrap (registry : Nat → Nat × Nat) (epoch : Nat) (members : List Nat) : List Wrap :=
  members.map fun m => ⟨epoch + 1, m, (registry m).1, (registry m).2⟩

/-- **A signing-key rotation preserves room access.**  After the member
rotates (its keyring gains the new secret and keeps the old; its record names
the new public key) and the founder's next rotation wraps to the record, the
member opens the new epoch, and every epoch it could open before it still
opens. -/
theorem rotation_preserves_room_access (pub : Nat → Nat) (ring : List Nat) (new : Nat)
    (wraps : List Wrap) (registry : Nat → Nat × Nat) (member epoch keyEpoch : Nat)
    (members : List Nat) (kept : member ∈ members) (past : List Nat)
    (opened : ∀ e ∈ past, opens pub ring wraps member e = true) :
    opens pub (new :: ring)
        (wraps ++ rewrap (register registry member keyEpoch (pub new)) epoch members)
        member (epoch + 1) = true ∧
      ∀ e ∈ past, opens pub (new :: ring)
        (wraps ++ rewrap (register registry member keyEpoch (pub new)) epoch members)
        member e = true := by
  constructor
  · simp only [opens, List.any_append, Bool.or_eq_true, List.any_eq_true]
    right
    refine ⟨⟨epoch + 1, member, keyEpoch, pub new⟩, ?_, ?_⟩
    · simp only [rewrap, List.mem_map]
      exact ⟨member, kept, by simp [register]⟩
    · simp
  · intro e member_e
    have before := opened e member_e
    simp only [opens, List.any_append, Bool.or_eq_true, List.any_eq_true] at before ⊢
    left
    obtain ⟨w, inWraps, holds⟩ := before
    refine ⟨w, inWraps, ?_⟩
    simp only [Bool.and_eq_true, List.any_cons, Bool.or_eq_true] at holds ⊢
    exact ⟨holds.1, Or.inr holds.2⟩

/-- **Pole: without the keyring, a rotation loses the past.**  A member whose
seed was overwritten holds only the new secret; an epoch wrapped to it only
under the old public key no longer opens.  (The audit's finding, half one.) -/
theorem rotation_without_keyring_loses_past (pub : Nat → Nat) (old new : Nat)
    (distinct : pub old ≠ pub new) (wraps : List Wrap) (member e : Nat)
    (onlyOld : ∀ w ∈ wraps, w.epoch = e → w.member = member → w.encPub = pub old) :
    opens pub [new] wraps member e = false := by
  simp only [opens, List.any_eq_false, List.any_cons, List.any_nil, Bool.or_false,
    Bool.and_eq_true, beq_iff_eq, not_and]
  intro w inWraps both addressed
  exact distinct ((onlyOld w inWraps both.1 both.2).symm.trans addressed.symm)

/-- **Pole: a re-wrap to the stale key locks the member out.**  If the founder
wraps the new epoch to the key stored beside the member's old wrap, and the
member holds only its new secret, the new epoch does not open.  (The audit's
finding, half two: why the founder wraps to the RECORD.) -/
theorem stale_rewrap_locks_out (pub : Nat → Nat) (old new : Nat) (distinct : pub old ≠ pub new)
    (registry : Nat → Nat × Nat) (member epoch : Nat) (members : List Nat)
    (stale : (registry member).2 = pub old) (wraps : List Wrap)
    (noneAhead : ∀ w ∈ wraps, w.epoch ≤ epoch) :
    opens pub [new] (wraps ++ rewrap registry epoch members) member (epoch + 1) = false := by
  simp only [opens, List.any_append, Bool.or_eq_false_iff, List.any_eq_false, List.any_cons,
    List.any_nil, Bool.or_false, Bool.and_eq_true, beq_iff_eq, not_and]
  constructor
  · intro w inWraps sameEpoch
    have := noneAhead w inWraps
    omega
  · intro w inRewrap both addressed
    simp only [rewrap, List.mem_map] at inRewrap
    obtain ⟨m, _, rfl⟩ := inRewrap
    have sameMember := both.2
    simp only at sameMember addressed
    subst sameMember
    exact distinct (by rw [← stale]; exact addressed.symm)

/-- **Pole: the old secret does not open the new epoch.**  A thief holding the
member's OLD encryption secret (it had the daily key) gets nothing from a
rotation that wraps to the member's recorded new key. -/
theorem old_secret_cannot_open_next_epoch (pub : Nat → Nat) (old new : Nat)
    (distinct : pub old ≠ pub new) (registry : Nat → Nat × Nat) (member epoch keyEpoch : Nat)
    (members : List Nat) (wraps : List Wrap) (noneAhead : ∀ w ∈ wraps, w.epoch ≤ epoch) :
    opens pub [old] (wraps ++ rewrap (register registry member keyEpoch (pub new)) epoch members)
      member (epoch + 1) = false := by
  simp only [opens, List.any_append, Bool.or_eq_false_iff, List.any_eq_false, List.any_cons,
    List.any_nil, Bool.or_false, Bool.and_eq_true, beq_iff_eq, not_and]
  constructor
  · intro w inWraps sameEpoch
    have := noneAhead w inWraps
    omega
  · intro w inRewrap both addressed
    simp only [rewrap, List.mem_map] at inRewrap
    obtain ⟨m, _, rfl⟩ := inRewrap
    have sameMember := both.2
    simp only at sameMember addressed
    subst sameMember
    simp [register] at addressed
    exact distinct addressed

end Rotation

end Minidregg.Kernel.PrivateRoomKeys

/-! ## Axiom pins -/

open Minidregg.Kernel.PrivateRoomKeys

#assert_axioms readTags_eq
#assert_axioms wrapAtomId_halves
#assert_axioms wrapAtomId_high_ne_zero
#assert_axioms recordAtomId_halves
#assert_axioms wrapAtomId_injective
#assert_axioms second_wrap_same_generation_refused
#assert_axioms keysLaw_refuses_nonfounder_wrap
#assert_axioms keysLaw_refuses_foreign_record
#assert_axioms keysLaw_refuses_wrap_edit
#assert_axioms keysLaw_refuses_tombstone
#assert_axioms keysLaw_refuses_non_atom
#assert_axioms keysLaw_admits_founder_wraps
#assert_axioms keysLaw_admits_own_record
#assert_axioms keysLaw_admits_reads
#assert_axioms member_wrap_refused
#assert_axioms founder_rotation_admitted
#assert_axioms founder_rewrap_admitted
#assert_axioms founder_tombstone_refused
#assert_axioms member_record_admitted
#assert_axioms member_record_edit_admitted
#assert_axioms foreign_record_refused
#assert_axioms founder_squat_refused
#assert_axioms member_read_admitted
#assert_axioms project_wrap_high
#assert_axioms project_record_region
#assert_axioms Rotation.rotation_preserves_room_access
#assert_axioms Rotation.rotation_without_keyring_loses_past
#assert_axioms Rotation.stale_rewrap_locks_out
#assert_axioms Rotation.old_secret_cannot_open_next_epoch
