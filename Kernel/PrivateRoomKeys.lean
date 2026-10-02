/-
# Kernel.PrivateRoomKeys -- the `keys` cell of a private room (PRIVACY §3.1, row 7)

A private room `R` keeps its room key `k_R^e` off the node: each member's client
holds it, and the node holds only WRAPS -- `k_R^e` encrypted to one member's
X25519 key (`native/resource-client/src/roomkey.rs`). The wraps live in one
content cell born `--in R`, the room's `keys` cell: one atom per
`(epoch, member)`, at atom id `epoch * 2^64 + member`, whose payload is the
member's public encryption key and the wrap. The kernel cannot read a wrap and
checks nothing about one. What it does check is this cell's law, `keysLaw`:

* only the founder writes the cell (`keysLaw_refuses_nonfounder_write`) -- a
  member cannot hand itself, or anyone, a key, and cannot replace a wrap;
* every write only creates atoms: no edit (`keysLaw_refuses_edit`), no
  tombstone (`keysLaw_refuses_tombstone`), no document, link, run, annotation
  or quote (`keysLaw_refuses_non_atom`). The set of wraps only grows, so the
  room's epoch (the largest epoch with a wrap) never goes backwards and a wrap,
  once written, is the wrap: a second write at the same `(epoch, member)` is
  the same atom id, which the content controller refuses;
* reads, delegation, law installs and revocations are left to capabilities
  (`keysLaw_admits_reads`): who may read the wraps is who may observe under R.

Every member may read every wrap. That is the cheaper choice and it is the
deployed one: per-address observation is not on this tree (PRIVACY row 10,
K-FIELDS-OBSERVE), and a wrap is useless without its member's X25519 secret --
its key-encryption key is cSHAKE256 of the X25519 shared secret, the room, the
epoch, the member, the ephemeral key and the member's public key, so it opens
for exactly one secret. That last sentence is a cryptographic assumption
(X25519 + XChaCha20-Poly1305), stated, not proved here.

What this file does NOT prove, and why. `no_wrap_for_kicked` (a kicked member
gets no wrap at the next epoch) is a client invariant: the kernel cannot know
what a wrap is for. `future_unreadable` is IND-CPA of the primitives. Both are
said in PRIVACY §3.1; neither is dressed as a theorem.

The deployed law is the JSON template
`deploy/shell/templates/room/private/law.keys.json` (the client installs that
file, with `@FOUNDER` replaced, through `include_str!`). The Host parses it to
the `Pred` below; this file states what that `Pred` decides.
-/
import Kernel.StreamResource

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

/-- The law a private room's `keys` cell is born with. -/
def keysLaw (founder : SubjectId) : Minidregg.Pred.Pred :=
  Minidregg.Pred.Pred.any
    [.memberOf "request/verb" readTags,
     Minidregg.Pred.Pred.all
       [.eq "request/subject" (Int.ofNat founder.value),
        .eq "content/atom-edits" 0,
        .eq "content/tombstones" 0,
        .eqSlots "content/operations" "content/atom-creates"]]

/-- A write by anyone but the founder is refused: no member writes a wrap. -/
theorem keysLaw_refuses_nonfounder_write (founder : SubjectId) (old new : Minidregg.Pred.State)
    (verb : Int) (writes : new.get "request/verb" = some verb) (isWrite : verb ∉ readTags)
    (other : new.get "request/subject" ≠ some (Int.ofNat founder.value)) :
    Minidregg.Pred.eval (keysLaw founder) old new = false := by
  simp [keysLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith_any, Minidregg.Pred.evalWith_all,
    Minidregg.Pred.evalWith, writes]
  exact ⟨isWrite, fun self => absurd self other⟩

/-- Even the founder may not edit an atom: a wrap, once written, stays. -/
theorem keysLaw_refuses_edit (founder : SubjectId) (old new : Minidregg.Pred.State)
    (verb : Int) (writes : new.get "request/verb" = some verb) (isWrite : verb ∉ readTags)
    (edits : new.get "content/atom-edits" ≠ some 0) :
    Minidregg.Pred.eval (keysLaw founder) old new = false := by
  simp [keysLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith_any, Minidregg.Pred.evalWith_all,
    Minidregg.Pred.evalWith, writes, edits]
  exact isWrite

/-- Nor tombstone one: the set of wraps, and so the room's epoch, only grows. -/
theorem keysLaw_refuses_tombstone (founder : SubjectId) (old new : Minidregg.Pred.State)
    (verb : Int) (writes : new.get "request/verb" = some verb) (isWrite : verb ∉ readTags)
    (tombstones : new.get "content/tombstones" ≠ some 0) :
    Minidregg.Pred.eval (keysLaw founder) old new = false := by
  simp [keysLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith_any, Minidregg.Pred.evalWith_all,
    Minidregg.Pred.evalWith, writes, tombstones]
  exact isWrite

/-- A write carrying any action other than an atom creation is refused. -/
theorem keysLaw_refuses_non_atom (founder : SubjectId) (old new : Minidregg.Pred.State)
    (verb : Int) (writes : new.get "request/verb" = some verb) (isWrite : verb ∉ readTags)
    (operations creates : Int) (ops : new.get "content/operations" = some operations)
    (atoms : new.get "content/atom-creates" = some creates) (other : operations ≠ creates) :
    Minidregg.Pred.eval (keysLaw founder) old new = false := by
  simp [keysLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith_any, Minidregg.Pred.evalWith_all,
    Minidregg.Pred.evalWith, writes, ops, atoms, other]
  exact isWrite

/-- The founder's write that only creates atoms is admitted. -/
theorem keysLaw_admits_founder_wraps (founder : SubjectId) (old new : Minidregg.Pred.State)
    (self : new.get "request/subject" = some (Int.ofNat founder.value))
    (noEdit : new.get "content/atom-edits" = some 0)
    (noTombstone : new.get "content/tombstones" = some 0)
    (count : Int) (ops : new.get "content/operations" = some count)
    (atoms : new.get "content/atom-creates" = some count) :
    Minidregg.Pred.eval (keysLaw founder) old new = true := by
  simp [keysLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith_any, Minidregg.Pred.evalWith_all,
    Minidregg.Pred.evalWith, self, noEdit, noTombstone, ops, atoms]

/-- Reads, delegations, law installs and revocations pass: capabilities decide them. -/
theorem keysLaw_admits_reads (founder : SubjectId) (old new : Minidregg.Pred.State)
    (verb : Int) (reads : new.get "request/verb" = some verb) (isRead : verb ∈ readTags) :
    Minidregg.Pred.eval (keysLaw founder) old new = true := by
  simp [keysLaw, Minidregg.Pred.eval, Minidregg.Pred.evalWith_any, Minidregg.Pred.evalWith,
    reads]
  exact Or.inl isRead

/-! ## Both poles on concrete projections (the premises are satisfiable) -/

/-- A member (subject 12) writing one wrap atom into founder 7's keys cell. -/
def memberWrap : Minidregg.Pred.State :=
  ⟨[("request/verb", 2), ("request/subject", 12), ("content/operations", 1),
    ("content/atom-creates", 1), ("content/atom-edits", 0), ("content/tombstones", 0)]⟩

/-- The founder writing two wrap atoms (a rotation for two remaining members). -/
def founderRotation : Minidregg.Pred.State :=
  ⟨[("request/verb", 2), ("request/subject", 7), ("content/operations", 2),
    ("content/atom-creates", 2), ("content/atom-edits", 0), ("content/tombstones", 0)]⟩

/-- The founder tombstoning a wrap (an edit with `tombstone := true`). -/
def founderTombstone : Minidregg.Pred.State :=
  ⟨[("request/verb", 2), ("request/subject", 7), ("content/operations", 1),
    ("content/atom-creates", 0), ("content/atom-edits", 1), ("content/tombstones", 1)]⟩

/-- A member reading the keys cell. -/
def memberRead : Minidregg.Pred.State :=
  ⟨[("request/verb", 1), ("request/subject", 12)]⟩

theorem member_wrap_refused : Minidregg.Pred.eval (keysLaw ⟨7⟩) memberWrap memberWrap = false := by
  decide

theorem founder_rotation_admitted :
    Minidregg.Pred.eval (keysLaw ⟨7⟩) founderRotation founderRotation = true := by
  decide

theorem founder_tombstone_refused :
    Minidregg.Pred.eval (keysLaw ⟨7⟩) founderTombstone founderTombstone = false := by
  decide

theorem member_read_admitted : Minidregg.Pred.eval (keysLaw ⟨7⟩) memberRead memberRead = true := by
  decide

end Minidregg.Kernel.PrivateRoomKeys

/-! ## Axiom pins -/

open Minidregg.Kernel.PrivateRoomKeys

/-- info: 'Minidregg.Kernel.PrivateRoomKeys.readTags_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms readTags_eq
/-- info: 'Minidregg.Kernel.PrivateRoomKeys.keysLaw_refuses_nonfounder_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keysLaw_refuses_nonfounder_write
/-- info: 'Minidregg.Kernel.PrivateRoomKeys.keysLaw_refuses_edit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keysLaw_refuses_edit
/-- info: 'Minidregg.Kernel.PrivateRoomKeys.keysLaw_refuses_tombstone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keysLaw_refuses_tombstone
/-- info: 'Minidregg.Kernel.PrivateRoomKeys.keysLaw_refuses_non_atom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keysLaw_refuses_non_atom
/-- info: 'Minidregg.Kernel.PrivateRoomKeys.keysLaw_admits_founder_wraps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keysLaw_admits_founder_wraps
/-- info: 'Minidregg.Kernel.PrivateRoomKeys.keysLaw_admits_reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keysLaw_admits_reads
/-- info: 'Minidregg.Kernel.PrivateRoomKeys.member_wrap_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms member_wrap_refused
/-- info: 'Minidregg.Kernel.PrivateRoomKeys.founder_rotation_admitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms founder_rotation_admitted
/-- info: 'Minidregg.Kernel.PrivateRoomKeys.founder_tombstone_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms founder_tombstone_refused
/-- info: 'Minidregg.Kernel.PrivateRoomKeys.member_read_admitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms member_read_admitted
