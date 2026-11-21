/-
# Kernel.JournalIndex -- the journal sequences of the deployed Store

Which sequences an accepted record belongs to (`sequences`), read from the record alone: its
retained signed ingress. The Store's index keeps, for each sequence, its length and the height
of each member (`Compiler.DurableIndex`, families 3 and 4; `Theory.JournalSequences`), written
by the append that accepts the record, re-derived by the open and by `store audit`. Served
reads open those rows; none walks the log.

Sequences today (both of the fleet surface):

* `fleetPayer payer`: the accepted fleet turns paid by an account, in journal order (the
  agent head, op 101: its newest turn and how many there are).
* `fleetIncoming account topic`: the accepted fleet turns whose transfer pays `account` and
  which published on `topic`; the empty topic lists every turn that pays the account (the
  incoming ledger, op 180).

A sequence id is 32 octets: cSHAKE256 under the index key customization over a kind byte and
the canonical bytes of what names it. Two different names share an id only on a cSHAKE256
collision; the exactness statements name that case (`Collides`).
-/
module

public import Kernel.FleetTurnCodec
public import Compiler.DurableIndex

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

namespace Minidregg.Kernel.JournalIndex

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableReceiver (IntentRecord)

set_option autoImplicit false

/-- What names a sequence. -/
inductive Name where
  | fleetPayer (payer : Nat)
  | fleetIncoming (account : Nat) (topic : List UInt8)
  deriving DecidableEq, Repr

/-- A name's canonical bytes: a kind byte, then its fields. -/
def Name.bytes : Name → List UInt8
  | .fleetPayer payer => 0 :: StreamCodec.nat.encode payer
  | .fleetIncoming account topic =>
      1 :: (StreamCodec.product StreamCodec.nat bytesStream).encode (account, topic)

/-- The sequence id of a name (the primary of its index rows). -/
def Name.id (name : Name) : Digest256 :=
  DurableIndex.primaryOf DurableIndex.Family.seqCount name.bytes

/-- The sequences an accepted fleet turn belongs to: its payer's; and, when it pays an
account, that account's ledger of every payment and of the payments on the topic it
published on. -/
def fleetNames (command : FleetTurn.Command) : List Name :=
  .fleetPayer command.payer ::
    match command.transfer with
    | none => []
    | some transfer =>
        .fleetIncoming transfer.destination [] ::
          match command.publication with
          | none => []
          | some publication =>
              if publication.topic.isEmpty then [] else [.fleetIncoming transfer.destination publication.topic]

/-- The names of the sequences a record belongs to: a fleet turn's, none otherwise. -/
def names (record : IntentRecord) : List Name :=
  match FleetTurn.decodeIngress record.event.canonicalBytes with
  | some ingress => fleetNames ingress.command
  | none => []

/-- **The deployed derivation**: the sequence ids of a record, as the index writes them. -/
def sequences (record : IntentRecord) : List Digest256 :=
  (names record).map Name.id

/-- Two different names of one log share a sequence id (a cSHAKE256 collision under the index
key customization): the one case in which a sequence lists a record that does not carry its
name. -/
def Collides (name : Name) (log : List IntentRecord) : Prop :=
  ∃ record ∈ log, ∃ other ∈ names record, other ≠ name ∧ other.id = name.id

/-- Without a collision, a record is in a name's sequence exactly when it carries the name. -/
theorem mem_sequences_iff {name : Name} {log : List IntentRecord} (clean : ¬ Collides name log)
    {record : IntentRecord} (inLog : record ∈ log) : name.id ∈ sequences record ↔ name ∈ names record := by
  constructor
  · intro member
    obtain ⟨other, carried, same⟩ := List.mem_map.mp member
    by_cases equal : other = name
    · exact equal ▸ carried
    · exact absurd ⟨record, inLog, other, carried, equal, same⟩ clean
  · intro carried
    exact List.mem_map.mpr ⟨name, carried, rfl⟩

end Minidregg.Kernel.JournalIndex
