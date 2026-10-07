/-
KN2-STORE-OPEN planted faults against the pinned history API. EVERY definition
below must FAIL to elaborate; `check-planted-api-faults.sh` requires one error
per numbered fault (and fails if any of them elaborates).
-/
import Compiler.DurableHistoryReader

open Minidregg.Compiler
open Minidregg.Compiler.DurableHistoryReader
open Minidregg.Compiler.DurableHistory (Head Refusal StoreIdentity)
open Minidregg.Theory.TypedAuthorization (Digest)

-- FAULT-1 (unverified absence): a reader answering "not accepted" with no opening.
def fault1 {store : StoreIdentity} (head : Head store) (t : Digest) : IO (Except Refusal (TxAnswer head t)) :=
  pure (.ok .absent)

-- FAULT-2 (forged frontier): a head built outside the open, or a head with its frontier replaced.
def fault2a (store : StoreIdentity) : Head store :=
  Head.mk 5 ⟨0⟩ [] ⟨0⟩ ⟨0⟩ (Or.inl sorry)
def fault2b {store : StoreIdentity} (head : Head store) : Head store := { head with frontier := [] }

-- FAULT-3 (bare state): stateAt answering a snapshot with no authenticity.
def fault3 {rootBytes : List UInt8 → Digest} (seed : Minidregg.Kernel.DurableReceiver.Seed)
    {store : StoreIdentity} (head : Head store) (h : Nat)
    (snapshot : Minidregg.Kernel.DurableDataIntent.DataSnapshot rootBytes) :
    IO (Except Refusal (StateAt rootBytes seed head h)) :=
  pure (.ok snapshot)

-- FAULT-4 (hand-built footprint): a verified footprint whose answer carries no opening.
def fault4 {store : StoreIdentity} (head : Head store) (t : Digest) : VerifiedFootprint head ⟨[t], []⟩ :=
  ⟨[⟨t, .absent⟩], rfl, [], rfl⟩

-- FAULT-5 (another Store's head): a head of Store `other` where the opened Store's is expected.
def fault5 (opened other : StoreIdentity) (head : Head other) : Head opened :=
  head

-- FAULT-6 (forged identity): a Store identity built outside the open.
def fault6 (key : DurableCheckpointCodec.MacKey) : StoreIdentity :=
  StoreIdentity.mk key ⟨0⟩
