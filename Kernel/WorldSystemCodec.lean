/-
# Kernel.WorldSystemCodec -- the World's system cell as bytes (checkpoint = World v1)

ROOT 10-14: the checkpoint IS a World = {cells : CellTable (STATE-AT),
system (this module), rootTree (STORE-ROOT)} under one MAC and one tag.  The
system sub-codec carries ALL six namespaces of `sysLayout`, each load-bearing:
`journal` (replay/conflict classify, `journal_exact`), `head` (height and log
chain), `retired` (a retired id is never re-created), `parent` (K-ROOM rows),
`spent` (nullifiers), `allowance` (the meter; without it every charged turn
after a reopen is `overAllowance`).  It is `StoreCodec.payloadStream` over one
`Wire`, so the bytes are the canonical sorted entry list and the roundtrip is
the codec law (`systemStream.decodePrefix_encode`).
-/
import Kernel.World
import Kernel.DurableDataIntent
import Compiler.StoreCodec
import Theory.AssertAxioms

namespace Minidregg.Kernel.WorldSystemCodec

open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Theory.ResourceCost (Lane)
open Minidregg.Kernel.World
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.StoreCodec (Wire unitStream)
open Minidregg.Kernel.DurableDataIntent (TransactionId)

set_option autoImplicit false

/-- A one-byte tag codec for a finite enumeration. -/
def tagStream {α : Type} (tag : α → UInt8) (ofTag : UInt8 → Option α)
    (roundtrip : ∀ a, ofTag (tag a) = some a) : StreamCodec α where
  encode a := [tag a]
  decodePrefix
    | [] => none
    | b :: rest => (ofTag b).map fun a => (a, rest)
  decodePrefix_encode := by
    intro a suffix
    simp [roundtrip]

def spaceTag : SysSpace → UInt8
  | .journal => 0 | .head => 1 | .retired => 2 | .parent => 3 | .spent => 4 | .allowance => 5

def spaceOfTag : UInt8 → Option SysSpace
  | 0 => some .journal | 1 => some .head | 2 => some .retired | 3 => some .parent
  | 4 => some .spent | 5 => some .allowance | _ => none

theorem spaceOfTag_tag (s : SysSpace) : spaceOfTag (spaceTag s) = some s := by cases s <;> rfl

def laneTag : Lane → UInt8
  | .incidences => 0 | .turnBytes => 1 | .memoryTouches => 2 | .witnessBytes => 3
  | .proofWork => 4 | .storageBytes => 5 | .networkBytes => 6 | .sideEffectCount => 7
  | .feeDebit => 8 | .leaseByteBlocks => 9

def laneOfTag : UInt8 → Option Lane
  | 0 => some .incidences | 1 => some .turnBytes | 2 => some .memoryTouches
  | 3 => some .witnessBytes | 4 => some .proofWork | 5 => some .storageBytes
  | 6 => some .networkBytes | 7 => some .sideEffectCount | 8 => some .feeDebit
  | 9 => some .leaseByteBlocks | _ => none

theorem laneOfTag_tag (l : Lane) : laneOfTag (laneTag l) = some l := by cases l <;> rfl

def spaceStream : StreamCodec SysSpace := tagStream spaceTag spaceOfTag spaceOfTag_tag
def laneStream : StreamCodec Lane := tagStream laneTag laneOfTag laneOfTag_tag

/-- The deployed system layout. -/
abbrev DSys := sysLayout TransactionId Digest

def keyStream : (s : SysSpace) → StreamCodec (SysKey TransactionId Digest s)
  | .journal => digestStream
  | .head => unitStream
  | .retired => StreamCodec.nat
  | .parent => StreamCodec.nat
  | .spent => digestStream
  | .allowance => laneStream

def valueStream : (s : SysSpace) → StreamCodec (SysValue Digest s)
  | .journal => StreamCodec.product StreamCodec.nat digestStream
  | .head => StreamCodec.product StreamCodec.nat digestStream
  | .retired => unitStream
  | .parent => StreamCodec.nat
  | .spent => unitStream
  | .allowance => StreamCodec.nat

/-- The system cell's wire: all six namespaces. -/
def systemWire : Wire DSys where
  name := "dregg/world-system/v1"
  namespaces := [SysSpace.journal, .head, .retired, .parent, .spent, .allowance]
  namespaces_complete := by intro s; cases s <;> decide
  namespaceStream := spaceStream
  keyStream := keyStream
  valueStream := valueStream
  keyCodecId := fun (s : SysSpace) => match s with
    | .journal | .spent => "digest" | .head => "unit" | .retired | .parent => "cell-id/nat"
    | .allowance => "lane/u8"
  valueCodecId := fun (s : SysSpace) => match s with
    | .journal | .head => "nat×digest" | .retired | .spent => "unit" | .parent => "cell-id/nat"
    | .allowance => "nat"

/-- **The system sub-codec of the World checkpoint.** -/
def systemStream : StreamCodec (Store DSys) := StoreCodec.payloadStream systemWire

theorem systemStream_roundtrip (s : Store DSys) (suffix : List UInt8) :
    systemStream.decodePrefix (systemStream.encode s ++ suffix) = some (s, suffix) :=
  systemStream.decodePrefix_encode s suffix

#assert_axioms systemStream_roundtrip

end Minidregg.Kernel.WorldSystemCodec
