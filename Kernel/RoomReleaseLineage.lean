/- Canonical head selection from source history. This parser produces Claims,
never authority or an Applied permit. The native chronological verifier must
admit EVERY event67 at its original prefix before the high protected reader may
export this selection as the latest head. Ordinary content atoms do not enter
this lineage, even if they contain identical-looking release bytes. -/
import Kernel.RoomReleaseIntent
namespace Minidregg.Kernel.RoomReleaseLineage
open Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableReceiver
set_option autoImplicit false

structure Claim where
  index : Nat
  source : RoomReleaseIntent.Ingress
  epoch : RoomKeyReleaseCodec.Epoch
  deriving DecidableEq

def previousEpoch (previous : Option Claim) : Option Nat := previous.map (fun p => p.epoch.epoch)
def previousIdentity (previous : Option Claim) : List UInt8 :=
  previous.map (fun p => p.epoch.identity) |>.getD (List.replicate 32 0)

/-- Reusing an epoch requires its COMPLETE original certificate bytes. A new
epoch names the prior exact identity and increments once; empty history cannot
be presented as a lower head. Signature/current-law checks are separate. -/
def nextKind (previous : Option Claim) (source : RoomReleaseIntent.Ingress)
    (epoch : RoomKeyReleaseCodec.Epoch) : Option Bool :=
  if source.body.priorEpoch != previousEpoch previous ||
      source.body.priorIdentity != previousIdentity previous then none else
  if epoch.room != source.body.room || epoch.keysCell != source.body.keysCell ||
      epoch.bytes != source.body.certificate || epoch.epoch ≥ 2^31 then none else
  match previous with
  | none => if epoch.epoch = 0 ∧ epoch.parent = List.replicate 32 0 ∧
      epoch.signer = source.body.actor then some true else none
  | some prior =>
    if epoch.bytes = prior.epoch.bytes then some false else
    if epoch.epoch = prior.epoch.epoch + 1 ∧ epoch.parent = prior.epoch.identity ∧
        epoch.signer = source.body.actor then some true else none

def latest (records : List IntentRecord) (room keysCell : Nat) : Except String (Option Claim) :=
  let rec loop : Nat → List IntentRecord → Option Claim → Except String (Option Claim)
    | _,[],head => .ok head
    | index,record :: tail,head =>
      if record.event.codecVersion = 67 then
        match RoomReleaseIntent.ingressCodec.decode record.event.canonicalBytes with
        | none => .error "malformed source room release event"
        | some source =>
          if source.body.room = room ∧ source.body.keysCell = keysCell then
            match RoomKeyReleaseCodec.decodeEpoch source.body.certificate with
            | none => .error "malformed source room epoch certificate"
            | some epoch =>
              match nextKind head source epoch with
              | none => .error "source room lineage fork, rollback or skipped epoch"
              | some _ => loop (index + 1) tail (some ⟨index,source,epoch⟩)
          else loop (index + 1) tail head
      else loop (index + 1) tail head
  loop 0 records none

theorem empty_head (room keysCell : Nat) : latest [] room keysCell = .ok none := rfl

theorem different_certificate_cannot_reuse {previous : Claim} {source : RoomReleaseIntent.Ingress}
    {epoch : RoomKeyReleaseCodec.Epoch}
    (different : epoch.bytes ≠ previous.epoch.bytes)
    (sameEpoch : epoch.epoch = previous.epoch.epoch) :
    nextKind (some previous) source epoch ≠ some false := by
  unfold nextKind
  split
  · simp
  · split
    · simp
    · simp [different]

#assert_axioms empty_head
#assert_axioms different_certificate_cannot_reuse
end Minidregg.Kernel.RoomReleaseLineage
