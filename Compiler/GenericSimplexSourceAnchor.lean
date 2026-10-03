import Compiler.GenericSimplexCodec
import Theory.AssertAxioms
namespace Minidregg.Compiler.GenericSimplexSourceAnchor
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false

/-- Exact source genesis, not its possibly colliding identifier. Epoch and
membership remain in the enclosing Context. This version always replays the
complete source log from genesis; it is not a checkpoint/reconfiguration codec. -/
def anchorStream : StreamCodec (Nat × Seed) :=
  StreamCodec.product StreamCodec.nat DurableReceiverCodec.seedStream

def anchorBytes (genesisHeight : Nat) (seed : Seed) : Bytes :=
  "MINI-SIMPLEX-SOURCE-GENESIS/v1".toUTF8.toList ++
    anchorStream.encode (genesisHeight,seed)

def bind (base : Context) (genesisHeight : Nat) (seed : Seed) : Context :=
  {base with instanceBytes := anchorBytes genesisHeight seed}

/-- A source genesis contains policies derived from runtime semantics. Including
the genesis bytes in those semantics would make construction self-referential.
Semantic membership parameters omit only the instance anchor; deployment pins
and authenticates the full Context separately after constructing the genesis. -/
def semanticMembershipBytes (context : Context) : Bytes :=
  contextStream.encode {context with instanceBytes := []}

theorem semantic_membership_anchor_independent (context : Context)
    (genesisHeight : Nat) (seed : Seed) :
    semanticMembershipBytes (bind context genesisHeight seed) =
      semanticMembershipBytes context := rfl

theorem anchor_injective (height₁ height₂ : Nat) (seed₁ seed₂ : Seed)
    (same : anchorBytes height₁ seed₁ = anchorBytes height₂ seed₂) :
    (height₁,seed₁) = (height₂,seed₂) := by
  have encoded : anchorStream.encode (height₁,seed₁) =
      anchorStream.encode (height₂,seed₂) := List.append_cancel_left same
  have decoded := congrArg anchorStream.toLawful.decode encoded
  have left := anchorStream.toLawful.decode_encode (height₁,seed₁)
  have right := anchorStream.toLawful.decode_encode (height₂,seed₂)
  change anchorStream.toLawful.decode (anchorStream.encode (height₁,seed₁)) =
    some (height₁,seed₁) at left
  change anchorStream.toLawful.decode (anchorStream.encode (height₂,seed₂)) =
    some (height₂,seed₂) at right
  rw [left,right] at decoded
  exact Option.some.inj decoded

#assert_axioms semantic_membership_anchor_independent
#assert_axioms anchor_injective
end Minidregg.Compiler.GenericSimplexSourceAnchor
