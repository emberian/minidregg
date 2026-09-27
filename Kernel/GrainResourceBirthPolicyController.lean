/-
Strict source ingress for the composite resource birth. This module does not
admit a request: the complete birth credential bundle and the signed grain
target, observation, and authority envelopes must still be checked against
one current loaded image and one joint candidate before any durable intent.
-/
import Compiler.GrainResourceBirthController
import Compiler.GrainResourceBirthHostCodec
import Kernel.ResourceBirthPolicyController
import Kernel.DeclaredResourceController

namespace Minidregg.Kernel.GrainResourceBirthPolicyController

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram

set_option autoImplicit false

structure SignedIngress where
  sourceBytes : List UInt8
  birthBytes : List UInt8
  grainBytes : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec SignedIngress :=
  StreamCodec.xmap (StreamCodec.product bytesStream
    (StreamCodec.product bytesStream bytesStream))
    (fun ingress => (ingress.sourceBytes, ingress.birthBytes, ingress.grainBytes))
    (fun pair => ⟨pair.1, pair.2.1, pair.2.2⟩)
    (by intro ingress; cases ingress; rfl)

def ingressFrame : List UInt8 :=
  "DREGG/GRAIN-RESOURCE-BIRTH/SIGNED-INGRESS/v2".toUTF8.toList

def ingressRawCodec : LawfulCodec SignedIngress where
  encode ingress := ingressFrame ++ ingressStream.encode ingress
  decode bytes := if bytes.take ingressFrame.length = ingressFrame then
    ingressStream.toLawful.decode (bytes.drop ingressFrame.length) else none
  decode_encode := by
    intro ingress
    have decoded := ingressStream.toLawful.decode_encode ingress
    change ingressStream.toLawful.decode (ingressStream.encode ingress) = some ingress at decoded
    simp [decoded]

def ingressCodec : LawfulCodec SignedIngress :=
  ResourceBirthCodec.strictCodec ingressRawCodec

/-- The new source carrier is bounded before nested descriptor decoding. This
cap applies only to grain-backed birth, not to the legacy bare-birth route. -/
def maxSourceBytes : Nat := 8 * 1024 * 1024

structure DecodedIngress where
  private mk ::
  raw : SignedIngress
  sourceSizeBound : raw.sourceBytes.length ≤ maxSourceBytes
  source : GrainResourceBirthController.Source
  birth : ResourceBirthPolicyController.Concrete.DecodedIngress
  grain : DeclaredResourceController.SignedIngress
  command : DeclaredResourceController.Command
  sourceExact : GrainResourceBirthHostCodec.sourceCodec.decode raw.sourceBytes = some source
  sourceCanonical : GrainResourceBirthHostCodec.sourceCodec.encode source = raw.sourceBytes
  birthExact : birth.bytes = raw.birthBytes
  grainExact : DeclaredResourceController.signedBytes grain.1 grain.2.1 grain.2.2 = raw.grainBytes
  commandExact : DeclaredResourceController.commandCodec.encode command =
    grain.2.2.commandBytes

def decodeIngress (bytes : List UInt8) : Option DecodedIngress := do
  let raw ← ingressCodec.decode bytes
  if size : raw.sourceBytes.length ≤ maxSourceBytes then
  match sourceDecoded : GrainResourceBirthHostCodec.sourceCodec.decode raw.sourceBytes with
  | none => none
  | some source =>
      match born : ResourceBirthPolicyController.Concrete.decodeIngress raw.birthBytes with
      | none => none
      | some birth =>
          match signed : DeclaredResourceController.decodeSignedBytes raw.grainBytes with
          | none => none
          | some grain =>
              match decoded : DeclaredResourceController.commandCodec.decode
                  grain.2.2.commandBytes with
              | none => none
              | some command =>
                  some ⟨raw, size, source, birth, grain, command, sourceDecoded,
                    GrainResourceBirthHostCodec.sourceCodec_canonical sourceDecoded,
                    ResourceBirthPolicyController.Concrete.decodeIngress_canonical born,
                    DeclaredResourceController.decodeSignedBytes_canonical signed,
                    DeclaredResourceController.command_decode_canonical decoded⟩
  else none

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.raw

theorem decodeIngress_canonical {bytes : List UInt8} {ingress : DecodedIngress}
    (decoded : decodeIngress bytes = some ingress) : ingress.bytes = bytes := by
  unfold decodeIngress at decoded
  cases parsed : ingressCodec.decode bytes with
  | none => simp [parsed] at decoded
  | some raw =>
      simp only [parsed, bind, Option.bind] at decoded
      split at decoded <;> try contradiction
      split at decoded <;> try contradiction
      split at decoded <;> try contradiction
      split at decoded <;> try contradiction
      split at decoded <;> try contradiction
      cases Option.some.inj decoded
      exact ResourceBirthCodec.strictCodec_canonical ingressRawCodec parsed

/-- This binds the three strict carriers to the source-derived command and
receiver domain/semantics. The caller obtains `source` from the canonical
source carrier; current target preparation verifies both supplied old states
against the same loaded cells before any fresh acceptance. -/
def SourceBound (domain semantics : Minidregg.Theory.TypedAuthorization.Digest)
    (tariff : GrainResourceBirthController.Tariff)
    (source : GrainResourceBirthController.Source)
    (ingress : DecodedIngress) : Prop :=
  ingress.raw.sourceBytes = GrainResourceBirthHostCodec.sourceCodec.encode source ∧
  ingress.birth.ingress.descriptorBytes =
    CanonicalCellRegistry.sourceEncoding.codec.encode source.birth ∧
  ingress.grain.2.2.commandBytes =
    DeclaredResourceController.commandCodec.encode (source.grainCommand tariff) ∧
  ingress.grain.1 = domain ∧
  ingress.grain.2.1 = semantics ∧
  ingress.grain.2.2.targetEnvelopes.length = 2 ∧
  ingress.grain.2.2.observeEnvelopes.length = 2

instance sourceBoundDecidable (domain semantics : Minidregg.Theory.TypedAuthorization.Digest)
    (tariff : GrainResourceBirthController.Tariff)
    (source : GrainResourceBirthController.Source) (ingress : DecodedIngress) :
    Decidable (SourceBound domain semantics tariff source ingress) := by
  unfold SourceBound
  infer_instance

def checkSourceBound (domain semantics : Minidregg.Theory.TypedAuthorization.Digest)
    (tariff : GrainResourceBirthController.Tariff)
    (source : GrainResourceBirthController.Source) (ingress : DecodedIngress) :
    Option (PLift (SourceBound domain semantics tariff source ingress)) :=
  if bound : SourceBound domain semantics tariff source ingress then some ⟨bound⟩ else none

theorem checkSourceBound_iff (domain semantics : Minidregg.Theory.TypedAuthorization.Digest)
    (tariff : GrainResourceBirthController.Tariff)
    (source : GrainResourceBirthController.Source) (ingress : DecodedIngress) :
    (checkSourceBound domain semantics tariff source ingress).isSome = true ↔
      SourceBound domain semantics tariff source ingress := by
  by_cases bound : SourceBound domain semantics tariff source ingress <;>
    simp [checkSourceBound, bound]

theorem sourceBound_birth_exact
    {domain semantics : Minidregg.Theory.TypedAuthorization.Digest}
    {tariff : GrainResourceBirthController.Tariff}
    {source : GrainResourceBirthController.Source} {ingress : DecodedIngress}
    (bound : SourceBound domain semantics tariff source ingress) :
    ingress.birth.descriptor = source.birth := by
  have bytes := bound.2.1
  have decoded := ingress.birth.descriptorExact
  rw [bytes, CanonicalCellRegistry.sourceEncoding.codec.decode_encode] at decoded
  exact (Option.some.inj decoded).symm

theorem sourceBound_source_exact
    {domain semantics : Minidregg.Theory.TypedAuthorization.Digest}
    {tariff : GrainResourceBirthController.Tariff}
    {source : GrainResourceBirthController.Source} {ingress : DecodedIngress}
    (bound : SourceBound domain semantics tariff source ingress) :
    ingress.source = source := by
  have bytes := bound.1
  have decoded := ingress.sourceExact
  rw [bytes, GrainResourceBirthHostCodec.sourceCodec.decode_encode] at decoded
  exact (Option.some.inj decoded).symm

theorem sourceBound_command_exact
    {domain semantics : Minidregg.Theory.TypedAuthorization.Digest}
    {tariff : GrainResourceBirthController.Tariff}
    {source : GrainResourceBirthController.Source} {ingress : DecodedIngress}
    (bound : SourceBound domain semantics tariff source ingress) :
    ingress.command = source.grainCommand tariff := by
  have bytes := bound.2.2.1
  have decoded := ingress.commandExact
  rw [bytes] at decoded
  have canonical := DeclaredResourceController.commandCodec.decode_encode
    (source.grainCommand tariff)
  have decodedIngress := DeclaredResourceController.commandCodec.decode_encode ingress.command
  rw [decoded] at decodedIngress
  rw [canonical] at decodedIngress
  exact (Option.some.inj decodedIngress).symm

theorem mismatched_command_refused
    (domain semantics : Minidregg.Theory.TypedAuthorization.Digest)
    (tariff : GrainResourceBirthController.Tariff)
    (source : GrainResourceBirthController.Source) (ingress : DecodedIngress)
    (different : ingress.command ≠ source.grainCommand tariff) :
    checkSourceBound domain semantics tariff source ingress = none := by
  unfold checkSourceBound
  split
  · exact False.elim (different (sourceBound_command_exact ‹SourceBound domain semantics tariff source ingress›))
  · rfl

end Minidregg.Kernel.GrainResourceBirthPolicyController
