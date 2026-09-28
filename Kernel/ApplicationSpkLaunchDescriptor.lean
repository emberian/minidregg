/-
The signed package identity used by a resident application launch. V1 SPK
identity binds the signed manifest hash but does not expose its commands to
Mini. This additive descriptor commits the complete ordered create-action
command list and the continue command from the same verified manifest parse.
It is reusable by any grain installing the package: action selection and the
grain's persistent volume identity belong to a separate lifecycle ingress.

The older ApplicationSpkPackageIdentity descriptor, root and replay grammar
are unchanged. Physical custody must compare every command here with the one
signature-verified SPK parse; a caller's matching SHA assertion is not proof
of that comparison.
-/
import Kernel.ApplicationSpkPackageIdentity

namespace Minidregg.Kernel.ApplicationSpkLaunchDescriptor

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- Argument and environment order, including duplicate environment names,
is preserved exactly. The host supplies UTF-8 bytes obtained from the signed
manifest parser and checks them again before launch. -/
structure Command where
  argv : List (List UInt8)
  environ : List (List UInt8 × List UInt8)
  deriving DecidableEq, Repr

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product (StreamCodec.list bytesStream)
      (StreamCodec.list (StreamCodec.product bytesStream bytesStream)))
    (fun command => (command.argv, command.environ))
    (fun (argv, environ) => ⟨argv, environ⟩)
    (by intro command; cases command; rfl)

def commandCodec : LawfulCodec Command :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/SPK-LAUNCH-COMMAND/v1".toUTF8.toList commandStream

def Command.canonicalBytes (command : Command) : List UInt8 :=
  commandCodec.encode command

def Command.digest (command : Command) : Digest :=
  (Sp800185Cshake256.hash
    "DREGG/APPLICATION/SPK-LAUNCH-COMMAND-ROOT/v1".toUTF8.toList
    command.canonicalBytes).digest

def bytesValid (bytes : List UInt8) : Bool :=
  !bytes.isEmpty && decide (bytes.length ≤ 4096) && !bytes.contains 0

def argumentValid (bytes : List UInt8) : Bool :=
  decide (bytes.length ≤ 4096) && !bytes.contains 0

/-- This is a bounded carrier check, not a reimplementation of the SPK
manifest parser's command semantics. -/
def Command.valid (command : Command) : Bool :=
  (match command.argv with
   | [] => false
   | executable :: arguments => bytesValid executable &&
       arguments.all argumentValid) &&
    decide (command.argv.length ≤ 64) &&
    decide (command.environ.length ≤ 128) &&
    command.environ.all (fun pair => bytesValid pair.1 &&
      decide (pair.1.length ≤ 256) && decide (pair.2.length ≤ 4096) &&
      !pair.2.contains 0)

/-- All signed create actions are retained in their original order. A grain
chooses one index in a separately signed START binding; the package root is
independent of that grain and its persistent volume. -/
structure Descriptor where
  package : ApplicationSpkPackageIdentity.Descriptor
  createCommands : List Command
  continueCommand : Command
  deriving DecidableEq, Repr

def descriptorStream : StreamCodec Descriptor :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationSpkPackageIdentity.descriptorStream
      (StreamCodec.product (StreamCodec.list commandStream) commandStream))
    (fun descriptor => (descriptor.package,
      descriptor.createCommands, descriptor.continueCommand))
    (fun (package, createCommands, continueCommand) =>
      ⟨package, createCommands, continueCommand⟩)
    (by intro descriptor; cases descriptor; rfl)

def codec : LawfulCodec Descriptor :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/SPK-LAUNCH-DESCRIPTOR/v2".toUTF8.toList descriptorStream

def codecV3 : LawfulCodec Descriptor :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/SPK-LAUNCH-DESCRIPTOR/v3".toUTF8.toList descriptorStream

/-- A launch whose signed package uses the new API prefix profile has its own
frame and root domain. GitWeb and web-only launch identities stay byte-exact. -/
def Descriptor.legacyProfile (descriptor : Descriptor) : Bool :=
  descriptor.package.legacyProfile

def Descriptor.canonicalBytes (descriptor : Descriptor) : List UInt8 :=
  if descriptor.legacyProfile then codec.encode descriptor
  else codecV3.encode descriptor

def decodeCanonical (bytes : List UInt8) : Option Descriptor :=
  match codec.decode bytes with
  | some descriptor =>
      if descriptor.legacyProfile then some descriptor else none
  | none =>
      match codecV3.decode bytes with
      | some descriptor =>
          if descriptor.legacyProfile then none else some descriptor
      | none => none

def Descriptor.valid (descriptor : Descriptor) : Bool :=
  descriptor.package.valid && !descriptor.createCommands.isEmpty &&
    decide (descriptor.createCommands.length ≤ 64) &&
    descriptor.createCommands.all Command.valid &&
    descriptor.continueCommand.valid &&
    decide (descriptor.canonicalBytes.length ≤ 1024 * 1024)

def Descriptor.root (descriptor : Descriptor) : Digest :=
  (Sp800185Cshake256.hash
    (if descriptor.legacyProfile then
      "DREGG/APPLICATION/SPK-PACKAGE-LAUNCH-ROOT/v2".toUTF8.toList
     else "DREGG/APPLICATION/SPK-PACKAGE-LAUNCH-ROOT/v3".toUTF8.toList)
    descriptor.canonicalBytes).digest

def Descriptor.matchesManifest (descriptor : Descriptor)
    (manifest : ApplicationDispatchManifest.Manifest) : Bool :=
  descriptor.valid && decide (manifest.packageRoot = descriptor.root) &&
    decide (manifest.interfaces = descriptor.package.interfaces) && manifest.valid

theorem Descriptor.matchesManifest_root (descriptor : Descriptor)
    (manifest : ApplicationDispatchManifest.Manifest)
    (matched : descriptor.matchesManifest manifest = true) :
    manifest.packageRoot = descriptor.root := by
  simp only [Descriptor.matchesManifest, Bool.and_eq_true,
    decide_eq_true_eq] at matched
  aesop

def Descriptor.selectedCreate (descriptor : Descriptor) (index : Nat) :
    Option Command := descriptor.createCommands[index]?

theorem decode_encode (descriptor : Descriptor) :
    codec.decode (codec.encode descriptor) = some descriptor :=
  codec.decode_encode descriptor

theorem decode_encode_v3 (descriptor : Descriptor) :
    codecV3.decode (codecV3.encode descriptor) = some descriptor :=
  codecV3.decode_encode descriptor

theorem decoded_canonical {bytes : List UInt8} {descriptor : Descriptor}
    (decoded : codec.decode bytes = some descriptor) :
    codec.encode descriptor = bytes :=
  NativeHostCodec.framed_canonical _ descriptorStream decoded

theorem decoded_canonical_v3 {bytes : List UInt8} {descriptor : Descriptor}
    (decoded : codecV3.decode bytes = some descriptor) :
    codecV3.encode descriptor = bytes :=
  NativeHostCodec.framed_canonical _ descriptorStream decoded

theorem legacy_codec_injective : Function.Injective codec.encode :=
  lawful_encode_injective codec

theorem canonical_injective_v3 : Function.Injective codecV3.encode :=
  lawful_encode_injective codecV3

theorem v2_frame_refuses_new_profile (descriptor : Descriptor)
    (newProfile : descriptor.legacyProfile = false) :
    decodeCanonical (codec.encode descriptor) = none := by
  simp [decodeCanonical, codec.decode_encode, newProfile]

end Minidregg.Kernel.ApplicationSpkLaunchDescriptor
