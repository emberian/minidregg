/-
Source-owned choice between a signed SPK create action and its signed continue
command. The package descriptor is reusable across grains. This binding is
specific to one never-recycled Mini application resource and its persistent
volume lineage. A physical host must attest that its protected volume maps to
this identifier; a path, empty directory, dev/inode pair or operator Boolean
does not establish Mini authority.

The separate checked START admission must obtain an exact completed-create
certificate from verified history for `continue`, and absence of an earlier
first-attempt claim for `create`. This pure shape alone is not a launch permit.
-/
import Kernel.ApplicationSpkLaunchDescriptor
import Compiler.NativeHostCodec

namespace Minidregg.Kernel.ApplicationLifecycleLaunchBinding

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- Mini resource IDs are permanently fresh within a deployment directory.
This ID follows that resource across package upgrades. Recreating a destroyed
grain requires a new app resource ID or a separately versioned incarnation
contract; host custody must not attach the old protected volume to a new
deployment. -/
def volumeIdOutput (domain : Digest) (app : Nat) : Sp800185Cshake256.Output :=
  Sp800185Cshake256.hash
    "DREGG/APPLICATION/PERSISTENT-VOLUME-ID/v1".toUTF8.toList
    ((StreamCodec.product digestStream StreamCodec.nat).encode (domain, app))

def volumeId (domain : Digest) (app : Nat) : Digest :=
  (volumeIdOutput domain app).digest

/-- Exact 32 source bytes for the physical registration profile. This is not
the Nat/varint `digestStream` encoding of a `Digest`. -/
def volumeIdBytes (domain : Digest) (app : Nat) : List UInt8 :=
  (volumeIdOutput domain app).bytes

theorem volumeIdBytes_length (domain : Digest) (app : Nat) :
    (volumeIdBytes domain app).length = 32 :=
  (volumeIdOutput domain app).length_exact

theorem volumeId_digestBytesLE (domain : Digest) (app : Nat) :
    Sp800185Cshake256.digestBytesLE (volumeId domain app) =
      volumeIdBytes domain app :=
  Sp800185Cshake256.digestBytesLE_digestOfBytesLE
    (volumeIdBytes domain app) (volumeIdBytes_length domain app)

inductive Choice where
  | create (actionIndex : Nat)
  | continue
  deriving DecidableEq, Repr

def choiceStream : StreamCodec Choice :=
  StreamCodec.xmap StreamCodec.nat
    (fun choice => match choice with
      | .create index => index + 1
      | .continue => 0)
    (fun value => match value with
      | 0 => .continue
      | index + 1 => .create index)
    (by intro choice; cases choice <;> rfl)

/-- A host-signed physical observation tied to the stable kernel volume ID.
`physicalWitness` is a bounded exact byte record supplied by the protected
volume custodian. Mini binds and compares it; Mini does not infer ownership or
filesystem state from those bytes. -/
structure Custody where
  volume : Digest
  physicalWitness : List UInt8
  deriving DecidableEq, Repr

def custodyStream : StreamCodec Custody :=
  StreamCodec.xmap (StreamCodec.product digestStream bytesStream)
    (fun custody => (custody.volume, custody.physicalWitness))
    (fun (volume, physicalWitness) => ⟨volume, physicalWitness⟩)
    (by intro custody; cases custody; rfl)

def custodyFrame : List UInt8 := "DREGG/SPK-VAR-CUSTODY/v1".toUTF8.toList

def Custody.validFor (custody : Custody) (volume : Digest) : Bool :=
  custody.volume == volume &&
    custody.physicalWitness.take custodyFrame.length == custodyFrame &&
    decide (custody.physicalWitness.length ≤ 4096)

/-- The selected create index is grain-specific, while the command itself
comes from the package's complete signed action list. `priorCreate` names the
exact successful creation receipt and its signed physical volume custody
bytes. Both remain selectors until the native receiver re-admits that
completion at its original prefix and proves its inclusion in Verified. -/
structure Binding where
  app : Nat
  volume : Digest
  packageRoot : Digest
  choice : Choice
  priorCreate : Option (NativeHostCodec.Receipt × Custody)
  commandDigest : Digest
  deriving DecidableEq, Repr

def bindingStream : StreamCodec Binding :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digestStream
        (StreamCodec.product digestStream
          (StreamCodec.product choiceStream
            (StreamCodec.product
              (StreamCodec.option
                (StreamCodec.product NativeHostCodec.receiptStream custodyStream))
              digestStream)))))
    (fun binding => (binding.app, binding.volume, binding.packageRoot,
      binding.choice, binding.priorCreate, binding.commandDigest))
    (fun (app, volume, packageRoot, choice, priorCreate, commandDigest) =>
      ⟨app, volume, packageRoot, choice, priorCreate, commandDigest⟩)
    (by intro binding; cases binding; rfl)

def codec : LawfulCodec Binding :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/LIFECYCLE-LAUNCH-BINDING/v1".toUTF8.toList bindingStream

def Binding.canonicalBytes (binding : Binding) : List UInt8 :=
  codec.encode binding

def Binding.selectedCommand (binding : Binding)
    (descriptor : ApplicationSpkLaunchDescriptor.Descriptor) :
    Option ApplicationSpkLaunchDescriptor.Command :=
  match binding.choice with
  | .create index => descriptor.selectedCreate index
  | .continue => some descriptor.continueCommand

def Binding.selectedCommandDigest (binding : Binding)
    (descriptor : ApplicationSpkLaunchDescriptor.Descriptor) : Option Digest :=
  (binding.selectedCommand descriptor).map ApplicationSpkLaunchDescriptor.Command.digest

def Binding.valid (domain : Digest) (binding : Binding)
    (descriptor : ApplicationSpkLaunchDescriptor.Descriptor) : Bool :=
  descriptor.valid && binding.volume == volumeId domain binding.app &&
    binding.packageRoot == descriptor.root &&
    decide (binding.selectedCommandDigest descriptor = some binding.commandDigest) &&
    match binding.choice, binding.priorCreate with
    | .create index, none => (descriptor.selectedCreate index).isSome
    | .continue, some (_, custody) => custody.validFor binding.volume
    | _, _ => false

theorem Binding.valid_selected_digest (domain : Digest) (binding : Binding)
    (descriptor : ApplicationSpkLaunchDescriptor.Descriptor)
    (valid : binding.valid domain descriptor = true) :
    binding.selectedCommandDigest descriptor = some binding.commandDigest := by
  simp only [Binding.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
  aesop

/-- Distinct source domains for the first one-shot launch claim and the
successful physical creation report. The eventual special receivers install
these as distinct stable nullifiers; a mere hash preimage is not a receipt. -/
def firstAttemptKey (domain : Digest) (binding : Binding) : Digest :=
  (Sp800185Cshake256.hash
    "DREGG/APPLICATION/FIRST-START-ATTEMPT/v1".toUTF8.toList
    ((StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat digestStream)).encode
      (domain, binding.app, binding.volume))).digest

def createdKey (domain : Digest) (binding : Binding) : Digest :=
  (Sp800185Cshake256.hash
    "DREGG/APPLICATION/VOLUME-CREATED/v1".toUTF8.toList
    ((StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat digestStream)).encode
      (domain, binding.app, binding.volume))).digest

theorem decode_encode (binding : Binding) :
    codec.decode binding.canonicalBytes = some binding :=
  codec.decode_encode binding

theorem decoded_canonical {bytes : List UInt8} {binding : Binding}
    (decoded : codec.decode bytes = some binding) :
    binding.canonicalBytes = bytes :=
  NativeHostCodec.framed_canonical _ bindingStream decoded

theorem canonical_injective : Function.Injective Binding.canonicalBytes :=
  lawful_encode_injective codec

theorem create_has_no_prior (domain : Digest) (binding : Binding)
    (descriptor : ApplicationSpkLaunchDescriptor.Descriptor)
    (valid : binding.valid domain descriptor = true)
    (index : Nat) (choice : binding.choice = .create index) :
    binding.priorCreate = none := by
  simp only [Binding.valid, Bool.and_eq_true] at valid
  have selected := valid.2
  cases h : binding.priorCreate with
  | none => rfl
  | some prior => simp [choice, h] at selected

end Minidregg.Kernel.ApplicationLifecycleLaunchBinding
