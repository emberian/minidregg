/- Participant-held public acknowledged history. This file is owned and retained
independently from server archive custody. It is not another source journal or
an authority/transfer token. Archive-before-signature comes from CheckedACK;
local durable CAS-before-return makes the participant acknowledgement usable.
-/
import Compiler.PortableContinuationArchiveIO
namespace Minidregg.Compiler.PortableParticipantPinIO
open Minidregg.Kernel.PortableContinuationManifest
open Minidregg.Compiler.PortableContinuationManifestCodec
open Minidregg.Compiler.PortableContinuationArchiveIO
set_option autoImplicit false

structure Config where
  helper : System.FilePath
  helperSha256 : String
  /-- Independently provisioned participant-owned private state, not copied
  from an archive or selected by a restored request. Bootstrap endpoint/key
  are authenticated independently; this API cannot bootstrap from a manifest. -/
  root : System.FilePath

def frame (pin : ParticipantPin) : Bytes :=
  acknowledgementFrame ⟨pin.participant,pin.publicKey,pin.identity,pin.acknowledged⟩

/-- Exact current/next pin files are compared by the SAME streaming native CAS
transport as agreement storage, with stable lock and fsync/rename/dir-fsync.
Only public pin bytes enter this participant directory. -/
private def cas (config : Config) (expected next : Bytes) : IO Unit := do
  IO.FS.withTempDir fun directory => do
    let helper := directory / "archive-helper"
    IO.FS.withFile config.helper .read fun handle => do
      let mut bytes := ByteArray.empty
      while bytes.size ≤ 64*1024*1024 do
        let part ← handle.read (min 65536 (64*1024*1024 + 1 - bytes.size)).toUSize
        if part.isEmpty then break
        bytes := bytes ++ part
      if bytes.size > 64*1024*1024 then throw (IO.userError "pin helper exceeds bound")
      IO.FS.writeBinFile helper bytes
    let paths := [(helper,"0500"),(directory / "expected","0600"),(directory / "next","0600")]
    IO.FS.writeBinFile (directory / "expected") expected.toByteArray
    IO.FS.writeBinFile (directory / "next") next.toByteArray
    for (path,mode) in paths do
      let result ← IO.Process.output {cmd := "/usr/bin/chmod",args := #[mode,path.toString]}
      if result.exitCode != 0 || result.stderr != "" then
        throw (IO.userError "participant private pin mode refused")
    IO.ofExcept (← RetainedArtifactIO.checkedFile helper config.helperSha256)
    let result ← IO.Process.output {cmd := helper.toString,args := #["cas",
      (config.root / "acknowledged-history.bin").toString,
      (directory / "expected").toString,(directory / "next").toString]}
    if result.exitCode != 0 || result.stderr != "" || result.stdout != "durable\n" then
      throw (IO.userError "participant pin CAS conflict or uncertain")

structure Held (config : Config) (old : ParticipantPin) (manifest : Manifest) where
  private mk ::
  checked : CheckedAcknowledgement old manifest

/-- Caller consumes an archive-retained signature/continuity capability.
Stale/forked local pin refuses. Exact lost-reply retry performs a new SAME-BYTES
CAS/readback instead of inferring durability from file equality. No result is
returned on an uncertain helper reply; reopen and retry the identical token.
A newer independent pin is never rolled back to this proposed endpoint. -/
def hold (config : Config) (old : ParticipantPin) (manifest : Manifest)
    (checked : CheckedAcknowledgement old manifest) : IO (Except String (Held config old manifest)) := do
  try
    let owner ← IO.Process.output {cmd := "/usr/bin/id",args := #["-u"]}
    let mode ← IO.Process.output {cmd := "/usr/bin/stat",args := #["-c","%u:%a:%f",config.root.toString]}
    if owner.exitCode != 0 || owner.stderr != "" || mode.exitCode != 0 || mode.stderr != "" ||
        mode.stdout != owner.stdout.trimAscii.toString ++ ":700:41c0\n" then
      return .error "participant state directory custody refused"
    let path := config.root / "acknowledged-history.bin"
    let present := (← IO.FS.readBinFile path).toList
    let expected := frame old
    let next := frame checked.next
    if present != expected && present != next then
      return .error "participant held history differs or already advanced"
    cas config present next
    if (← IO.FS.readBinFile path).toList != next then
      return .error "participant pin exact readback differs"
    return .ok ⟨checked⟩
  catch _ => return .error "participant pin persistence uncertain or refused"

/-- Every locally held ACK preserves independently pinned identity/key and
has a checked authenticated nondecreasing history endpoint. File/OS/disk and
signature verification remain the explicit native boundary assumptions. -/
theorem held_nonregression (config : Config) (old : ParticipantPin) (manifest : Manifest)
    (held : Held config old manifest) : old.acknowledged.height ≤ held.checked.next.acknowledged.height :=
  acknowledge_nonregression held.checked.exact

theorem held_identity (config : Config) (old : ParticipantPin) (manifest : Manifest)
    (held : Held config old manifest) : held.checked.next.identity = old.identity :=
  (acknowledge_exact held.checked.exact).2.2.2.2.2.2.2.2

#assert_axioms held_nonregression
#assert_axioms held_identity
end Minidregg.Compiler.PortableParticipantPinIO
