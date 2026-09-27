import Kernel.NativeHostReplay

open Minidregg.Compiler
open Minidregg.Kernel

def main : IO Unit := do
  let imageBytes ← IO.FS.readBinFile
    "/home/ember/build/minidregg-f461-replay-profile-v2-20260927/image.bin"
  let some image := DurableReceiverCodec.decode imageBytes.toList
    | throw (IO.userError "copied image failed canonical decode")
  let mut index := 0
  for record in image.accepted do
    let bytes := record.event.canonicalBytes
    let kind :=
      if (ApplicationShareIssueGrainSource.codec.decode bytes).isSome then "grainShareIssue"
      else if (GrainResourceBirthPolicyController.decodeIngress bytes).isSome then "grainBirth"
      else if (ResourceBirthPolicyController.Concrete.decodeIngress bytes).isSome then "resourceBirth"
      else if (DeclaredResourceController.decodeSignedBytes bytes).isSome then "ordinaryInvoke"
      else "otherSpecial"
    IO.println s!"{index} {record.event.codecVersion} {kind}"
    index := index + 1
