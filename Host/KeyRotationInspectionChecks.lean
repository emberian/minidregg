/- Signature-critical inspection checks: canonical framing alone does not
bind a possession header to the command that a client displays. -/
import Host.Json

namespace Minidregg.Host.KeyRotationInspectionChecks
open Minidregg.Kernel

private def command : SubjectKeyRotation.Command :=
  ⟨⟨9⟩, 31, ⟨18, 5, 1, 9, List.replicate 32 (2 : UInt8), 0, 100, some ⟨77⟩⟩⟩
private def plan : SubjectKeyRotation.SigningPlan :=
  ⟨⟨8501⟩, ⟨27⟩, SubjectKeyRotation.commandCodec.encode command,
    SubjectKeyRotation.possessionFrame ⟨8501⟩ ⟨27⟩ command⟩
private def accepts (value : SubjectKeyRotation.SigningPlan) : Bool :=
  (Minidregg.Host.Json.inspect "subject-key-rotation-plan"
    (SubjectKeyRotation.signingPlanCodec.encode value)).isOk

#guard accepts plan
#guard !accepts { plan with possessionHeader := [0] }
#guard !accepts { plan with domain := ⟨8502⟩ }
#guard !accepts { plan with commandBytes :=
  SubjectKeyRotation.commandCodec.encode { command with nonce := 32 } }

end Minidregg.Host.KeyRotationInspectionChecks
