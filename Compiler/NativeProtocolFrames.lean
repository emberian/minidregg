/- Source-owned native protocol frame bytes shared by the actual codecs and
runtime identity. This module deliberately imports no controller or profile:
wire epochs can be committed without a codec → profile → codec import cycle.
Existing namespaces are retained so every encoder/decoder uses these same
constants; retired frame fixtures remain next to their refusal proofs. -/
import Init

namespace Minidregg.Compiler.NativeHostCodec

/-- Version 4 (K-RENOUNCE): the call gains `renounce`; a v3 call refuses. -/
def callFrame : List UInt8 := "DREGG/NATIVE-HOST/SIGNED-CALL/v4".toUTF8.toList

/-- Version 5 binds the complete roster witness into the authoring intent. -/
def draftFrame : List UInt8 := "DREGG/NATIVE-HOST/DRAFT/v5".toUTF8.toList

/-- Version 6 carries the roster-bound finalized draft. -/
def signingPlanFrame : List UInt8 := "DREGG/NATIVE-HOST/SIGNING-PLAN/v6".toUTF8.toList

/-- Version 4: receipts bind `(worldRoot, height)` (not the whole-image
boundary); a refusal carries its closed `RefusalReason` and, for a law
refusal, the failing clause (`LawLeaf`). Version-1, version-2 and version-3
outcomes refuse; none is reinterpreted. -/
def outcomeFrame : List UInt8 := "DREGG/NATIVE-HOST/OUTCOME/v4".toUTF8.toList

end Minidregg.Compiler.NativeHostCodec

namespace Minidregg.Compiler.NativeObservationCodec

/-- v7 retains the full docuverse query sum and signs roster-bound install drafts. -/
def intentFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-INTENT/v7".toUTF8.toList

/-- The union of document views, committed clock fields, and the early intent
signature. v10 adds the roster-bound draft encoding without changing tuple order. -/
def challengeFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-CHALLENGE/v10".toUTF8.toList

def signedFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-SIGNED/v10".toUTF8.toList

end Minidregg.Compiler.NativeObservationCodec

namespace Minidregg.Kernel.PolicyInstallReceiver

def ingressFrame : List UInt8 := "DREGG/POLICY/INSTALL/SIGNED-INGRESS".toUTF8.toList ++ [2]

end Minidregg.Kernel.PolicyInstallReceiver

namespace Minidregg.Kernel.DeclaredResourceController

/-- Version 8 unifies observe-only reads, world-kind mutations and typed
audience epoch/roster bindings. Both prior v7 shapes refuse. -/
def commandFrame : List UInt8 := "DREGG/RESOURCE/TRANSACTION".toUTF8.toList ++ [8]

end Minidregg.Kernel.DeclaredResourceController
