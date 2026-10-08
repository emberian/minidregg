/- Source-owned native protocol frame bytes shared by the actual codecs and
runtime identity. This module deliberately imports no controller or profile:
wire epochs can be committed without a codec → profile → codec import cycle.
Existing namespaces are retained so every encoder/decoder uses these same
constants; retired frame fixtures remain next to their refusal proofs. -/
import Theory.PersistedCodecTags
import Init

namespace Minidregg.Compiler.NativeHostCodec

/-- Version 4 (K-RENOUNCE): the call gains `renounce`; a v3 call refuses. -/
def callFrame : List UInt8 := Minidregg.Theory.PersistedCodecTags.nativeprotocolframes_callframe_4cd7d6ce.toUTF8.toList

/-- Version 5 binds the complete roster witness into the authoring intent. -/
def draftFrame : List UInt8 := Minidregg.Theory.PersistedCodecTags.nativeprotocolframes_draftframe_7af8fd37.toUTF8.toList

/-- Version 6 carries the roster-bound finalized draft. -/
def signingPlanFrame : List UInt8 := Minidregg.Theory.PersistedCodecTags.nativeprotocolframes_signingplanframe_6d288d35.toUTF8.toList

/-- Version 5 adds the committed charged terminal disposition and its canonical
typed objective-activity cause bytes. Older outcomes refuse; none is
reinterpreted. -/
def outcomeFrame : List UInt8 := Minidregg.Theory.PersistedCodecTags.nativeprotocolframes_outcomeframe_11a5eba7.toUTF8.toList

end Minidregg.Compiler.NativeHostCodec

namespace Minidregg.Compiler.NativeObservationCodec

/-- v7 retains the full docuverse query sum and signs roster-bound install drafts. -/
def intentFrame : List UInt8 := Minidregg.Theory.PersistedCodecTags.nativeprotocolframes_intentframe_ad208d3e.toUTF8.toList

/-- The union of document views, committed clock fields, and the early intent
signature. v10 adds the roster-bound draft encoding without changing tuple order. -/
def challengeFrame : List UInt8 := Minidregg.Theory.PersistedCodecTags.nativeprotocolframes_challengeframe_5b33ffe4.toUTF8.toList

def signedFrame : List UInt8 := Minidregg.Theory.PersistedCodecTags.nativeprotocolframes_signedframe_c007c7c1.toUTF8.toList

end Minidregg.Compiler.NativeObservationCodec

namespace Minidregg.Kernel.PolicyInstallReceiver

def ingressFrame : List UInt8 := Minidregg.Theory.PersistedCodecTags.nativeprotocolframes_ingressframe_70a174b6

end Minidregg.Kernel.PolicyInstallReceiver

namespace Minidregg.Kernel.DeclaredResourceController

/-- Version10 adds authenticated whole-definition observe-only tag7 and exact
canonical noun constructor output. Older receiving frames refuse reinterpretation. -/
def commandFrame : List UInt8 := Minidregg.Theory.PersistedCodecTags.nativeprotocolframes_commandframe_c43cf00a

end Minidregg.Kernel.DeclaredResourceController
