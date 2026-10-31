/- Host compatibility surface; shared continuity implementation lives below Host. -/
module

public import Compiler.ReceiptContinuityIO

@[expose] public section

namespace Minidregg.Host.ReceiptContinuity
export Minidregg.Compiler.ReceiptContinuityIO (Request RootWitness systemSiblings systemSiblings_length identityOf current recent remember rememberWitness atHeight atPoint produce parseRequest parseExtension identityJson pointJson extensionJson challengePointJson verifyJson serve)
end Minidregg.Host.ReceiptContinuity
