/- Host compatibility surface; shared continuity implementation lives below Host. -/
import Compiler.ReceiptContinuityIO
namespace Minidregg.Host.ReceiptContinuity
export Minidregg.Compiler.ReceiptContinuityIO (Request RootWitness systemSiblings systemSiblings_length identityOf current recent remember atHeight atPoint produce parseRequest parseExtension identityJson pointJson extensionJson challengePointJson verifyJson serve)
end Minidregg.Host.ReceiptContinuity
