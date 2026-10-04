/- Source-owned protected content coordinates retain ordinary write protection
independently of any particular execution language or checkpoint codec. -/
import Compiler.ContentControlFrame
namespace Minidregg.Kernel.ProtectedContentGate
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false

def ordinaryGate {rootBytes : List UInt8 → Minidregg.Theory.TypedAuthorization.Digest}
    (pin : Minidregg.Compiler.ContentControlFrame.Pin)
    (_snapshot : DataSnapshot rootBytes) (intent : DataIntent rootBytes) :
    Except RejectReason Unit :=
  if intent.writes.any (fun write => write.cellId == pin.cell)
  then .error (.durable .transactionConflict) else .ok ()

end Minidregg.Kernel.ProtectedContentGate
