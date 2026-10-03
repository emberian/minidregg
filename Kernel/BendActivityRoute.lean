/- Defense in depth for the explicit Activity application signature namespace.
NativeHostContext selects this gate only under the source-owned route edition.
All ordinary current-admission entry points must also call commandAllowed;
event3 classification alone cannot stop laundering through another wrapper.
-/
import Compiler.BendActivityNonce
import Kernel.DeclaredResourceController

namespace Minidregg.Kernel.BendActivityRoute
open Minidregg.Theory
open Minidregg.Compiler
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

def commandAllowed (command : Command) : Bool := BendActivityNonce.ordinaryAllowed command.nonce

/-- Typed event64 exceptions are admitted by their private actual phase token;
ordinary event3 cannot publish a marked command as if it had no phase guard. -/
def ordinaryEventGate {rootBytes : List UInt8 → TypedAuthorization.Digest}
    (intent : DataIntent rootBytes) : Except RejectReason Unit := do
  if intent.event.codecVersion != 3 then .ok () else do
    let some (_,_,signed) := decodeSignedBytes intent.event.canonicalBytes
      | .error (.durable .transactionConflict)
    let some command := commandCodec.decode signed.commandBytes
      | .error (.durable .transactionConflict)
    if commandAllowed command then .ok () else .error (.durable .transactionConflict)

#assert_axioms ordinaryEventGate
end Minidregg.Kernel.BendActivityRoute
