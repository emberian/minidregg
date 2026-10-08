import Compiler.DurableHistoryStoreCore
import Compiler.DurableReceiverIO

namespace Minidregg.Compiler.DurableHistoryStore

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent (TransactionId StableNullifier DataSnapshot)
open Minidregg.Kernel.DurableReceiver (IntentRecord Seed replay)
open Minidregg.Kernel.DurableCheckpoint (State)
open Minidregg.Compiler.DurableHistory
open Minidregg.Compiler.DurableHistoryReader
open Minidregg.Compiler.DurableReceiverIO (Transport Loaded indexRows)
open Minidregg.Compiler.DurableCheckpointCodec (recordFrame chainAfter openSealed MacKey)

set_option autoImplicit false

/-- **A Reader of a portable image** (a foreign accepted prefix that arrives as
bytes, with no Store of its own). The image is written into the EMPTY Store
`transport` names (`DurableReceiverIO.writeImage`: its seed, then each record
appended through the one receive path and read back) and read back as a Reader of
a SCRATCH Store (`StoreIdentity.ofScratch`: never equal to an opened Store,
`StoreIdentity.ofScratch_ne_ofOpen`; never an `Opening`, `Opening.not_scratch`).

What its head is bound to: the chain recomputed from the image's own bytes (each
append advances it from the deployment's log start), MAC'd under the scratch
Store's fresh key, and nothing else. That MAC authenticates NOTHING about the
foreign data: the key was made here, for this copy. The image is authenticated
only by the commitment check below (and by whatever re-admission its caller runs
over the Reader); never read the scratch Store's MAC as evidence. So before any Reader is returned the image is
checked against the commitment its evidence carries: the image's height and its
world root (`commitment.rootOf`) must be the carried ones, else it is refused by
name; and the written Store's log start must be `logStart` (the deployment's, for
this image's seed). The caller owns the Store's directory and its lifetime (the
Reader reads it on every query). -/
def scratchReader (transport : Transport) (rootBytes : List UInt8 → Digest)
    (image : Minidregg.Kernel.DurableReceiver.Image) (logStart : Digest) (commitment : Commitment) :
    IO (Except String ((store : StoreIdentity) × Reader rootBytes store)) := do
  if image.accepted.length ≠ commitment.height then
    return .error s!"scratch Store: the image's height {image.accepted.length} is not the carried height {commitment.height}"
  if commitment.rootOf image ≠ commitment.worldRoot then
    return .error s!"scratch Store: the image's world root at height {commitment.height} is not the carried commitment"
  match ← DurableReceiverIO.writeImage transport rootBytes image with
  | .error detail => return .error detail
  | .ok written =>
      if written.logStart ≠ logStart then
        return .error "scratch Store: its log start is not the image's (another deployment's transport)"
      readerForScratch transport rootBytes written

end Minidregg.Compiler.DurableHistoryStore
