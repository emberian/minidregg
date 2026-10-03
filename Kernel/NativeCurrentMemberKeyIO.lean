/- Closed source readback effect. No synthetic Durable supplied by a caller. -/
import Kernel.NativeCurrentMemberKey
namespace Minidregg.Kernel.NativeCurrentMemberKeyIO
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.NativeCurrentMemberKey
set_option autoImplicit false
structure Request where
  point : Point
  member : SubjectId
  room : Nat
  keysCell : Nat
  payload : List UInt8

def requestStream : StreamCodec Request :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat bytesStream)))))
    (fun r => (r.point.height,r.point.root,r.member,r.room,r.keysCell,r.payload))
    (fun (h,w,m,r,k,p) => ⟨⟨h,w⟩,m,r,k,p⟩) (by intro r; cases r with | mk point member room keysCell payload => cases point; rfl)
def requestFrame : List UInt8 := "DREGG.CURRENT.RECIPIENT.QUERY".toUTF8.toList ++ [1]
def requestBytes (r : Request) : List UInt8 := requestFrame ++ requestStream.encode r

def decode (bytes : List UInt8) : Option Request := do
  if bytes.length > 4096 || bytes.take requestFrame.length != requestFrame then none else
  let request ← requestStream.toLawful.decode (bytes.drop requestFrame.length)
  if requestBytes request = bytes then some request else none

structure Readback (config : Config) (request : Request) where
  private mk ::
  target : Durable
  claim : CurrentRecipientRecord.Claim
  payloadExact : CurrentRecipientRecord.decode request.member request.payload = some claim
  scopeExact : claim.room = request.room ∧ claim.keysCell = request.keysCell
  authenticated : Authenticated config target request.point claim

/-- Reads the deployment's actual protected transport then audits/validates it.
The independent locked client supplies the point; a packet cannot provide a
Store, native helper, mutable key map or positive verification callback. -/
def authenticate (config : Config) (request : Request) : IO (Except String (Readback config request)) := do
  match payloadExact : CurrentRecipientRecord.decode request.member request.payload with
  | none => return .error "invalid current recipient record"
  | some claim =>
    if scopeExact : claim.room = request.room ∧ claim.keysCell = request.keysCell then
      match ← DurableReceiverIO.load config.physicalTransport ResourceBirthCodec.rootBytes with
      | .error detail => return .error detail
      | .ok target =>
        match ← NativeCurrentMemberKey.authenticate config target request.point claim with
        | .error detail => return .error detail
        | .ok token => return .ok ⟨target,claim,payloadExact,scopeExact,token⟩
    else return .error "recipient record scope mismatch"

/-- Response is an exact CLAIM outside the closed pinned-local verifier effect.
It carries the whole input/context, never a free-standing current pubkey. No
native authorization or Authenticated constructor deserializes this output. -/
def Readback.response {config : Config} {request : Request} (r : Readback config request) : List UInt8 :=
  "DREGG.CURRENT.RECIPIENT.READBACK".toUTF8.toList ++ [1] ++
  bytesStream.encode (requestBytes request) ++ digestStream.encode config.deployment.domain ++
  digestStream.encode config.profile.semantics ++
  StreamCodec.nat.encode r.authenticated.selected.key.keyId ++
  StreamCodec.nat.encode r.authenticated.selected.key.keyEpoch ++
  bytesStream.encode r.authenticated.selected.key.publicKey

theorem readback_scoped {config : Config} {request : Request} (r : Readback config request) :
    r.claim.room = request.room ∧ r.claim.keysCell = request.keysCell := r.scopeExact
#assert_axioms readback_scoped
end Minidregg.Kernel.NativeCurrentMemberKeyIO
