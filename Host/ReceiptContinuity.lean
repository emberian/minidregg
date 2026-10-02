/- Public hash-only history extension, produced from the same loaded receiver
image used by ordinary signed observations. No journal payload is disclosed. -/
import Kernel.ReceiptContinuity
import Kernel.NativeHostContext
import Lean

namespace Minidregg.Host.ReceiptContinuity

open Lean
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.ReceiptContinuity
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.WorldRoot
open Minidregg.Kernel.WorldRootCache

set_option autoImplicit false

structure Request where
  query : Query
  /-- Previously verified client-held opening; avoids historical reconstruction
  on every ordinary read. It is checked, not trusted merely because supplied. -/
  witness : Option (Digest × List Digest)

structure RootWitness where
  point : Point
  chain : Digest
  siblings : List Digest

/-- Read cached sibling hashes in O(tree depth), without rehashing the world. -/
def cachedSiblings : DeployedTree → List Bool → List Digest
  | _, [] => []
  | tree, bit :: rest =>
      let (left, right) := tree.children
      let sibling := if bit then left else right
      sibling.digest deployed deployedEmpties rest.length ::
        cachedSiblings (if bit then right else left) rest

theorem cachedSiblings_length (tree : DeployedTree) (bits : List Bool) :
    (cachedSiblings tree bits).length = bits.length := by
  induction bits generalizing tree with
  | nil => rfl
  | cons bit rest ih => simp [cachedSiblings, ih]

def identityOf (config : NativeHost.Config) : Identity :=
  ⟨config.deployment.domain, config.profile.semantics, config.expectedSeed⟩

def current (loaded : NativeHost.Durable) : RootWitness :=
  ⟨⟨loaded.height, loaded.worldRoot⟩, loaded.chain,
    cachedSiblings loaded.roots.tree (deployed.ix .system)⟩

/-- Cache only already loaded roots, so the extra proof request for a just-issued
challenge need not replay history if the clock ticked in between. Bounded and
non-authoritative: every response is still cryptographically checked. -/
initialize recent : IO.Ref (List (Identity × RootWitness)) ← IO.mkRef []

def remember (config : NativeHost.Config) (loaded : NativeHost.Durable) : IO Unit := do
  let value := current loaded
  let identity := identityOf config
  recent.modify fun entries =>
    ((identity, value) :: entries.filter (fun entry =>
      !(entry.1 == identity && entry.2.point == value.point))).take 64

/-- Historical fallback uses the canonical prefix executor and the same world
root entries as normal receiving. No alleged root supplied by a client is used
as a producer's computed root. -/
def atHeight (loaded : NativeHost.Durable) (height : Nat) : Except String RootWitness := do
  if height > loaded.height then throw "continuity target is beyond the loaded head"
  if height = loaded.height then return current loaded
  let some snapshot := loaded.atPrefix height
    | throw "continuity historical prefix did not replay"
  let image := loaded.prefixImage height
  let chain := DurableCheckpointCodec.chainAfter loaded.logStart image.accepted
  let roots := DurableReceiverIO.RootCache.ofEntries (DurableReceiverIO.entriesOf image snapshot chain)
  return ⟨⟨height, roots.root⟩, chain, cachedSiblings roots.tree (deployed.ix .system)⟩

def atPoint (config : NativeHost.Config) (loaded : NativeHost.Durable)
    (point : Point) : IO (Except String RootWitness) := do
  if point.height > loaded.height then return .error "continuity target is beyond the loaded head"
  let cache ← recent.get
  match cache.find? (fun entry => entry.1 == identityOf config && entry.2.point == point) with
  | some entry => return .ok entry.2
  | none =>
      return do
        let witness ← atHeight loaded point.height
        if witness.point ≠ point then throw "continuity root differs at the requested height"
        return witness

/-- The suffix comes from accepted records of the actual loaded image, and the
end chain is opened through the exact requested world root. Hash collisions are
the cryptographic limit; source-asserted height/digest claims alone never pass. -/
def produce (config : NativeHost.Config) (loaded : NativeHost.Durable)
    (request : Request) : IO (Except String Extension) := do
  let query := request.query
  if query.identity ≠ identityOf config then return .error "continuity deployment identity differs"
  if query.start.height > query.target.height then return .error "continuity query runs backwards"
  if query.target.height > loaded.height then return .error "continuity target is beyond the loaded head"
  let target ← atPoint config loaded query.target
  let .ok _ := target | return .error "continuity target root differs from the loaded history"
  let start ← match request.witness with
    | some (chain, siblings) => pure (.ok ⟨query.start, chain, siblings⟩)
    | none => atPoint config loaded query.start
  let .ok start := start | return .error "continuity starting root differs from the loaded history"
  let endHeight := min (query.start.height + maxSuffix) query.target.height
  let ending := if endHeight = query.target.height then target else atHeight loaded endHeight
  let .ok ending := ending | return .error "continuity intermediate prefix unavailable"
  let suffix := ((loaded.image.accepted.drop query.start.height).take
    (endHeight - query.start.height)).map DurableCheckpointCodec.recordDigest
  let extension : Extension := ⟨identityOf config, start.point, ending.point,
    start.chain, ending.chain, start.siblings, ending.siblings, suffix,
    decide (endHeight = query.target.height)⟩
  match verify query extension with
  | .error message => return .error message
  | .ok _ => return .ok extension

private def field (value : Json) (name : String) : Except String Json := value.getObjVal? name

private def natural (value : Json) : Except String Nat := do
  let text ← value.getStr?
  if text.length > 80 then throw "continuity integer exceeds bound"
  let some number := text.toNat? | throw "continuity integer must be decimal"
  if toString number ≠ text then throw "continuity integer is not canonical decimal"
  return number

private def digest (value : Json) : Except String Digest := do
  let number ← natural value
  if number ≥ 2^256 then throw "continuity digest exceeds 256 bits"
  return ⟨number⟩

private def digests (value : Json) (limit : Nat) : Except String (List Digest) := do
  let values ← value.getArr?
  if values.size > limit then throw "continuity digest list exceeds bound"
  values.toList.mapM digest

private def parseIdentity (value : Json) : Except String Identity := do
  if (← (← field value "algorithm").getStr?) ≠ algorithm then
    throw "unsupported continuity algorithm"
  return ⟨← digest (← field value "domain"), ← digest (← field value "semantics"),
    ← digest (← field value "expectedSeed")⟩

private def parsePoint (value : Json) : Except String Point := do
  return ⟨← natural (← field value "height"), ← digest (← field value "worldRoot")⟩

def parseRequest (value : Json) : Except String Request := do
  let identity ← parseIdentity (← field value "identity")
  let fromJson ← field value "from"
  let anchor ← if fromJson == Json.null then pure none else some <$> parsePoint fromJson
  let target ← parsePoint (← field value "target")
  let witness ← match value.getObjVal? "fromChain", value.getObjVal? "fromSiblings" with
    | .error _, .error _ => pure none
    | .ok chain, .ok siblings => some <$> (do return (← digest chain, ← digests siblings 256))
    | _, _ => throw "continuity starting witness is incomplete"
  return ⟨⟨identity, anchor, target⟩, witness⟩

def parseExtension (value : Json) : Except String Extension := do
  return ⟨← parseIdentity (← field value "identity"), ← parsePoint (← field value "from"),
    ← parsePoint (← field value "to"), ← digest (← field value "startChain"),
    ← digest (← field value "endChain"), ← digests (← field value "fromSiblings") 256,
    ← digests (← field value "toSiblings") 256, ← digests (← field value "suffix") maxSuffix,
    ← (← field value "complete").getBool?⟩

private def decimal (value : Nat) : Json := toJson (toString value)

def identityJson (identity : Identity) : Json := Json.mkObj [
  ("algorithm", toJson algorithm), ("domain", decimal identity.domain.value),
  ("semantics", decimal identity.semantics.value), ("expectedSeed", decimal identity.expectedSeed.value)]

def pointJson (point : Point) : Json := Json.mkObj [
  ("height", decimal point.height), ("worldRoot", decimal point.worldRoot.value)]

private def digestsJson (values : List Digest) : Json := toJson (values.map fun value => toString value.value)

def extensionJson (extension : Extension) : Json := Json.mkObj [
  ("identity", identityJson extension.identity), ("from", pointJson extension.startPoint),
  ("to", pointJson extension.endPoint), ("startChain", decimal extension.startChain.value),
  ("endChain", decimal extension.endChain.value), ("fromSiblings", digestsJson extension.fromSiblings),
  ("toSiblings", digestsJson extension.toSiblings), ("suffix", digestsJson extension.suffix),
  ("complete", toJson extension.complete)]

/-- Observation challenges name the absolute admission height, while system
leaves and receipts count accepted records from zero. Normalize through the
source-owned config, checking the challenge's deployment and semantic identity. -/
def challengePointJson (config : NativeHost.Config) (value : Json) : Except String Json := do
  let domain ← digest (← field value "domain")
  let semantics ← digest (← field value "semantics")
  if domain ≠ config.deployment.domain ∨ semantics ≠ config.profile.semantics then
    throw "continuity challenge deployment identity differs"
  let height ← natural (← field value "height")
  if height < config.genesisHeight then throw "continuity challenge height is below genesis"
  let root ← digest (← field value "worldRoot")
  return pointJson ⟨height - config.genesisHeight, root⟩

/-- Pure local client verifier; it does not contact or open the server's Store. -/
def verifyJson (config : NativeHost.Config) (requestJson responseJson : Json) : Except String Json := do
  let request ← parseRequest requestJson
  if request.query.identity ≠ identityOf config then throw "continuity verifier deployment identity differs"
  let extension ← parseExtension responseJson
  let point ← verify request.query extension
  return Json.mkObj [("to", pointJson point), ("complete", toJson extension.complete),
    ("chain", decimal extension.endChain.value), ("siblings", digestsJson extension.toSiblings)]

def serve (config : NativeHost.Config) (loaded : NativeHost.Durable)
    (payload : List UInt8) : IO (Except String (List UInt8)) := do
  let some text := String.fromUTF8? payload.toByteArray
    | return .error "continuity request is not UTF-8"
  match Json.parse text >>= parseRequest with
  | .error message => return .error message
  | .ok request =>
      match ← produce config loaded request with
      | .error message => return .error message
      | .ok extension => return .ok ((extensionJson extension).compress.toUTF8.toList)

end Minidregg.Host.ReceiptContinuity
