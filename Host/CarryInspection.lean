/- Public verifier for an explicitly authorized external carry edge.
It verifies canonical source-owned signing bytes, preexisting operator authority,
both endpoint openings and artifact pins. It receives no private Store image.
The operator-local CarriedSegment receiver performs semantic source audit and
new-profile state validation before the detached edge is signed. -/
import Kernel.CarriedSegment
import Host.ReceiptContinuity
import Compiler.CredentialSignatureIO
import Compiler.RetainedArtifactIO

namespace Minidregg.Host.CarryInspection

open Lean
open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.CarriedSegment
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

private def field (value : Json) (name : String) : Except String Json := value.getObjVal? name
private def stringField (value : Json) (name : String) : Except String String :=
  (field value name).bind Json.getStr?

private def natural (value : Json) : Except String Nat := do
  let text ← value.getStr?
  if text.length > 80 then throw "carry integer exceeds bound"
  let some number := text.toNat? | throw "carry integer must be decimal"
  if toString number != text then throw "carry integer is not canonical decimal"
  return number

private def digestValue (value : Json) : Except String Digest := do
  let number ← natural value
  if number ≥ 2^256 then throw "carry digest exceeds 256 bits"
  return ⟨number⟩

private def hexNibble (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

private def decodeHex : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
      let hi ← hexNibble a
      let lo ← hexNibble b
      let tail ← decodeHex rest
      return UInt8.ofNat (hi * 16 + lo) :: tail
  | _ => none

def encodeHex (bytes : List UInt8) : String :=
  let digit := fun n : Nat => Char.ofNat (if n < 10 then '0'.toNat + n else 'a'.toNat + n - 10)
  String.ofList (bytes.flatMap fun byte => [digit (byte.toNat / 16), digit (byte.toNat % 16)])

private def hex (value : Json) (length : Nat) : Except String (List UInt8) := do
  let text ← value.getStr?
  if text.length != 2 * length then throw "carry hexadecimal byte length differs"
  let some bytes := decodeHex text.toList | throw "carry hex is not canonical lowercase"
  return bytes

def parseIdentity (value : Json) : Except String Identity := do
  if (← stringField value "algorithm") != ReceiptContinuity.algorithm then
    throw "carry identity algorithm differs"
  return ⟨← digestValue (← field value "domain"), ← digestValue (← field value "semantics"),
    ← digestValue (← field value "expectedSeed")⟩

private def point (value : Json) : Except String Point := do
  return ⟨← natural (← field value "height"), ← digestValue (← field value "worldRoot"),
    ← digestValue (← field value "logChain")⟩

private def capsule (value : Json) : Except String CapsulePins := do
  return ⟨← hex (← field value "host") 32, ← hex (← field value "storageHelper") 32,
    ← hex (← field value "signatureVerifier") 32, ← hex (← field value "configuration") 32,
    ← hex (← field value "profile") 32⟩

def parseBody (value : Json) : Except String Body := do
  return ⟨← parseIdentity (← field value "source"), ← point (← field value "cut"),
    ← digestValue (← field value "sourceImageDigest"), ← capsule (← field value "sourceCapsule"),
    ← parseIdentity (← field value "target"), ← capsule (← field value "targetCapsule"),
    ← natural (← field value "transformation"), ← digestValue (← field value "writesDigest"),
    ← digestValue (← field value "originIndexDigest"), ← hex (← field value "operatorPublicKey") 32,
    ← hex (← field value "nonce") 32⟩

private def siblings (value : Json) : Except String (List Digest) := do
  let values ← value.getArr?
  if values.size != 256 then throw "carry opening must have exactly 256 siblings"
  values.toList.mapM digestValue

def parseSeal (value : Json) : Except String EdgeSeal := do
  if (← stringField value "algorithm") != "minidregg-carry-edge-v1" then
    throw "unsupported carry edge"
  return ⟨← parseBody (← field value "body"), ← point (← field value "newStart"),
    ← siblings (← field value "sourceSiblings"), ← siblings (← field value "targetSiblings"),
    ← hex (← field value "signature") 64⟩

private def decimal (value : Nat) : Json := .str (toString value)

def identityJson (value : Identity) : Json := Json.mkObj [
  ("algorithm", .str ReceiptContinuity.algorithm), ("domain", decimal value.domain.value),
  ("semantics", decimal value.semantics.value), ("expectedSeed", decimal value.genesis.value)]

def pointJson (value : Point) (path : List Digest) : Json := Json.mkObj [
  ("height", decimal value.height), ("worldRoot", decimal value.worldRoot.value),
  ("logChain", decimal value.logChain.value),
  ("systemSiblings", toJson (path.map fun item => toString item.value))]


def capsuleJson (value : CapsulePins) : Json := Json.mkObj [
  ("host", .str (encodeHex value.host)), ("storageHelper", .str (encodeHex value.storageHelper)),
  ("signatureVerifier", .str (encodeHex value.signatureVerifier)),
  ("configuration", .str (encodeHex value.configuration)), ("profile", .str (encodeHex value.profile))]

private def barePointJson (value : Point) : Json := Json.mkObj [
  ("height", decimal value.height), ("worldRoot", decimal value.worldRoot.value),
  ("logChain", decimal value.logChain.value)]

def bodyJson (value : Body) : Json := Json.mkObj [
  ("source", identityJson value.source), ("cut", barePointJson value.cut),
  ("sourceImageDigest", decimal value.sourceImage.value), ("sourceCapsule", capsuleJson value.sourceCapsule),
  ("target", identityJson value.target), ("targetCapsule", capsuleJson value.targetCapsule),
  ("transformation", decimal value.transformation), ("writesDigest", decimal value.writes.value),
  ("originIndexDigest", decimal value.originIndex.value),
  ("operatorPublicKey", .str (encodeHex value.operatorPublicKey)), ("nonce", .str (encodeHex value.nonce))]

def edgeJson (value : EdgeSeal) : Json := Json.mkObj [
  ("algorithm", .str "minidregg-carry-edge-v1"), ("body", bodyJson value.body),
  ("newStart", barePointJson value.targetStart),
  ("sourceSiblings", toJson (value.sourceSiblings.map fun item => toString item.value)),
  ("targetSiblings", toJson (value.targetSiblings.map fun item => toString item.value)),
  ("signature", .str (encodeHex value.signature))]

open Minidregg.Compiler.RetainedArtifactIO

private def liftResult {α : Type} (value : Except String α) : IO α := IO.ofExcept value

private partial def boundedBytes (input : IO.FS.Handle) (limit : Nat)
    (acc : ByteArray := ByteArray.empty) : IO ByteArray := do
  let chunk ← input.read (min 65536 (limit + 1 - acc.size)).toUSize
  if chunk.isEmpty then return acc
  let next := acc ++ chunk
  if next.size > limit then throw (IO.userError "carry edge exceeds bound")
  boundedBytes input limit next

private def readEdgeText (path : System.FilePath) : IO String := do
  let bytes ← IO.FS.withFile path .read fun input => boundedBytes input 1048576
  let some text := String.fromUTF8? bytes | throw (IO.userError "carry edge is not UTF-8")
  return text

/-- Exact CLI request contract. All trust pins are client-owned request fields,
never imported from the untrusted edge body. The caller keeps its custody lock
while this runs, verifies old-anchor -> old-cut continuity, and atomically adopts
only the verified new start after the target endpoint proves it or an extension. -/
def verifyRequestWithIdentity (expected : Identity) (request : Json) : IO (Except String Json) := do
  try
    let requested ← liftResult (parseIdentity (← liftResult (field request "oldIdentity")))
    if requested != expected then return .error "carry verifier source identity differs from trusted profile"
    let operator ← liftResult (hex (← liftResult (field request "operatorPublicKey")) 32)
    let registryString ← liftResult (stringField request "sourceCapsulePath")
    let registry ← IO.FS.realPath registryString
    let pins ← liftResult (field request "sourceCapsulePins")
    let pinnedIdentity ← liftResult (parseIdentity (← liftResult (field pins "identity")))
    if pinnedIdentity != expected then return .error "registered client capsule identity differs"
    for (name, pin) in [("verifier", "verifierSha256"), ("original-config.json", "configSha256"),
        ("profile.json", "profileSha256"), ("signature-verifier", "signatureVerifierSha256")] do
      let path := registry / name
      let resolved ← IO.FS.realPath path
      if resolved != path then return .error "client carry capsule is not a retained regular path"
      let hash ← liftResult (stringField pins pin)
      liftResult (← checkedFile path hash)
    let signaturePath ← liftResult (stringField pins "signatureVerifierPath")
    if signaturePath != (registry / "signature-verifier").toString then
      return .error "carry signature verifier escapes retained client capsule"
    let edgePath ← liftResult (stringField request "edgeManifestPath")
    let edgeText ← readEdgeText edgePath
    let edge ← liftResult (Json.parse edgeText >>= parseSeal)
    let target ← liftResult (checkPublic expected operator edge)
    -- Pin the new locally selected runtime and exact configuration before
    -- invoking it or publishing settings; never execute a path from the edge.
    let targetVerifier ← liftResult (stringField request "newVerifierPath")
    liftResult (← checkedFile targetVerifier (encodeHex edge.body.targetCapsule.host))
    let targetConfig ← liftResult (stringField request "newConfigPath")
    liftResult (← checkedFile targetConfig (encodeHex edge.body.targetCapsule.configuration))
    match ← CredentialSignatureIO.verify ⟨signaturePath⟩ operator edge.signingBytes edge.signature with
    | .error error => return .error s!"carry signature verifier failed: {repr error}"
    | .ok false => return .error "carry operator signature invalid"
    | .ok true =>
        let described ← IO.Process.output { cmd := targetVerifier, args := #[targetConfig, "profile"] }
        if described.exitCode != 0 || described.stderr != "" then
          return .error "authorized target runtime cannot describe its pinned profile"
        let profile ← liftResult (Json.parse described.stdout)
        let targetIdentity : Identity := ⟨← liftResult (digestValue (← liftResult (field profile "domain"))),
          ← liftResult (digestValue (← liftResult (field profile "semantics"))),
          ← liftResult (digestValue (← liftResult (field profile "expectedSeed")))⟩
        if targetIdentity != edge.body.target then return .error "actual target profile differs from carry edge"
        let profilePin ← IO.FS.withTempDir fun directory => do
          let path := directory / "profile.json"
          IO.FS.writeFile path described.stdout
          checkedFile path (encodeHex edge.body.targetCapsule.profile)
        liftResult profilePin
        return .ok (Json.mkObj [
          ("algorithm", .str "minidregg-carry-edge-v1"),
          ("oldIdentity", identityJson edge.body.source),
          ("oldCut", pointJson edge.body.cut edge.sourceSiblings),
          ("newIdentity", identityJson edge.body.target),
          ("newStart", pointJson target edge.targetSiblings),
          ("bodyDigest", decimal edge.body.id.value),
          ("originIndexDigest", decimal edge.body.originIndex.value),
          ("operatorPublicKey", .str (encodeHex operator)),
          ("targetVerifierDigest", .str (encodeHex edge.body.targetCapsule.host)),
          ("trust", .str "explicit-authorized-external-handoff")])
  catch error => return .error s!"carry edge refused: {error}"


/-- Normal Host callers still bind the source to their compiled configuration. -/
def verifyRequest (config : NativeHost.Config) (request : Json) : IO (Except String Json) :=
  verifyRequestWithIdentity
    ⟨config.deployment.domain, config.profile.semantics, config.expectedSeed⟩ request

/-- Bootstrap for a separately installed generic verifier. Its old identity
comes only from the client's preexisting capsule, not from the edge or the
target runtime. OLD_CONFIG must be the exact independently registered config.
The old trusted executable re-describes that config before any target runs. -/
def registeredSourceIdentity (configuration : System.FilePath) (request : Json) :
    IO (Except String Identity) := do
  try
    let registryString ← liftResult (stringField request "sourceCapsulePath")
    let registry ← IO.FS.realPath registryString
    let pins ← liftResult (field request "sourceCapsulePins")
    for (name, pin) in [("verifier", "verifierSha256"), ("original-config.json", "configSha256"),
        ("profile.json", "profileSha256"), ("signature-verifier", "signatureVerifierSha256")] do
      let path := registry / name
      let resolved ← IO.FS.realPath path
      if resolved != path then return .error "registered verifier capsule path changed"
      liftResult (← checkedFile path (← liftResult (stringField pins pin)))
    liftResult (← checkedFile configuration (← liftResult (stringField pins "configSha256")))
    let signaturePath ← liftResult (stringField pins "signatureVerifierPath")
    if signaturePath != (registry / "signature-verifier").toString then
      return .error "registered signature verifier escapes capsule"
    let profileText ← readEdgeText (registry / "profile.json")
    let profile ← liftResult (Json.parse profileText)
    let identity : Identity := ⟨← liftResult (digestValue (← liftResult (field profile "domain"))),
      ← liftResult (digestValue (← liftResult (field profile "semantics"))),
      ← liftResult (digestValue (← liftResult (field profile "expectedSeed")))⟩
    let pinned ← liftResult (parseIdentity (← liftResult (field pins "identity")))
    let requested ← liftResult (parseIdentity (← liftResult (field request "oldIdentity")))
    if identity != pinned || identity != requested then
      return .error "registered old verifier identity differs from client custody"
    let described ← IO.Process.output {
      cmd := (registry / "verifier").toString
      args := #[(registry / "original-config.json").toString, "profile"] }
    if described.exitCode != 0 || described.stderr != "" || described.stdout != profileText then
      return .error "old trusted verifier no longer describes its registered profile"
    return .ok identity
  catch error => return .error s!"registered old verifier refused: {error}"

/-- The profile command performs no edge lookup and executes no target code. -/
def registeredVerifierProfile (configuration : System.FilePath) (request : Json) :
    IO (Except String Json) := do
  match ← registeredSourceIdentity configuration request with
  | .error detail => return .error detail
  | .ok identity =>
    match field request "sourceCapsulePins" with
    | .error detail => return .error detail
    | .ok pins => return .ok (Json.mkObj [
      ("algorithm", .str "minidregg-carry-verifier-v1"),
      ("identity", identityJson identity),
      ("sourceCapsulePins", pins),
      ("edgeAlgorithm", .str "minidregg-carry-edge-v1")])

def verifyRegisteredRequest (configuration : System.FilePath) (request : Json) :
    IO (Except String Json) := do
  match ← registeredSourceIdentity configuration request with
  | .error detail => return .error detail
  | .ok identity => verifyRequestWithIdentity identity request

end Minidregg.Host.CarryInspection
