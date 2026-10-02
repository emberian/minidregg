/-
Strict JSON boundary for source paid status and source purchase/claim quotes.
Main must apply
its duplicate-key parser and 4096-byte raw-body limit before passing Json here.
Byte values and 32-byte little-endian digests are hexadecimal. Natural scalars
are canonical decimal strings. No signing, transfer, or pricing is done in JSON.
-/
import Kernel.NativeHostPayClaims
import Kernel.PayStarterAllowance
import Lean.Data.Json

namespace Minidregg.Host.PayClaims

open Lean
open Minidregg.Kernel
open Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

abbrev Result := Except String
private abbrev Object := Std.TreeMap.Raw String Json compare

def maxJsonResponseBytes : Nat := 8192

private def need {A : Type} (message : String) : Option A → Result A
  | none => .error message | some value => .ok value

private def object (required optional : List String) (json : Json) : Result Object := do
  let value ← json.getObj?.mapError (fun _ => "object expected")
  let actual := value.foldl (init := []) (fun names key _ => key :: names)
  for key in required do
    unless actual.contains key do throw s!"missing field: {key}"
  for key in actual do
    unless (required ++ optional).contains key do throw s!"unknown field: {key}"
  return value

private def field (obj : Object) (name : String) : Result Json :=
  need s!"missing field: {name}" (obj.get? name)

private def string (name : String) (value : Json) : Result String :=
  value.getStr?.mapError (fun _ => s!"{name}: string expected")

private def natural (name : String) (bits : Nat) (value : Json) : Result Nat := do
  let text ← string name value
  let number ← need s!"{name}: canonical unsigned decimal string expected" text.toNat?
  unless toString number = text do throw s!"{name}: canonical unsigned decimal string expected"
  unless number < 2 ^ bits do throw s!"{name}: unsigned {bits}-bit range exceeded"
  return number

private def nibble (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def bytes (name : String) (width : Nat) (value : Json) : Result (List UInt8) := do
  let text ← string name value
  let encoded := text.toUTF8
  unless encoded.size = 2 * width do throw s!"{name}: exactly {width} hexadecimal bytes expected"
  let mut output := ByteArray.empty
  for i in [:width] do
    let high ← need s!"{name}: hexadecimal expected" (nibble (Char.ofNat encoded[2 * i]!.toNat))
    let low ← need s!"{name}: hexadecimal expected" (nibble (Char.ofNat encoded[2 * i + 1]!.toNat))
    output := output.push (UInt8.ofNat (16 * high + low))
  return output.toList

private def hex (value : List UInt8) : Json := .str <| String.ofList <|
  value.flatMap fun byte =>
    let digits := "0123456789abcdef".toList
    [digits[byte.toNat / 16]?.getD '0', digits[byte.toNat % 16]?.getD '0']

private def decimal (value : Nat) : Json := .str (toString value)
private def digest (value : Digest) : Json := hex (PayEnrolMemoV2.encodeLE 32 value.value)
private def optional {A : Type} (render : A → Json) (value : Option A) : Json :=
  (value.map render).getD .null

/-- Check the actual compact UTF-8 output, not a guessed JSON expansion factor. -/
def boundedJson (value : Json) : Result Json :=
  if value.compress.toUTF8.size ≤ maxJsonResponseBytes then .ok value
  else .error "paid response exceeds 8192 UTF-8 bytes"

private def mode (value : Json) : Result PayEnrolClaim.Mode := do
  match ← string "mode" value with
  | "enrol" => return .enroll
  | "renew" => return .renew
  | _ => throw "mode: enrol or renew expected"

private def modeJson : PayEnrolClaim.Mode → Json
  | .enroll => "enrol" | .renew => "renew"

private def terms (obj : Object) : Result PayClaimQuote.Terms := do
  let economicMode ← mode (← field obj "mode")
  let weeks ← natural "weeks" 32 (← field obj "weeks")
  unless 0 < weeks do throw "weeks: must be positive"
  let starter ← natural "starter" 64 (← field obj "starter")
  let expiry ← natural "expiryHour" 64 (← field obj "expiryHour")
  return ⟨economicMode, weeks, starter, expiry⟩

def statusRequest (json : Json) : Result PayClaimStatus.Request := do
  let obj ← object ["identityKey"] ["signature", "originalRecipient"] json
  let identity ← bytes "identityKey" 32 (← field obj "identityKey")
  let locator ← match obj.get? "signature", obj.get? "originalRecipient" with
    | none, none => .ok none
    | some signature, some recipient => do
      return some ⟨← bytes "signature" 64 signature, ← bytes "originalRecipient" 32 recipient⟩
    | _, _ => .error "signature and originalRecipient must be supplied together"
  let request : PayClaimStatus.Request := ⟨identity, locator⟩
  (PayClaimStatus.decodeRequest (PayClaimStatus.requestCodec.encode request)).mapError
    (fun reason => s!"paid status request: {repr reason}")

def quoteRequest (json : Json) : Result PayClaimQuote.Request := do
  let obj ← json.getObj?.mapError (fun _ => "object expected")
  let kind ← string "kind" (← field obj "kind")
  let request ← match kind with
    | "purchase" => do
      let obj ← object ["kind", "identityKey", "sshKey", "mode", "weeks", "starter", "expiryHour"]
        ["freshNext"] json
      let identity ← bytes "identityKey" 32 (← field obj "identityKey")
      let ssh ← bytes "sshKey" 32 (← field obj "sshKey")
      let next ← match obj.get? "freshNext" with
        | none => .ok none
        | some value => do
          let raw ← bytes "freshNext" 32 value
          return some (⟨PayEnrolMemoV2.decodeLE raw⟩ : Digest)
      return Sum.inl (⟨identity, ssh, next, ← terms obj⟩ : PayClaimQuote.Purchase)
    | "claim" => do
      let obj ← object ["kind", "claimId", "mode", "weeks", "starter", "expiryHour", "nonce"] [] json
      let id ← bytes "claimId" 102 (← field obj "claimId")
      let nonce ← natural "nonce" 64 (← field obj "nonce")
      return Sum.inr (⟨id, ← terms obj, nonce⟩ : PayClaimQuote.ClaimRequest)
    | _ => .error "kind: purchase or claim expected"
  (PayClaimQuote.decodeRequest (PayClaimQuote.requestCodec.encode request)).mapError
    (fun reason => s!"paid quote request: {repr reason}")

private def pendingReason : PayEnrolClaim.PendingReason → Json
  | .termsStale => "termsStale" | .expired => "expired" | .authStale => "authStale"

private def freshness : Option PayChainTip.FreshnessReject → Json
  | none => "fresh"
  | some .missing => "missing"
  | some .malformed => "malformed"
  | some .future => "future"
  | some .stale => "stale"

private def asOf (tip : PayCell.ChainTip) : Json := .mkObj
  [("slot", decimal tip.slot), ("blockTime", decimal tip.blockTime), ("hour", decimal tip.hour)]

private def entryJson (value : PayClaimStatus.Entry) : Json := .mkObj
  [("subject", decimal value.subject), ("account", decimal value.account),
   ("sshBlob", hex value.sshBlob), ("index", optional decimal value.index),
   ("leaseUntil", decimal value.leaseUntil), ("enrolledSlot", decimal value.enrolledSlot)]

private def paymentJson : PayClaimStatus.Payment → Json
  | .notRequested => .mkObj [("state", "notRequested")]
  | .unobservedOrUnknownPositiveV1 => .mkObj [("state", "unobservedOrUnknownPositiveV1")]
  | .pendingV2 value => .mkObj [("state", "pendingV2"),
      ("amountAtomic", decimal value.amountAtomic), ("slot", decimal value.slot),
      ("index", decimal value.index), ("reason", pendingReason value.reason)]
  | .consumedV2 value => .mkObj [("state", "consumedV2"),
      ("amountAtomic", decimal value.amountAtomic), ("slot", decimal value.slot),
      ("index", decimal value.index), ("mode", modeJson value.mode),
      ("weeks", decimal value.requestedWeeks), ("mintedCredit", decimal value.mintedCredit),
      ("birthFee", decimal value.birthFee), ("membershipCredit", decimal value.membershipCredit),
      ("creditedRemainder", decimal value.creditedRemainder),
      ("pricingCommitment", digest value.pricingCommitment),
      ("authorization", match value.authorization with
        | .originalMemo => "originalMemo" | .acceptCurrentQuote => "acceptCurrentQuote"),
      ("acceptedRequest", optional (fun request => hex
        (PayEnrolClaim.acceptRequestCodec.encode request)) value.acceptedRequest)]
  | .journalV1Negative value => .mkObj [("state", "journalV1Negative"),
      ("amountAtomic", decimal value.amountAtomic), ("slot", decimal value.slot),
      ("index", decimal value.index), ("reasonCode", decimal value.reason.code),
      ("reason", .str s!"{repr value.reason}")]

private def statusJson (value : PayClaimStatus.Response) : Json := .mkObj
  [("type", "payStatus"), ("identityKey", hex value.request.identityKey),
   ("paymentLocator", optional (fun locator => .mkObj
      [("signature", hex locator.signature), ("originalRecipient", hex locator.originalRecipient),
       ("claimId", hex locator.id)]) value.request.payment),
   ("clockHour", decimal value.clockHour), ("asOf", optional asOf value.asOfChainTip),
   ("chainFreshness", freshness value.freshness),
   ("leaseState", match value.leaseState with
      | .active => "active" | .expired => "expired" | .notEnrolled => "notEnrolled"),
   ("entry", optional entryJson value.entry), ("payment", paymentJson value.payment)]

/-- Status remains useful when current chain evidence is stale. The source
returns explicit unknown-positive-v1 status rather than inventing success. -/
def statusLoadedJson (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (json : Json) : Result Json := do
  let request ← statusRequest json
  let responseBytes ← NativeHost.payClaimStatusLoaded config opened
    (PayClaimStatus.requestCodec.encode request)
  let response ← need "noncanonical source paid status response"
    (PayClaimStatus.responseCodec.decode responseBytes)
  boundedJson (statusJson response)


/-- Offline operator accounting is derived from one already genesis-walked image.
The caller must supply the opened image returned by NativeHostSession.startWalked. -/
def auditHeaderJson (config : NativeHost.Config) (opened : NativeHost.Opened config)
    : Result Json := do
  let ledger ← NativeHost.payLedgerLoaded config opened
  return .mkObj [("type", "payClaimAudit"),
    ("domain", decimal config.deployment.domain.value),
    ("semantics", decimal config.profile.semantics.value),
    ("expectedSeed", decimal config.expectedSeed.value),
    ("auditedHeight", decimal opened.durable.image.accepted.length),
    ("worldRoot", decimal opened.durable.worldRoot.value),
    ("ledger", .mkObj [("well", .str (toString ledger.well))])]

private def ownerJson (value : PayEnrolV2Decision.CurrentOwner) : Json := .mkObj
  [("identityKey", hex value.identityKey), ("authorizingKey", hex value.currentKey),
   ("authorityEpoch", decimal value.epoch), ("nextKeyDigest", optional digest value.nextKeyDigest)]

private def splitJson (value : PayEnrolClaim.FixedQuote) : Json := .mkObj
  [("amountAtomic", decimal value.amountAtomic), ("mintedCredit", decimal value.credit),
   ("birthFee", decimal value.birthFee), ("weeks", decimal value.requestedWeeks),
   ("membershipCredit", decimal value.membershipCredit),
   ("creditedRemainder", decimal value.creditedRemainder),
   ("minimumStarterCredit", decimal value.minimumStarterCredit)]

private def unsignedJson (value : PayEnrolMemoV2.Unsigned) : Json := .mkObj
  [("wireMode", decimal value.mode.byte.toNat),
   ("deploymentCommitment", digest value.deploymentCommitment),
   ("pricingCommitment", digest value.pricingCommitment),
   ("identityKey", hex value.enrollmentIdentityKey), ("authorizingKey", hex value.authorizingKey),
   ("authorityEpoch", decimal value.authorityEpoch), ("sshKey", hex value.sshKey),
   ("nextKeyDigest", digest value.nextKeyDigest),
   ("declaredNext", optional digest value.declaredNext), ("weeks", decimal value.weeks),
   ("minimumStarterCredit", decimal value.minimumStarterCredit),
   ("expiryHour", decimal value.expiresAtProcessingChainHour), ("amountAtomic", decimal value.amountAtomic)]

private def acceptJson (value : PayEnrolClaim.AcceptRequest) : Json := .mkObj
  [("action", "acceptCurrentQuote"), ("mode", modeJson value.mode),
   ("claimId", hex value.claimId), ("identityKey", hex value.ownerIdentityKey),
   ("authorizingKey", hex value.authorizingKey), ("authorityEpoch", decimal value.authorityEpoch),
   ("nonce", decimal value.nonce), ("pricingCommitment", digest value.pricingCommitment),
   ("weeks", decimal value.requestedWeeks), ("minimumStarterCredit", decimal value.minimumStarterCredit),
   ("expiryHour", decimal value.expiresAtProcessingChainHour)]

private def commandJson (value : PayClaimCommand.Command) : Json := .mkObj
  [("expectedAuthorityRoot", digest value.expectedAuthorityRoot),
   ("expectedPayRoot", digest value.expectedPayRoot),
   ("action", match value.action with
      | .inl accept => acceptJson accept
      | .inr rotation => .mkObj [("action", "rotatePendingOwner"),
          ("identityKey", hex rotation.ownerIdentityKey), ("expectedEpoch", decimal rotation.expectedEpoch),
          ("nonce", decimal rotation.nonce), ("successorKey", hex rotation.successorKey),
          ("successorNextKeyDigest", digest rotation.successorNextKeyDigest)])]

/-- Both messages are the source full unsigned frame. No fabricated detached
signature or placeholder signed memo is ever constructed for presentation. -/
private def materialJson (config : NativeHost.Config) (response : PayClaimQuote.Response) : Json :=
  match response.signingMaterial with
  | .inl unsigned =>
    let context : PayEnrolMemoV2.Context :=
      ⟨response.settlement.mint, response.settlement.tokenProgram, response.settlement.recipient⟩
    let message := PayEnrolMemoV2.unsignedFrame context unsigned
    .mkObj [("kind", "purchase"), ("unsigned", unsignedJson unsigned),
      ("unsignedCanonical", hex (PayEnrolMemoV2.unsignedBytes unsigned)),
      ("miniMessage", hex message), ("sshMessage", hex message),
      ("sshNamespace", .str (String.ofList
        (PayEnrolMemoV2.sshsigNamespace.map fun byte => Char.ofNat byte.toNat)))]
  | .inr command => .mkObj [("kind", "claim"), ("command", commandJson command),
      ("canonicalCommand", hex (PayClaimCommand.commandCodec.encode command)),
      ("signingMessage", hex (PayClaimCommand.possessionFrame config.deployment.domain
        config.profile.semantics command))]

private def quoteJson (config : NativeHost.Config) (response : PayClaimQuote.Response) : Json := .mkObj
  [("type", "payQuote"), ("authorityRoot", digest response.authorityRoot), ("payRoot", digest response.payRoot),
   ("asOf", asOf ⟨response.asOfSlot, response.asOfBlockTime⟩),
   ("priceReserved", .bool response.priceReserved),
   ("maxQuoteLifetimeHours", decimal PayClaimQuote.maxQuoteLifetimeHours),
   ("settlement", .mkObj [("index", decimal response.settlement.index),
      ("recipient", hex response.settlement.recipient), ("mint", hex response.settlement.mint),
      ("tokenProgram", hex response.settlement.tokenProgram)]),
   ("owner", ownerJson response.owner), ("split", splitJson response.split),
   ("signing", materialJson config response)]

/-- Source chooses identity-specific birth pricing and the exact arithmetic.
Canonical source shape/response bounds pass before JSON expansion is measured. -/
def quoteLoadedJson (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (json : Json) : Result Json := do
  let obj ← json.getObj?.mapError (fun _ => "object expected")
  let normalized ← if obj.get? "kind" == some (.str "purchase") ∧
      obj.get? "starter" == some .null then do
    let recommended ← need "byte-priced deployment requires explicit starter"
      (PayStarterAllowance.recommendation config.tariff (obj.get? "mode" == some (.str "renew")))
    pure (Json.mkObj (obj.foldl (init := []) (fun fields key value =>
      (key, if key == "starter" then decimal recommended else value) :: fields)))
    else pure json
  let request ← quoteRequest normalized
  let pay ← need "pay cell unavailable" (PayCellDomain.load config.deployment opened.durable.snapshot)
  let clock ← need "authenticated clock unavailable" (ClockCellDomain.load config.deployment opened.durable.snapshot)
  let identity ← (PayClaimQuote.requestIdentity pay.cell.logical request).mapError
    (fun reason => s!"paid quote identity: {repr reason}")
  let pricing := NativeHost.payClaimPricing config opened identity
  let response ← (PayClaimQuote.quote pay.cell opened.authority.snapshot clock.clock pricing request).mapError
    (fun reason => s!"paid quote: {repr reason}")
  let _ ← (PayClaimQuote.encodeResponse response).mapError
    (fun reason => s!"paid quote response: {repr reason}")
  boundedJson (quoteJson config response)

/-- Inspect only the closed source plan produced by op183; this does not prove
present authorization or rebase a stale command. -/
def claimPlanJson (bytes : List UInt8) : Result Json := do
  unless bytes.length ≤ 3072 do throw "claim plan exceeds 3072 bytes"
  let plan ← need "noncanonical claim signing plan" (NativeHost.claimSigningPlanCodec.decode bytes)
  unless plan.command.valid ∧ plan.domain.value < 2 ^ 256 ∧ plan.semantics.value < 2 ^ 256 do
    throw "claim signing plan shape refused"
  boundedJson (.mkObj [("type", "payClaimSigningPlan"), ("domain", digest plan.domain),
    ("semantics", digest plan.semantics), ("command", commandJson plan.command),
    ("canonicalCommand", hex (PayClaimCommand.commandCodec.encode plan.command)),
    ("signingMessage", hex plan.signingBytes), ("canonicalPlan", hex bytes)])

/-- Local source inspection binds native retained attempts to closed command bytes. -/
def claimCommandJson (bytes : List UInt8) : Result Json := do
  unless bytes.length ≤ 2048 do throw "claim command exceeds 2048 bytes"
  let command ← need "noncanonical claim command" (PayClaimCommand.commandCodec.decode bytes)
  unless command.valid do throw "claim command shape refused"
  boundedJson (.mkObj [("type", "payClaimCommand"), ("command", commandJson command),
    ("canonicalCommand", hex bytes)])

def claimIngressJson (config : NativeHost.Config) (bytes : List UInt8) : Result Json := do
  let ingress ← need "noncanonical signed claim ingress" (PayClaimCommand.decodeIngress bytes)
  let receipt := PayClaimReceiver.receipt config.deployment.domain config.profile.semantics ingress
  boundedJson (.mkObj [("type", "payClaimIngress"), ("command", commandJson ingress.command),
    ("canonicalCommand", hex ingress.ingress.commandBytes),
    ("signature", hex ingress.ingress.possessionSignature), ("canonicalIngress", hex bytes),
    ("expectedReceipt", .mkObj [("transactionId", decimal receipt.transactionId.value),
      ("eventId", decimal receipt.eventId.value)])])

/-- Offline source authoring preserves explicit roots. Authorization and the
successor commitment are checked only by the actual receiving source. -/
def authorRotation (json : Json) : Result (List UInt8) := do
  let obj ← object ["expectedAuthorityRoot", "expectedPayRoot", "identityKey", "expectedEpoch",
    "nonce", "successorKey", "successorNextKeyDigest"] [] json
  let authority ← bytes "expectedAuthorityRoot" 32 (← field obj "expectedAuthorityRoot")
  let pay ← bytes "expectedPayRoot" 32 (← field obj "expectedPayRoot")
  let identity ← bytes "identityKey" 32 (← field obj "identityKey")
  let epoch ← natural "expectedEpoch" 64 (← field obj "expectedEpoch")
  let nonce ← natural "nonce" 64 (← field obj "nonce")
  let successor ← bytes "successorKey" 32 (← field obj "successorKey")
  let next ← bytes "successorNextKeyDigest" 32 (← field obj "successorNextKeyDigest")
  let command : PayClaimCommand.Command :=
    ⟨⟨PayEnrolMemoV2.decodeLE authority⟩, ⟨PayEnrolMemoV2.decodeLE pay⟩,
      .inr ⟨identity, epoch, nonce, successor, ⟨PayEnrolMemoV2.decodeLE next⟩⟩⟩
  unless command.valid do throw "claim rotation shape refused"
  return PayClaimCommand.commandCodec.encode command

/-- Portable local source construction from an explicitly published receiving
context. The stable deployment seed is taken only from pinned configuration;
no live tariff is fabricated and no price is calculated here. -/
def purchaseContext (config : NativeHost.Config) (json : Json) : Result Json := do
  let obj ← object ["mint", "tokenProgram", "recipient"] ["nextPublic"] json
  let mint ← bytes "mint" 32 (← field obj "mint")
  let program ← bytes "tokenProgram" 32 (← field obj "tokenProgram")
  let recipient ← bytes "recipient" 32 (← field obj "recipient")
  let next ← match obj.get? "nextPublic" with
    | none => pure none
    | some value => do
      let public ← bytes "nextPublic" 32 value
      pure (some (SigningKeyCommitment.digest public))
  boundedJson (.mkObj [("type", "payPurchaseContext"),
    ("deploymentCommitment", digest (PayEnrolPricing.deploymentContextCommitment
      config.deployment.domain config.expectedSeed mint program recipient)),
    ("nextKeyDigest", optional digest next), ("domain", decimal config.deployment.domain.value),
    ("expectedSeed", decimal config.expectedSeed.value), ("mint", hex mint),
    ("tokenProgram", hex program), ("recipient", hex recipient)])

theorem bounded_json_size (value result : Json) (accepted : boundedJson value = .ok result) :
    result.compress.toUTF8.size ≤ maxJsonResponseBytes := by
  unfold boundedJson at accepted
  split at accepted
  · rename_i bounded
    injection accepted with same
    subst result
    exact bounded
  · cases accepted

#assert_axioms bounded_json_size

end Minidregg.Host.PayClaims
