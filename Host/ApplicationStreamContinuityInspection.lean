/- Strict private source codec helpers. Inspection presents a frame's shape;
only the pinned op152 callback establishes its fresh receiving provenance. -/
import Kernel.ApplicationStreamContinuity
import Lean.Data.Json

namespace Minidregg.Host.ApplicationStreamContinuityInspection

open Lean
open Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.ApplicationStreamContinuity

set_option autoImplicit false

def exactObject (fields : List String) (json : Json) :
    Except String (Std.TreeMap.Raw String Json compare) := do
  let obj ← json.getObj?.mapError (fun _ => "continuity object expected")
  let actual := obj.foldl (init := []) (fun keys key _ => key :: keys)
  for key in fields do
    unless actual.contains key do throw s!"continuity missing {key}"
  for key in actual do
    unless fields.contains key do throw s!"continuity unexpected {key}"
  pure obj

def field (obj : Std.TreeMap.Raw String Json compare) (key : String) :
    Except String Json :=
  match obj.get? key with
  | some value => .ok value
  | none => .error s!"continuity missing {key}"

def nat (json : Json) : Except String Nat := do
  let s ← json.getStr?.mapError (fun _ => "continuity decimal string expected")
  let some n := s.toNat? | throw "continuity unsigned decimal expected"
  unless toString n == s do throw "continuity noncanonical decimal"
  pure n

def int (json : Json) : Except String Int := do
  let s ← json.getStr?.mapError (fun _ => "continuity decimal string expected")
  let some n := s.toInt? | throw "continuity signed decimal expected"
  unless toString n == s do throw "continuity noncanonical decimal"
  pure n

private def nibble (byte : UInt8) : Option Nat :=
  let n := byte.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 97 ≤ n ∧ n ≤ 102 then some (n - 97 + 10)
  else none

def hex (limit : Nat) (json : Json) : Except String (List UInt8) := do
  let s ← json.getStr?.mapError (fun _ => "continuity hex string expected")
  let input := s.toUTF8
  unless input.size % 2 == 0 && decide (input.size / 2 ≤ limit) do
    throw "continuity hex length refused"
  let mut output := ByteArray.empty
  for i in [:input.size / 2] do
    match nibble input[2*i]!, nibble input[2*i+1]! with
    | some hi, some lo => output := output.push (UInt8.ofNat (16*hi+lo))
    | _, _ => throw "continuity lowercase hex expected"
  pure output.toList

def hexJson (bytes : List UInt8) : Json :=
  .str (String.fromUTF8! (hexBytes bytes).toByteArray)

def decimal (n : Nat) : Json := .str (toString n)
def signedDecimal (n : Int) : Json := .str (toString n)

def authorChallenge (config : NativeHost.Config) (json : Json) : Except String (List UInt8) := do
  let obj ← exactObject ["domain", "semantics", "app", "appGeneration", "session",
    "sessionGeneration", "subject", "ticketResource", "sessionFingerprintHex",
    "streamNonceHex", "attemptNonceHex", "minimumHeight", "minimumWorldRoot"] json
  let domain ← nat (← field obj "domain")
  let semantics ← nat (← field obj "semantics")
  unless domain == config.deployment.domain.value && semantics == config.profile.semantics.value do
    throw "continuity namespace differs from pinned source"
  let fingerprint ← hex 32 (← field obj "sessionFingerprintHex")
  let stream ← hex 32 (← field obj "streamNonceHex")
  let attempt ← hex 32 (← field obj "attemptNonceHex")
  unless fingerprint.length == 32 && stream.length == 32 && attempt.length == 32 do
    throw "continuity fingerprint and nonces must be 32 bytes"
  let binding : Binding :=
    { app := ← nat (← field obj "app")
      appGeneration := ← int (← field obj "appGeneration")
      session := ← nat (← field obj "session")
      sessionGeneration := ← int (← field obj "sessionGeneration")
      subject := ← nat (← field obj "subject")
      ticketResource := ← nat (← field obj "ticketResource")
      fingerprint := ⟨fingerprint.foldr (fun byte rest => byte.toNat + 256 * rest) 0⟩ }
  let challenge : Challenge :=
    { domain := config.deployment.domain, semantics := config.profile.semantics
      binding := binding, streamNonce := stream, attemptNonce := attempt
      minimumHeight := ← nat (← field obj "minimumHeight")
      minimumWorldRoot := ⟨← nat (← field obj "minimumWorldRoot")⟩ }
  pure (challengeCodec.encode challenge)

def authorRequest (json : Json) : Except String (List UInt8) := do
  let obj ← exactObject ["challengeHex", "ingressHex"] json
  let challengeBytes ← hex 8192 (← field obj "challengeHex")
  let some challenge := challengeCodec.decode challengeBytes
    | throw "noncanonical continuity challenge"
  let ingress ← hex 12102760 (← field obj "ingressHex")
  unless !ingress.isEmpty do throw "empty continuity ingress"
  pure (requestCodec.encode ⟨challenge, ingress⟩)

def inspect (bytes : List UInt8) : Except String Json := do
  let some (challenge, tip) := inspectBytes bytes
    | throw "noncanonical continuity attestation"
  let b := challenge.binding
  pure <| .mkObj
    [("type", "application-stream-continuity-inspection-v1"),
     ("frameHex", hexJson bytes),
     ("challengeHex", hexJson (challengeCodec.encode challenge)),
     ("domain", decimal challenge.domain.value),
     ("semantics", decimal challenge.semantics.value),
     ("streamNonceHex", hexJson challenge.streamNonce),
     ("attemptNonceHex", hexJson challenge.attemptNonce),
     ("app", decimal b.app),
     ("appGeneration", signedDecimal b.appGeneration),
     ("session", decimal b.session),
     ("sessionGeneration", signedDecimal b.sessionGeneration),
     ("subject", decimal b.subject),
     ("ticketResource", decimal b.ticketResource),
     ("sessionFingerprint", decimal b.fingerprint.value),
     ("tip", .mkObj [("height", decimal tip.height),
       ("chain", decimal tip.chain.value), ("worldRoot", decimal tip.worldRoot.value)])]

end Minidregg.Host.ApplicationStreamContinuityInspection
