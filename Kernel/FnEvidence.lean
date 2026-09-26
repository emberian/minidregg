/-
Read-only export and independent verification of one public native operation.
Verification calls the existing native historical re-admission path. It never
installs the foreign image or treats a carried receipt as execution authority.
-/
import Kernel.NativeHost
import Compiler.FnEvidenceCodec

namespace Minidregg.Kernel.FnEvidence

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.FnEvidenceCodec
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

/-- Selecting an original receipt at acceptedCount seals exactly that many
accepted records, even if the source history has advanced since confirmation. -/
theorem originalPrefix_length {α : Type} (accepted : List α) (acceptedCount : Nat)
    (within : acceptedCount ≤ accepted.length) :
    (accepted.take acceptedCount).length = acceptedCount := by
  simp [List.length_take, Nat.min_eq_left within]

def exportPackage (config : Config) (signedCall : List UInt8)
    (limits : Limits := Limits.portable) : IO (Except String (List UInt8)) := do
  unless limits.valid do return .error "invalid operator evidence limits"
  unless signedCall.length ≤ limits.callBytes do
    return .error "signed call exceeds evidence bound"
  let some call := callCodec.decode signedCall
    | return .error "noncanonical native signed call"
  let opened ← match ← NativeHost.openExisting config with
    | .ok opened => pure opened
    | .error detail => return .error s!"source native history: {detail}"
  let .confirmed .replayed receipt := NativeHost.lookupLoaded config opened call
    | return .error "exact signed call is absent or conflicts with source history"
  unless 1 ≤ receipt.acceptedCount &&
      receipt.acceptedCount ≤ opened.durable.image.accepted.length do
    return .error "original receipt is outside accepted history"
  let image : DurableReceiver.Image :=
    ⟨opened.durable.image.seed, opened.durable.image.accepted.take receipt.acceptedCount⟩
  return encodeCheckedWith limits ⟨config.deployment.domain, config.profile.semantics,
    config.expectedSeed, signedCall, receipt, DurableReceiverCodec.encode image⟩

def verify (config : Config) (bytes : List UInt8)
    (limits : Limits := Limits.portable) : IO (Except String Receipt) := do
  let package ← match decodeCheckedWith limits bytes with
    | .ok package => pure package
    | .error detail => return .error detail
  unless package.domain == config.deployment.domain &&
      package.semantics == config.profile.semantics &&
      package.genesisPin == config.expectedSeed do
    return .error "package domain, profile, or genesis differs from independent pin"
  let some call := callCodec.decode package.signedCall
    | return .error "noncanonical native signed call"
  match ← NativeHostReplay.verifyBytes config package.acceptedPrefix with
  | .error failure => return .error s!"native prefix refused at {failure.index}: {failure.detail}"
  | .ok ⟨target, verified⟩ =>
      unless target.image.accepted.length == package.originalReceipt.acceptedCount do
        return .error "package carries a later or shorter accepted prefix"
      unless verified.receipts.getLast? == some package.originalReceipt do
        return .error "original accepted-prefix receipt mismatch"
      match NativeHost.lookupLoaded config verified.opened call with
      | .confirmed .replayed receipt =>
          if receipt == package.originalReceipt then return .ok receipt
          else return .error "exact-call historical receipt mismatch"
      | _ => return .error "signed call is absent or conflicts with verified prefix"

end Minidregg.Kernel.FnEvidence
