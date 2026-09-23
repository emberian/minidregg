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

def exportPackage (config : Config) (signedCall : List UInt8) : IO (Except String (List UInt8)) := do
  unless signedCall.length ≤ maxCallBytes do
    return .error "signed call exceeds P0 evidence bound"
  let some call := callCodec.decode signedCall
    | return .error "noncanonical native signed call"
  let opened ← match ← NativeHost.openExisting config with
    | .ok opened => pure opened
    | .error detail => return .error s!"source native history: {detail}"
  let .confirmed .replayed receipt := NativeHost.lookupLoaded config opened call
    | return .error "exact signed call is absent or conflicts with source history"
  unless receipt.acceptedCount == 1 do
    return .error "P0 export requires the first accepted event"
  let image : DurableReceiver.Image :=
    ⟨opened.durable.image.seed, opened.durable.image.accepted.take receipt.acceptedCount⟩
  return encodeChecked ⟨config.deployment.domain, config.profile.semantics,
    config.expectedSeed, signedCall, receipt, DurableReceiverCodec.encode image⟩

def verify (config : Config) (bytes : List UInt8) : IO (Except String Receipt) := do
  let package ← match decodeChecked bytes with
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
      unless verified.receipts == [package.originalReceipt] do
        return .error "original accepted-prefix receipt mismatch"
      match NativeHost.lookupLoaded config verified.opened call with
      | .confirmed .replayed receipt =>
          if receipt == package.originalReceipt then return .ok receipt
          else return .error "exact-call historical receipt mismatch"
      | _ => return .error "signed call is absent or conflicts with verified prefix"

end Minidregg.Kernel.FnEvidence
