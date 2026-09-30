import Host.CapabilityInspection

namespace Minidregg.Host.CapabilityInspectionCheck

open Lean
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Host.CapabilityInspection

private def parent : Capability .object := {
  id := ⟨141⟩, root := ⟨101⟩, parent := some ⟨101⟩, issuer := ⟨17⟩
  holder := .subject ⟨8⟩
  scope := ⟨{⟨8401⟩}, {.observeObject, .delegateObject}, 9007199254740993⟩
  notBefore := 23, notAfter := 99999, issuerEpoch := 7
  policyId := ⟨8401⟩, policyEpoch := 11
  ancestors := {⟨101⟩}, channels := {⟨29⟩, ⟨31⟩} }

def main : IO Unit := do
  let stored : StoredCapability .object := ⟨parent, []⟩
  let bytes := (storedCapabilityStream .object).encode stored
  let inspected ← match inspect .object bytes with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  let expectedHead := Json.mkObj [
    ("id", "141"), ("root", "101"), ("parent", "101"), ("issuer", "17"),
    ("holder", Json.mkObj [("type", "subject"), ("subject", "8")]),
    ("targets", Json.arr #["8401"]), ("verbs", Json.arr #["observe", "delegate"]),
    ("maxCost", "9007199254740993"), ("notBefore", "23"), ("notAfter", "99999"),
    ("issuerEpoch", "7"), ("policyId", "8401"), ("policyEpoch", "11"),
    ("ancestors", Json.arr #["101"]), ("channels", Json.arr #["29", "31"])]
  match inspected.getObjVal? "head" with
  | .error message => throw (IO.userError message)
  | .ok head => unless head == expectedHead do
      throw (IO.userError "decoded capability fields differ from exact source")
  match inspect .object (bytes ++ [0]) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "capability trailing bytes accepted")
  match inspect .object [] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "empty capability accepted")
  IO.println "capability inspection: exact parent fields, wide integer and malformed input PASS"

#eval main

end Minidregg.Host.CapabilityInspectionCheck
