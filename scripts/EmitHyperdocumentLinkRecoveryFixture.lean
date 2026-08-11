import Assurance.HyperdocumentLinkLocalFileStore

open Minidregg.Assurance.HyperdocumentLinkLocalFileStore

/-- Emit the exact Lean-authored recovery byte stream consumed by the local
filesystem conformance tests. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      IO.FS.writeBinFile path ⟨recoveryFixture.toArray⟩
      IO.println s!"wrote {recoveryFixture.length} Lean-authored bytes to {path}"
      pure 0
  | _ =>
      IO.eprintln "usage: EmitHyperdocumentLinkRecoveryFixture.lean OUTPUT"
      pure 2
