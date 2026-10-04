/- Driver of scripts/check-fn-wire.sh: run Mini's grammar interpreter over an fn wire-grammar
file. `lake env lean --run scripts/check-fn-wire.lean FILE [--unpinned]`.
Pinned (default): the file's BLAKE3-256 must be `pinnedDigest`, then every vector is checked.
`--unpinned`: the digest is reported, not required (only for the gate's planted-fault controls).
Prints one verdict line `fn-wire: OK ...` or `fn-wire: RED ...`; exit 0 only on OK. -/
import Compiler.FnWirePinned

open Minidregg.Compiler

def main (args : List String) : IO UInt32 := do
  let some (path, pinned) := (match args with
      | [p] => some (p, true)
      | [p, "--unpinned"] => some (p, false)
      | _ => none)
    | IO.eprintln "usage: check-fn-wire.lean FILE [--unpinned]"; return 64
  let bytes ← IO.FS.readBinFile path
  let digest := Blake3.toHex (Blake3.hash bytes.toList)
  if pinned && digest != FnWire.pinnedDigest then
    IO.println s!"fn-wire: RED digest {digest} is not the pinned {FnWire.pinnedDigest} (fn {FnWire.pinnedRevision})"
    return 1
  let some text := String.fromUTF8? bytes
    | IO.println "fn-wire: RED the file is not UTF-8"; return 1
  match FnWire.checkDoc text with
  | .ok s =>
      IO.println s!"fn-wire: OK families={s.families} accepted={s.accepted} refused={s.refused} octets={bytes.size} digest={digest}{if pinned then s!" pinned fn {FnWire.pinnedRevision}" else " UNPINNED"}"
      return 0
  | .error e =>
      IO.println s!"fn-wire: RED {e}"
      return 1
