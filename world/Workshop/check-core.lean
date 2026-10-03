/- Check the actual upstream-elaborated proof/program Book using the installed
exact BendTT kernel port. This does not execute a world method or grant rights. -/
import Theory.BendTTSource

open Minidregg.Theory.BendTT

def main (paths : List String) : IO UInt32 := do
  if paths.isEmpty then
    IO.eprintln "BendTT Book paths required"
    return 2
  for path in paths do
    let source ← IO.FS.readFile path
    match Book.parse source with
    | .error detail =>
        IO.eprintln s!"BENDTT BOOK PARSE REFUSED {path}: {detail}"
        return 1
    | .ok book =>
        if book.any (fun definition => definition.o) then
          IO.eprintln s!"BENDTT BOOK OPAQUE REFUSED {path}"
          return 1
        match Book.check book with
        | .error detail =>
            IO.eprintln s!"BENDTT BOOK CHECK REFUSED {path}: {detail}"
            return 1
        | .ok () =>
            IO.println s!"BENDTT BOOK CHECK PASS {path} definitions={book.length}"
  return 0
