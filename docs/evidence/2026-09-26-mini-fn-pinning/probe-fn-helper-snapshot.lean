import Host.Main

open Lean

set_option autoImplicit false

def probeFnHelperSnapshot : IO Unit :=
  IO.FS.withTempDir fun directory => do
    let source := directory / "source-helper"
    IO.FS.writeFile source "#!/bin/sh\nprintf old"
    let permission ← IO.Process.output
      { cmd := "/bin/chmod", args := #["0700", source.toString] }
    unless permission.exitCode == 0 do
      throw (IO.userError "test helper chmod failed")
    let pinnedPath ← Minidregg.Host.snapshotOperatorFile directory "pinned-helper"
      source.toString 4096 "0500"
    IO.FS.writeFile source "#!/bin/sh\nprintf new"
    let original ← IO.Process.output { cmd := source.toString }
    let pinned ← IO.Process.output { cmd := pinnedPath }
    unless original.exitCode == 0 && original.stdout == "new" &&
        pinned.exitCode == 0 && pinned.stdout == "old" do
      throw (IO.userError "pinned helper changed after original pathname replacement")
    IO.println "PASS private helper retains old bytes after source rewrite"

#eval probeFnHelperSnapshot
