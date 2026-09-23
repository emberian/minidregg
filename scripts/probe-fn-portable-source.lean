import Kernel.FnPortableSource

open Minidregg.Kernel.FnPortableSource

def require (condition : Bool) (detail : String) : IO Unit :=
  unless condition do throw (IO.userError detail)

def main (arguments : List String) : IO Unit := do
  let [sourcePath, packagePath] := arguments
    | throw (IO.userError "usage: probe-fn-portable-source SOURCE PACKAGE")
  let source ← IO.FS.readBinFile sourcePath
  let package ← IO.FS.readBinFile packagePath
  let .ok extracted := extract source.toList
    | throw (IO.userError "public exact source was refused")
  require (extracted.package == package.toList) "decoded body differs from exact P0 package"
  require (extracted.messageId ==
    "<mini-e1-1bea29c16a63e8722f156770@example.invalid>") "wrong exact Message-ID"
  require (extracted.groups == "fn.test") "wrong exact group"
  let text := String.fromUTF8! source
  for (name, altered) in
      [("MIME", text.replace "Content-Type: application/vnd.dregg.fn-native-prefix; version=1"
         "Content-Type: text/plain"),
       ("duplicate", text.replace "Content-Transfer-Encoding: base64"
         "Content-Transfer-Encoding: base64\r\nContent-Transfer-Encoding: base64"),
       ("body", text.replace "RFJFR0cv" "!FJFR0cv"),
       ("line", text.replace "RFJFR0cv" "RFJFR0cv\r\n")]
    do
      require (match extract altered.toUTF8.toList with
        | .error _ => true
        | .ok _ => false) s!"{name} mutation was accepted"
  IO.println "fn portable E1 extraction and four negative cases passed"
