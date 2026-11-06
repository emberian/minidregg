/-
scripts/kernel-vectors.lean -- Lean-authored conformance vectors for native/mini-kernels.

  lake env lean --run scripts/kernel-vectors.lean > native/mini-kernels/testdata/lean-vectors.json

Writes the fixed rows the tree's conformance theorems pin and SEEDED rows computed by the Lean
fast path (`cshake256Fast`, `kmac256Fast`: the proved implementation, called by name so the
`@[csimp]` kernel attachment of `cshake256Bytes`/`kmac256Bytes` is not what produces them) at
the rate boundaries 0, 1, 135, 136, 137, 271, 272, 273 and 4096 input bytes, with empty and
non-empty customizations. The `cshake256_midstate` rows are the absorbed-prefix bodies
(`Midstate.absorbFast`, `Midstate.finishFast`, likewise by name, not the `@[extern]` seams) at
prefix lengths straddling the rate. `cargo test -p mini-kernels --test conformance` reads the file.
-/
import Theory.Sp800185Cshake256Fast
import Theory.Sp800185Cshake256Midstate
import Compiler.Sp800185Kmac256Conformance

open Minidregg.Compiler.Sp800185Cshake256

def hexOf (bytes : List UInt8) : String :=
  String.join (bytes.map fun b =>
    let digits := "0123456789abcdef".toList
    String.ofList [digits[(b.toNat / 16)]!, digits[(b.toNat % 16)]!])

/-- A seeded byte list (64-bit LCG; the seed names the row). -/
def seeded (seed count : Nat) : List UInt8 := Id.run do
  let mut state : UInt64 := UInt64.ofNat (seed * 2654435761 + 12345)
  let mut out : Array UInt8 := #[]
  for _ in [0:count] do
    state := state * 6364136223846793005 + 1442695040888963407
    out := out.push (UInt8.ofNat ((state >>> 33).toNat % 256))
  return out.toList

def lengths : List Nat := [0, 1, 135, 136, 137, 271, 272, 273, 4096]

def customizations : List (String × List UInt8) :=
  [("empty", []), ("lifecycle", "DREGG.CELL.LIFECYCLE/v1".toUTF8.toList),
   ("long", (seeded 99 200))]

def cshakeRow (name : String) (customization input output : List UInt8) : String :=
  s!"    \{\"name\": \"{name}\", \"customization\": \"{hexOf customization}\", \"input\": \"{hexOf input}\", \"output\": \"{hexOf output}\"}"

def kmacRow (name : String) (key customization input output : List UInt8) : String :=
  s!"    \{\"name\": \"{name}\", \"key\": \"{hexOf key}\", \"customization\": \"{hexOf customization}\", \"input\": \"{hexOf input}\", \"output\": \"{hexOf output}\"}"

def midstateRow (name : String) (customization pre suffix : List UInt8) : String :=
  let midstate := Midstate.absorbFast (Native.bytesOfList customization) (Native.bytesOfList pre)
  let output := Midstate.finishFast midstate (Native.bytesOfList suffix)
  s!"    \{\"name\": \"{name}\", \"customization\": \"{hexOf customization}\", \"prefix\": \"{hexOf pre}\", \"suffix\": \"{hexOf suffix}\", \"midstate\": \"{hexOf midstate.data.toList}\", \"output\": \"{hexOf output.data.toList}\"}"

def main : IO Unit := do
  let fixedCshake := [
    cshakeRow "nist-sp800-185-sample-3" "Email Signature".toUTF8.toList [0, 1, 2, 3]
      (Fast.cshake256Fast "Email Signature".toUTF8.toList [0, 1, 2, 3]),
    cshakeRow "shake256-empty" [] [] (Fast.cshake256Fast [] [])]
  let mut cshake := fixedCshake
  let mut seed := 1
  for (cname, custom) in customizations do
    for n in lengths do
      let input := seeded seed n
      cshake := cshake ++ [cshakeRow s!"seeded-{cname}-{n}" custom input (Fast.cshake256Fast custom input)]
      seed := seed + 1
  let key := kmacVectorKey
  let fixedKmac := [
    kmacRow "pycryptodome-tagged" key "My Tagged Application".toUTF8.toList [0, 1, 2, 3]
      (kmac256Fast key "My Tagged Application".toUTF8.toList [0, 1, 2, 3]),
    kmacRow "pycryptodome-checkpoint-customization" key
      "DREGG/NATIVE-HOST/CHECKPOINT-MAC/v1".toUTF8.toList "abc".toUTF8.toList
      (kmac256Fast key "DREGG/NATIVE-HOST/CHECKPOINT-MAC/v1".toUTF8.toList "abc".toUTF8.toList)]
  let mut kmac := fixedKmac
  for (cname, custom) in customizations do
    for n in lengths do
      let input := seeded seed n
      let k := seeded (seed + 1000) (if n % 2 == 0 then 32 else 7)
      kmac := kmac ++ [kmacRow s!"seeded-{cname}-{n}" k custom input (kmac256Fast k custom input)]
      seed := seed + 1
  let mut midstate : List String := []
  for (cname, custom) in customizations do
    for n in [0, 1, 135, 136, 137, 272, 273] do
      let pre := seeded seed n
      let suffix := seeded (seed + 2000) (if n % 2 == 0 then 5 else 136)
      midstate := midstate ++ [midstateRow s!"seeded-{cname}-{n}" custom pre suffix]
      seed := seed + 1
  IO.println "{"
  IO.println "  \"source\": \"Lean-authored vectors, written by scripts/kernel-vectors.lean from the Lean fast path (cshake256Fast / kmac256Fast). The fixed rows are the constants the tree's conformance theorems pin; the seeded rows cover the rate boundaries. Regenerate with `lake env lean --run scripts/kernel-vectors.lean`.\","
  IO.println "  \"cshake256\": ["
  IO.println (String.intercalate ",\n" cshake)
  IO.println "  ],"
  IO.println "  \"kmac256\": ["
  IO.println (String.intercalate ",\n" kmac)
  IO.println "  ],"
  IO.println "  \"cshake256_midstate\": ["
  IO.println (String.intercalate ",\n" midstate)
  IO.println "  ]"
  IO.println "}"
