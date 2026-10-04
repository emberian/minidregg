import Compiler.GenericSimplexIO
/-!
Reopen of long append-only agreement journals, compiled (`lake build
generic-simplex-log-reopen`, then run the binary). A standing replica appends
one `Delta` frame per acknowledged input, so its journal grows without bound and
every restart decodes, re-encodes, compares and replays the whole image. A
long run's journal (1757 frames, 19.7 MB, on the four-source evidence copy)
aborted reopen with "Stack overflow detected": `openRestored` decided
`l.encode = bytes` with core's `List.hasDecEq`, which recurses once per BYTE
(64-byte frames) on the 1 GiB stack the Lean runtime gives `main`, so any image
above ~16.7 MB overflowed.

Three shapes, each 100 000 entries: a log of 100 000 appended delta frames, every
hundredth carrying a COMMIT witness with a 32 KiB block (an image of ~34 MB,
above the per-byte recursion's limit, so the old reopen aborts on it); a base frame holding
100 000 events (a converted legacy journal); and a single delta holding 100 000
events. Each is built through the same `appendRestored`
the replica runs, then reopened exactly as `openNative` does (`scanLog`, then
`openRestored`), and the reopened log and state must equal the in-memory ones.
-/
namespace Minidregg.Verify.GenericSimplexLogReopen
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false

def entries : Nat := 100000

/-- A well-formed n=4 f=1 context: four distinct 1952-byte public keys. -/
def context : Context :=
  ⟨[1,2,3], 0, [4,5,6], ⟨4,1,100000,8,3⟩,
    (List.range 4).map fun i => List.replicate 1952 (UInt8.ofNat (i + 1))⟩

/-- Inputs that replay without failing: polls and in-view clock ticks. -/
def event (i : Nat) : Event :=
  if i % 2 == 0 then encodeInput .poll else encodeInput (.tick (i % 99999))

/-- Witnesses are retained, not replayed: their size models the COMMIT
evidence (a block carrying whole source records) a real delta carries. -/
def witnesses (i : Nat) : List CommitWitness :=
  if i % 100 == 0 then [⟨i + 1, [List.replicate 32768 (UInt8.ofNat i)], ⟨1, []⟩⟩] else []

def require (condition : Bool) (detail : String) : IO Unit :=
  unless condition do throw (IO.userError detail)

/-- Reopen `bytes` the way `openNative` does and compare with the writer's image. -/
def reopenMatches (bytes : Bytes) (expected : Restored context) (shape : String) : IO Unit := do
  let some valid := scanLog bytes
    | throw (IO.userError s!"{shape}: scanLog refused the image")
  require (valid == bytes.length) s!"{shape}: scanLog reported a torn tail"
  let some reopened := openRestored context (bytes.take valid)
    | throw (IO.userError s!"{shape}: openRestored refused the image")
  require (reopened.length == expected.length) s!"{shape}: reopened length differs"
  require (reopened.log == expected.log) s!"{shape}: reopened log differs"
  require (reopened.state == expected.state) s!"{shape}: reopened state differs"
  IO.println s!"PASS {shape}: {bytes.length} bytes, {reopened.log.recent.length} delta frames, {reopened.log.merged.events.length} events"

def fresh (base : Journal) : IO (Restored context) := do
  let some r := openRestored context (Log.encode ⟨base,[]⟩)
    | throw (IO.userError "base journal does not replay")
  return r

def main : IO Unit := do
  let empty : Journal := ⟨context,0,0,[],[]⟩
  -- 1. 100 000 appended delta frames, one input each.
  IO.println s!"{entries} appended delta frames"
  let mut r ← fresh empty
  let mut image : Array UInt8 := (Log.encode ⟨empty,[]⟩).toArray
  let mut lastFrame := 0
  for i in List.range entries do
    let some (next,frame) := appendRestored r [event i] (witnesses i)
      | throw (IO.userError s!"append {i} refused")
    r := next
    lastFrame := frame.length
    image := frame.foldl Array.push image
  require (r.length == image.size) "appended frame lengths disagree with the image"
  require (image.size > 1073741824 / 64) "delta-frame image does not exceed the per-byte recursion limit"
  reopenMatches image.toList r "delta-frames"
  -- A torn final frame (an unacknowledged append cut short) is classified as
  -- such: the valid prefix ends before it.
  require (scanLog (image.toList.take (image.size - 3)) == some (image.size - lastFrame))
    "torn final frame not classified as a torn tail"
  IO.println "PASS torn tail: the valid prefix ends at the last complete frame"
  -- 2. One base frame carrying 100 000 events (a converted legacy journal).
  IO.println s!"base frame with {entries} events"
  let big := (List.range entries).map event
  let some base := openRestored context (Log.encode ⟨{empty with events := big},[]⟩)
    | throw (IO.userError "large base frame does not replay")
  reopenMatches base.log.encode base "base-events"
  -- 3. One delta frame carrying 100 000 events.
  IO.println s!"one delta frame with {entries} events"
  let start ← fresh empty
  let some (one,_) := appendRestored start big []
    | throw (IO.userError "large delta does not replay")
  reopenMatches one.log.encode one "delta-events"

end Minidregg.Verify.GenericSimplexLogReopen

def main : IO Unit := Minidregg.Verify.GenericSimplexLogReopen.main
