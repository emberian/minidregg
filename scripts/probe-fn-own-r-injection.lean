/-
The qualified fn owner injects two hop-local header lines before a signed R
carrier that already includes Date and Message-ID. This checks the one native
delivery observed in the fresh own-R gate and refusal of nearby altered forms.
The source/Store authority still comes from native hybrid verification and
Mini's accepted tag-10/tag-9 selectors, not this byte-shape probe.
-/
import Host.Main

open Minidregg.Host

set_option autoImplicit false

private def require (condition : Bool) (detail : String) : IO Unit := do
  unless condition do throw (IO.userError detail)

private def bytes (value : String) : List UInt8 := value.toUTF8.toList

def ownRInjectionProbe : IO Unit := do
  let authored := bytes "From: example\r\nDate: fixed\r\nMessage-ID: <r>\r\n\r\nbody\r\n"
  let injection := bytes
    "Path: fn.example.invalid!not-for-mail\r\nInjection-Info: fn.example.invalid\r\n"
  require (fnOwnRCarrierMatches authored authored)
    "exact signed carrier was refused"
  require (fnOwnRCarrierMatches (injection ++ authored) authored)
    "qualified two-line fn injection was refused"
  for altered in [
    bytes "Path: fn.example.invalid!not-for-mail\r\nInjection-Info: other.invalid\r\n",
    bytes "Path: fn.example.invalid!not-for-mail\r\nXref: extra\r\nInjection-Info: fn.example.invalid\r\n",
    bytes "path: fn.example.invalid!not-for-mail\r\nInjection-Info: fn.example.invalid\r\n",
    bytes "Path: fn.example.invalid!not-for-mail\nInjection-Info: fn.example.invalid\r\n",
    bytes "Path: .invalid!not-for-mail\r\nInjection-Info: .invalid\r\n"] do
    require (!fnOwnRCarrierMatches (altered ++ authored) authored)
      "altered fn injection prefix was accepted"
  require (!fnOwnRCarrierMatches (injection ++ authored ++ [33]) authored)
    "modified signed carrier tail was accepted"
  let some receivedPath ← IO.getEnv "FN_OWNR_RECEIVED"
    | throw (IO.userError "missing FN_OWNR_RECEIVED")
  let some authoredPath ← IO.getEnv "FN_OWNR_AUTHORED"
    | throw (IO.userError "missing FN_OWNR_AUTHORED")
  let received ← IO.FS.readBinFile receivedPath
  let authored ← IO.FS.readBinFile authoredPath
  require (fnOwnRCarrierMatches received.toList authored.toList)
    "actual qualified fn own-R delivery did not preserve exact signed carrier"
  IO.println s!"PASS strict fn injection prefix and exact retained carrier: received={received.size}, authored={authored.size}"

#eval ownRInjectionProbe
