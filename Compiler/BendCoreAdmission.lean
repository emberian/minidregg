/- Actual pinned BendTT parse/check admission, with canonical core bytes.
This is the source kernel gate, not a surface-elaborator correctness theorem
or an alternative to Mini's current program RunClaim receiving contract. -/
import Theory.BendTTSource
import Compiler.BendWorldSource

namespace Minidregg.Compiler.BendCoreAdmission
open Minidregg.Theory.BendTT
set_option autoImplicit false

def text (book : Book) : String :=
  String.intercalate "\n" (book.map fun d =>
    (if d.o then "opaque " else "") ++ d.k ++ " : " ++ Term.show d.T 0 ++
      " = " ++ Term.show d.v 0) ++ "\n"

def encode (book : Book) : List UInt8 := (text book).toUTF8.toList

structure Checked where
  private mk ::
  bytes : List UInt8
  book : Book
  canonical : encode book = bytes
  checked : Book.check book = .ok ()
  /-- Initial execution profile has no opaque foreign implementations. -/
  transparent : book.all (fun d => !d.o) = true

def admit (bytes : List UInt8) : Except String Checked := do
  let some source := String.fromUTF8? ⟨bytes.toArray⟩ | throw "invalid BendTT UTF-8"
  let book ← Book.parse source
  if canonical : encode book = bytes then
    if checked : Book.check book = .ok () then
      if transparent : book.all (fun d => !d.o) = true then
        pure ⟨bytes, book, canonical, checked, transparent⟩
      else throw "opaque implementation has no runtime refinement"
    else throw "BendTT Book.check refused"
  else throw "BendTT bytes are not canonical core text"

/-- Canonicalize an emitted Book before publication, then require actual parser
roundtrip/check admission. An elaborator's successful exit is insufficient. -/
def canonicalize (bytes : List UInt8) : Except String Checked := do
  let some source := String.fromUTF8? ⟨bytes.toArray⟩ | throw "invalid BendTT UTF-8"
  let book ← Book.parse source
  admit (encode book)

structure Entry (core : Checked) where
  name : String
  definition : Def
  exact : Book.get core.book name = some definition

def entry (core : Checked) (name : String) : Except String (Entry core) :=
  match found : Book.get core.book name with
  | none => .error "BendTT entry is absent"
  | some definition => .ok ⟨name, definition, found⟩

theorem checked_live (core : Checked) : Book.WellTyped core.book ∧ Book.Live core.book :=
  book_check core.book core.checked

theorem canonical_bytes (core : Checked) : encode core.book = core.bytes := core.canonical

end Minidregg.Compiler.BendCoreAdmission
