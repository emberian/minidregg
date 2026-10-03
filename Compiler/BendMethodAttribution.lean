/- Source inspection attribution and actual checked core-entry selection.
The parser/elaborator transcript is retained verbatim. This module checks its
source/entry coordinates, not a theorem that arbitrary transcripts describe
correct elaboration. That separate correspondence obligation cannot be replaced
by accepting an unrelated well-typed Book. -/
import Compiler.BendCoreAdmission

namespace Minidregg.Compiler.BendMethodAttribution
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.BendTT
set_option autoImplicit false

structure Claim where
  moduleIndex : Nat
  source : Digest
  sourceDefinition : String
  coreEntry : String
  startByte : Nat
  endByte : Nat
  transcript : List UInt8
  deriving DecidableEq, Repr

def stream : StreamCodec Claim :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream
    (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat bytesStream))))))
    (fun c => (c.moduleIndex, c.source, c.sourceDefinition, c.coreEntry,
      c.startByte, c.endByte, c.transcript))
    (fun c => ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1,
      c.2.2.2.2.2.1, c.2.2.2.2.2.2⟩)
    (by intro c; cases c; rfl)

structure Selected (core : BendCoreAdmission.Checked)
    (package : BendWorldSource.Package) (claim : Claim) where
  private mk ::
  sourceModule : BendWorldSource.Module
  exactModule : package.modules[claim.moduleIndex]? = some sourceModule
  exactSource : BendWorldSource.sourceId sourceModule.bytes = claim.source
  spanBound : claim.startByte ≤ claim.endByte ∧ claim.endByte ≤ sourceModule.bytes.length
  entry : BendCoreAdmission.Entry core
  exactEntry : entry.name = claim.coreEntry

def select (core : BendCoreAdmission.Checked) (package : BendWorldSource.Package)
    (claim : Claim) : Except String (Selected core package claim) := do
  let some sourceModule := package.modules[claim.moduleIndex]?
    | throw "method source module is absent"
  if exactModule : package.modules[claim.moduleIndex]? = some sourceModule then
    if exactSource : BendWorldSource.sourceId sourceModule.bytes = claim.source then
      if spanBound : claim.startByte ≤ claim.endByte ∧
          claim.endByte ≤ sourceModule.bytes.length then
        let entry ← BendCoreAdmission.entry core claim.coreEntry
        if exactEntry : entry.name = claim.coreEntry then
          pure ⟨sourceModule, exactModule, exactSource, spanBound, entry, exactEntry⟩
        else throw "method checked entry differs"
      else throw "method source span is outside exact source bytes"
    else throw "method source revision differs"
  else throw "method source module differs"

def Selected.body {core : BendCoreAdmission.Checked} {package : BendWorldSource.Package}
    {claim : Claim} (selected : Selected core package claim) : Minidregg.Theory.BendTT.Term :=
  selected.entry.definition.v
def Selected.signature {core : BendCoreAdmission.Checked} {package : BendWorldSource.Package}
    {claim : Claim} (selected : Selected core package claim) : Minidregg.Theory.BendTT.Term :=
  selected.entry.definition.T

theorem selected_definition {core : BendCoreAdmission.Checked} {package : BendWorldSource.Package}
    {claim : Claim} (selected : Selected core package claim) :
    Book.get core.book claim.coreEntry = some selected.entry.definition := by
  rw [← selected.exactEntry]
  exact selected.entry.exact

end Minidregg.Compiler.BendMethodAttribution
