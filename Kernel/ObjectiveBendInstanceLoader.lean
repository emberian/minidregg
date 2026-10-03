/- Actual finite Objective Bend object loading. Canonical pin decoding alone
never authorizes execution: this loader reflects every immutable partial,
constructs lawful complete behavior, admits the exact linked Bend Book and
matches its canonical bytes. The existing native world carrier retains state. -/
import Compiler.ObjectiveBendInstance
import Compiler.ObjectiveBendConstruction

namespace Minidregg.Kernel.ObjectiveBendInstanceLoader
open Minidregg.Compiler
open Minidregg.Compiler.WorldKindDescriptor
open Minidregg.Compiler.ObjectiveBendInstance
open Minidregg.Theory.BendTT
set_option autoImplicit false

def pinSpace (descriptor : Descriptor) : Option (PinSpace descriptor) := do
  let candidates := (List.finRange descriptor.fields.length).filter fun index =>
    (descriptor.fields.get index).meaning == pinMeaning
  let [index] := candidates | none
  if bytes : (descriptor.fields.get index).codec = .bytes then
    if immutable : (descriptor.fields.get index).discipline = .rom then
      if meaning : (descriptor.fields.get index).meaning = pinMeaning then
        some ⟨index, bytes, immutable, meaning⟩
      else none
    else none
  else none

/-- Helpers are the actual checked source package's dependency Book, not a
method-name evaluator or a Boolean assertion of source correspondence. Source
attribution of helpers to package bytes remains the shared publication join. -/
def loadPin (helpers : Book) (pin : Pin) : Except String (Loaded pin) := do
  match reflected : pin.prototypes.mapM ObjectiveBendPrototype.reflect with
  | .error reason => throw reason
  | .ok specs =>
    let some root := specs.getLast? | throw "empty immutable prototype closure"
    let construction ← (ObjectiveBendConstruction.construct helpers root specs).mapError
      (fun refusal => s!"prototype construction refused: {repr refusal}")
    if exactLayers : construction.layers = specs then
      if exactCore : pin.core = construction.core.bytes then
        if exactRoot : rootId pin = some construction.root.id then
          pure ⟨construction, by simpa only [exactLayers] using reflected, exactRoot, exactCore⟩
        else throw "pinned root differs from constructed prototype"
      else throw "pinned core differs from actual constructed Book"
    else throw "constructed source layers differ from immutable closure"

structure LoadedStore (store : Minidregg.Theory.Store.Store WorldKindCell.instanceLayout) where
  object : ObjectiveBendInstance.Instance
  native : WorldKindCell.instanceAt store = some object.value

/-- Decodes the ACTUAL native object carrier. The registry's authenticated
materializer/root and current authority must be retained by the call binder;
this pure loader does not turn caller bytes into an authenticated resource. -/
def load (helpers : Book) (store : Minidregg.Theory.Store.Store WorldKindCell.instanceLayout) :
    Except String (LoadedStore store) := do
  match native : WorldKindCell.instanceAt store with
  | none => throw "invalid native world object"
  | some value =>
    let some space := pinSpace value.descriptor | throw "missing semantic ROM prototype pin"
    match pinned : pinAt value space with
    | none => throw "invalid canonical object prototype pin"
    | some pin =>
      let source ← loadPin helpers pin
      pure ⟨⟨value, space, pin, pinned, source⟩, native⟩

end Minidregg.Kernel.ObjectiveBendInstanceLoader
