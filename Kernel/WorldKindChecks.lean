/- Narrow executable refutations for descriptor and instance preparation.
These are not native admission journeys. -/
import Kernel.WorldKindInstance

namespace Minidregg.Kernel.WorldKindChecks

open Minidregg.Compiler
open Minidregg.Compiler.WorldKindDescriptor
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.WorldKindInstance

def poll : Descriptor :=
  ⟨500, 0,
    [⟨1, "question", "The question this poll asks", .bytes, .rom⟩,
     ⟨2, "votes", "Each subject's recorded choice", .natural, .appendOnly⟩,
     ⟨3, "open", "Whether this poll accepts votes", .natural, .ram⟩]⟩

def emptyPoll : Instance := ⟨poll, by decide, 0⟩

#guard (decodeDefinition (descriptorCodec.encode poll)).isSome
#guard !(decodeDefinition (descriptorCodec.encode { poll with
  fields := poll.fields ++ [⟨2, "duplicate", "Duplicates the votes field", .natural, .ram⟩] })).isSome
#guard !(decodeDefinition (descriptorCodec.encode { poll with
  fields := [⟨1, "", "Meaning", .natural, .ram⟩] })).isSome
#guard !(decodeDefinition (descriptorCodec.encode { poll with
  fields := [⟨1, "title", "", .natural, .ram⟩] })).isSome
#guard !(decodeDefinition (descriptorCodec.encode poll ++ [0])).isSome
#guard (decode (encode emptyPoll)).isSome
#guard !(decode (encode emptyPoll ++ [0])).isSome

/- No operation invents a field or writes ROM after birth. -/
#guard !(prepare emptyPoll [.create 99 0 (StreamCodec.nat.encode 1)]).isSome
#guard !(prepare emptyPoll [.create 1 0 (bytesStream.encode [65])]).isSome
#guard !(prepare emptyPoll [.create 2 7 [255, 0]]).isSome
#guard (prepare emptyPoll [.create 2 7 (StreamCodec.nat.encode 1)]).isSome
#guard !(prepare emptyPoll [.create 2 7 (StreamCodec.nat.encode 1),
  .write 2 7 (StreamCodec.nat.encode 1) (StreamCodec.nat.encode 2)]).isSome
#guard !(prepare emptyPoll [.create 2 7 (StreamCodec.nat.encode 1),
  .create 2 7 (StreamCodec.nat.encode 2)]).isSome
#guard (prepare emptyPoll [.create 3 0 (StreamCodec.nat.encode 1),
  .write 3 0 (StreamCodec.nat.encode 1) (StreamCodec.nat.encode 0)]).isSome
#guard !(prepare emptyPoll [.create 3 0 (StreamCodec.nat.encode 1),
  .write 3 0 (StreamCodec.nat.encode 2) (StreamCodec.nat.encode 0)]).isSome

/- Merely retaining a field's integer codec and address does not preserve its
meaning. The descriptor and StoreCodec frame both change. -/
def changedMeaning : Descriptor :=
  { poll with fields := [⟨3, "membership", "Membership administration", .natural, .ram⟩] }

#guard descriptorCodec.encode poll != descriptorCodec.encode changedMeaning
#guard StoreCodec.frame (wire poll) != StoreCodec.frame (wire changedMeaning)

end Minidregg.Kernel.WorldKindChecks
