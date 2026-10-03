# Two authored faces of the same workshop, using the shared WorldSurface types.
# The input slots are independently admitted observations. Actions reference
# independently prepared native intents. There are no raw private values,
# hidden object lookups, per-domain renderer handlers or authored enabled bits.
import Base
import ./WorldSurface.bend as World

def domain_face(artifact: List<&2, Nat>, exportName: List<&2, Nat>,
    title: List<&2, Nat>, catalogLabel: List<&2, Nat>, capacityLabel: List<&2, Nat>,
    reviewLabel: List<&2, Nat>, requestLabel: List<&2, Nat>, adoptLabel: List<&2, Nat>,
    catalogSlot: Nat, capacitySlot: Nat, reviewSlot: Nat,
    requestReview: World.Intent, proposeAdoption: World.Intent) -> World.Surface:
  World.Surface{artifact, exportName,
    [World.Node{2n, catalogSlot, catalogLabel, Nil{}},
     World.Node{1n, capacitySlot, capacityLabel, Nil{}},
     World.Node{1n, reviewSlot, reviewLabel, Nil{}},
     World.Node{3n, 0n, requestLabel, Nil{}},
     World.Node{3n, 1n, adoptLabel, Nil{}},
     World.Node{4n, 0n, title, [0n, 1n, 2n, 3n, 4n]}],
    5n, [requestReview, proposeAdoption]}

def source_face(artifact: List<&2, Nat>, exportName: List<&2, Nat>,
    sourceLabel: List<&2, Nat>, activityLabel: List<&2, Nat>, title: List<&2, Nat>,
    sourceSlot: Nat, activitySlot: Nat, intents: List<&2, World.Intent>) -> World.Surface:
  World.source_face(artifact, exportName, sourceLabel, activityLabel, title,
    sourceSlot, activitySlot, intents)

def KeepsBinding(-artifact: List<&2, Nat>, -exportName: List<&2, Nat>,
    result: World.Surface) -> Type:
  match result:
    case World.Surface{selectedArtifact, selectedExport, nodes, root, intents}:
      Pair({selectedArtifact == artifact : List<&2, Nat>},
        {selectedExport == exportName : List<&2, Nat>})

law domain_binding:
  for +artifact: List<&2, Nat>
  for +exportName: List<&2, Nat>
  for title: List<&2, Nat>
  for catalogLabel: List<&2, Nat>
  for capacityLabel: List<&2, Nat>
  for reviewLabel: List<&2, Nat>
  for requestLabel: List<&2, Nat>
  for adoptLabel: List<&2, Nat>
  for catalogSlot: Nat
  for capacitySlot: Nat
  for reviewSlot: Nat
  for requestReview: World.Intent
  for proposeAdoption: World.Intent
  KeepsBinding(artifact, exportName, domain_face(artifact, exportName,
    title, catalogLabel, capacityLabel, reviewLabel, requestLabel, adoptLabel,
    catalogSlot, capacitySlot, reviewSlot, requestReview, proposeAdoption))

def domain_binding(artifact, exportName, title, catalogLabel, capacityLabel,
    reviewLabel, requestLabel, adoptLabel, catalogSlot, capacitySlot, reviewSlot,
    requestReview, proposeAdoption):
  ({==}, {==})
