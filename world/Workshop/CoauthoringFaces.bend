# A shared coauthoring institution's working face. Every mount/value slot is an
# individually admitted native observation. Each action names an independently
# prepared exact native intent; editor labels never create rights.
import Base
import ./WorldSurface.bend as World

def institution_face(artifact: List<&2, Nat>, exportName: List<&2, Nat>,
    title: List<&2, Nat>, sourceLabel: List<&2, Nat>, proposalLabel: List<&2, Nat>,
    decisionLabel: List<&2, Nat>, historyLabel: List<&2, Nat>,
    instancesLabel: List<&2, Nat>, proposeLabel: List<&2, Nat>,
    endorseLabel: List<&2, Nat>, decideLabel: List<&2, Nat>,
    adoptLabel: List<&2, Nat>, freshLabel: List<&2, Nat>,
    sourceSlot: Nat, proposalSlot: Nat, decisionSlot: Nat, historySlot: Nat,
    instancesSlot: Nat, propose: World.Intent, endorse: World.Intent,
    decide: World.Intent, adopt: World.Intent, fresh: World.Intent) -> World.Surface:
  World.Surface{artifact, exportName,
    [World.Node{2n, sourceSlot, sourceLabel, Nil{}},
     World.Node{2n, proposalSlot, proposalLabel, Nil{}},
     World.Node{1n, decisionSlot, decisionLabel, Nil{}},
     World.Node{2n, historySlot, historyLabel, Nil{}},
     World.Node{2n, instancesSlot, instancesLabel, Nil{}},
     World.Node{3n, 0n, proposeLabel, Nil{}},
     World.Node{3n, 1n, endorseLabel, Nil{}},
     World.Node{3n, 2n, decideLabel, Nil{}},
     World.Node{3n, 3n, adoptLabel, Nil{}},
     World.Node{3n, 4n, freshLabel, Nil{}},
     World.Node{4n, 0n, title, [0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n, 9n]}],
    10n, [propose, endorse, decide, adopt, fresh]}

# Shared Studio mounts native source and append history. It can expose the same
# revision process without a station metaphor, and existing pinned instances
# keep their authored source rather than silently following a new default.
def source_activity_face(artifact: List<&2, Nat>, exportName: List<&2, Nat>,
    sourceLabel: List<&2, Nat>, activityLabel: List<&2, Nat>, title: List<&2, Nat>,
    sourceSlot: Nat, activitySlot: Nat, intents: List<&2, World.Intent>) -> World.Surface:
  World.source_face(artifact, exportName, sourceLabel, activityLabel, title,
    sourceSlot, activitySlot, intents)
