# Objective Bend source interface for the generic admitted-observation surface.
# The required native bridge encodes these typed values through BendWorldSurface.lean.
# Its admission must check byte/digest bounds, backwards node indices, admitted slots,
# and exact independently prepared intent bindings before showing any action.
# A Surface is a presentation value. It creates no resource read or permission.
import Base

type Intent is Data:
  Intent{artifact: List<&2, Nat>, exportName: List<&2, Nat>,
    program: List<&2, Nat>, instance: Nat, expectedRoot: List<&2, Nat>,
    arguments: List<&2, Nat>}

# tag 0 = authored prose; 1 = admitted value; 2 = admitted doc/object mount;
# 3 = action referencing intents[slot]; 4 = group of earlier child nodes.
# Observation indices address the declared, individually admitted input vector.
# No world name, raw observation bytes, URL, script, or enabled flag is accepted.
type Node is Data:
  Node{tag: Nat, slot: Nat, label: List<&2, Nat>, children: List<&2, Nat>}

type Surface is Data:
  Surface{artifact: List<&2, Nat>, exportName: List<&2, Nat>,
    nodes: List<&2, Node>, root: Nat, intents: List<&2, Intent>}

# Two reusable faces over the same admitted object inputs. The labels and exact
# artifact/export bindings are supplied by authored code, not renderer handlers.
def board_face(artifact: List<&2, Nat>, exportName: List<&2, Nat>,
    summaryLabel: List<&2, Nat>, sourceLabel: List<&2, Nat>, title: List<&2, Nat>,
    summarySlot: Nat, sourceSlot: Nat, intents: List<&2, Intent>) -> Surface:
  Surface{artifact, exportName,
    Con{Node{1n, summarySlot, summaryLabel, Nil{}},
      Con{Node{2n, sourceSlot, sourceLabel, Nil{}},
        Con{Node{4n, 0n, title, Con{0n, Con{1n, Nil{}}}}, Nil{}}}},
    2n, intents}

def source_face(artifact: List<&2, Nat>, exportName: List<&2, Nat>,
    sourceLabel: List<&2, Nat>, activityLabel: List<&2, Nat>, title: List<&2, Nat>,
    sourceSlot: Nat, activitySlot: Nat, intents: List<&2, Intent>) -> Surface:
  Surface{artifact, exportName,
    Con{Node{2n, sourceSlot, sourceLabel, Nil{}},
      Con{Node{1n, activitySlot, activityLabel, Nil{}},
        Con{Node{4n, 0n, title, Con{0n, Con{1n, Nil{}}}}, Nil{}}}},
    2n, intents}
