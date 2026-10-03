# Reusable readable inhabited-world faces through the ONE generic WorldSurface.
# Slots reference individually native-authorized observations; source supplies
# prose and indices, never a private value, enabled flag, URL or action grant.
import Base
import ./WorldSurface.bend as Surface

# Room, player roster, shared props/supply and exact admitted history are
# independent live slots. The action node pins one independently prepared intent.
def room(artifact: List<&2, Nat>, exportName: List<&2, Nat>,
    title: List<&2, Nat>, roomLabel: List<&2, Nat>, peopleLabel: List<&2, Nat>,
    thingsLabel: List<&2, Nat>, historyLabel: List<&2, Nat>, nextLabel: List<&2, Nat>,
    roomSlot: Nat, peopleSlot: Nat, thingsSlot: Nat, historySlot: Nat,
    nextIntent: Nat, intents: List<&2, Surface.Intent>) -> Surface.Surface:
  Surface.Surface{artifact, exportName,
    [Surface.Node{2n, roomSlot, roomLabel, Nil{}},
     Surface.Node{1n, peopleSlot, peopleLabel, Nil{}},
     Surface.Node{1n, thingsSlot, thingsLabel, Nil{}},
     Surface.Node{1n, historySlot, historyLabel, Nil{}},
     Surface.Node{3n, nextIntent, nextLabel, Nil{}},
     Surface.Node{4n, 0n, title, [0n, 1n, 2n, 3n, 4n]}],
    5n, intents}

# The same source/rules/decision/invitation slots serve text or app views. A
# visible invitation is a source fact; only its current native law grants join.
def authoring(artifact: List<&2, Nat>, exportName: List<&2, Nat>,
    title: List<&2, Nat>, sourceLabel: List<&2, Nat>, proposalLabel: List<&2, Nat>,
    decisionLabel: List<&2, Nat>, invitationsLabel: List<&2, Nat>,
    sourceSlot: Nat, proposalSlot: Nat, decisionSlot: Nat, invitationsSlot: Nat,
    intents: List<&2, Surface.Intent>) -> Surface.Surface:
  Surface.Surface{artifact, exportName,
    [Surface.Node{2n, sourceSlot, sourceLabel, Nil{}},
     Surface.Node{2n, proposalSlot, proposalLabel, Nil{}},
     Surface.Node{1n, decisionSlot, decisionLabel, Nil{}},
     Surface.Node{1n, invitationsSlot, invitationsLabel, Nil{}},
     Surface.Node{4n, 0n, title, [0n, 1n, 2n, 3n]}],
    4n, intents}

# GM context is a bounded source/rules/shared-state/history view. Narration and
# action suggestions remain separate ordinary outputs handled by resident custody.
def resident(artifact: List<&2, Nat>, exportName: List<&2, Nat>,
    title: List<&2, Nat>, rulesLabel: List<&2, Nat>, sharedLabel: List<&2, Nat>,
    historyLabel: List<&2, Nat>, narrationLabel: List<&2, Nat>,
    rulesSlot: Nat, sharedSlot: Nat, historySlot: Nat, narrationSlot: Nat,
    intents: List<&2, Surface.Intent>) -> Surface.Surface:
  Surface.Surface{artifact, exportName,
    [Surface.Node{2n, rulesSlot, rulesLabel, Nil{}},
     Surface.Node{1n, sharedSlot, sharedLabel, Nil{}},
     Surface.Node{1n, historySlot, historyLabel, Nil{}},
     Surface.Node{2n, narrationSlot, narrationLabel, Nil{}},
     Surface.Node{4n, 0n, title, [0n, 1n, 2n, 3n]}],
    4n, intents}
