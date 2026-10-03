# Domain/source/activity views of one admitted service commons object.
# Surface values expose independently admitted observations and native prepared
# intents; they do not enable authority or synthesize provider truth.
import Base
import ./WorldSurface.bend as World
import ./ResidentServiceCommons.bend as Service

type ActivityLink is Data:
  NoActivity{}
  Existing{run: Service.Run, requestCell: Nat, sequence: Nat,
    assignedResident: Nat, nativeOperation: List<&2, Nat>}

def existing(+run: Service.Run) -> ActivityLink:
  match run:
    case Service.Run{identity, cell, sequence, assigned, operation, activity, ordinal, binding}:
      Existing{run, cell, sequence, assigned, operation}

def activity_link(state: Service.State) -> ActivityLink:
  match state:
    case Service.Vacant{}:
      NoActivity{}
    case Service.Held{reservation}:
      NoActivity{}
    case Service.Running{reservation, run}:
      existing(run)
    case Service.Uncertain{reservation, run}:
      existing(run)
    case Service.Delivered{reservation, run, completion}:
      existing(run)
    case Service.Finished{reservation, run, completion, review}:
      existing(run)
    case Service.Cancelled{reservation}:
      NoActivity{}

type Labels is Data:
  Labels{title: List<&2, Nat>, quote: List<&2, Nat>, providerClaim: List<&2, Nat>,
    sponsorDecision: List<&2, Nat>, request: List<&2, Nat>, home: List<&2, Nat>,
    completion: List<&2, Nat>, recipientReview: List<&2, Nat>, activity: List<&2, Nat>,
    action: List<&2, Nat>}

type Slots is Data:
  Slots{quote: Nat, providerClaim: Nat, sponsorDecision: Nat, request: Nat,
    home: Nat, completion: Nat, recipientReview: Nat, activity: Nat}

# Separate rows preserve sponsor approval, provider claims, observed completion
# and recipient review. A green sponsor decision never labels the answer true.
def domain_face(artifact: List<&2, Nat>, exportName: List<&2, Nat>, labels: Labels,
    slots: Slots, action: World.Intent) -> World.Surface:
  match labels slots:
    case Labels{title, quote, providerClaim, sponsor, request, home, completion, review, activity, actionLabel}
        Slots{quoteSlot, claimSlot, sponsorSlot, requestSlot, homeSlot, completionSlot, reviewSlot, activitySlot}:
      World.Surface{artifact, exportName,
        [World.Node{1n, quoteSlot, quote, Nil{}},
         World.Node{1n, claimSlot, providerClaim, Nil{}},
         World.Node{1n, sponsorSlot, sponsor, Nil{}},
         World.Node{2n, requestSlot, request, Nil{}},
         World.Node{2n, homeSlot, home, Nil{}},
         World.Node{1n, completionSlot, completion, Nil{}},
         World.Node{1n, reviewSlot, review, Nil{}},
         World.Node{1n, activitySlot, activity, Nil{}},
         World.Node{3n, 0n, actionLabel, Nil{}},
         World.Node{4n, 0n, title, [0n,1n,2n,3n,4n,5n,6n,7n,8n]}],
        9n, [action]}

def source_face(artifact: List<&2, Nat>, exportName: List<&2, Nat>,
    sourceLabel: List<&2, Nat>, activityLabel: List<&2, Nat>, title: List<&2, Nat>,
    sourceSlot: Nat, activitySlot: Nat, intents: List<&2, World.Intent>) -> World.Surface:
  World.source_face(artifact, exportName, sourceLabel, activityLabel, title,
    sourceSlot, activitySlot, intents)

# Recovery controls are existing native lookup/reconciliation intents. The UI
# supplies no retry callback, raw provider credentials, worker checkpoint or URL.
def activity_face(artifact: List<&2, Nat>, exportName: List<&2, Nat>,
    title: List<&2, Nat>, requestLabel: List<&2, Nat>, pendingLabel: List<&2, Nat>,
    outcomeLabel: List<&2, Nat>, recoveryLabel: List<&2, Nat>,
    requestSlot: Nat, pendingSlot: Nat, outcomeSlot: Nat, recovery: World.Intent) -> World.Surface:
  World.Surface{artifact, exportName,
    [World.Node{2n, requestSlot, requestLabel, Nil{}},
     World.Node{1n, pendingSlot, pendingLabel, Nil{}},
     World.Node{1n, outcomeSlot, outcomeLabel, Nil{}},
     World.Node{3n, 0n, recoveryLabel, Nil{}},
     World.Node{4n, 0n, title, [0n,1n,2n,3n]}], 4n, [recovery]}

law uncertainty_keeps_activity:
  for reservation: Service.Reservation
  for +run: Service.Run
  {activity_link(Service.Uncertain{reservation, run}) == existing(run) : ActivityLink}

def uncertainty_keeps_activity(reservation, run):
  {==}

law delivery_keeps_activity:
  for reservation: Service.Reservation
  for +run: Service.Run
  for completion: Service.Completion
  {activity_link(Service.Delivered{reservation, run, completion}) == existing(run) : ActivityLink}

def delivery_keeps_activity(reservation, run, completion):
  {==}

# Same artifact/export identity pins source inspection to the authored domain face.
def KeepsSource(-artifact: List<&2, Nat>, -exportName: List<&2, Nat>, surface: World.Surface) -> Type:
  match surface:
    case World.Surface{actualArtifact, actualExport, nodes, root, intents}:
      Pair({actualArtifact == artifact : List<&2, Nat>}, {actualExport == exportName : List<&2, Nat>})

law domain_source_bound:
  for +artifact: List<&2, Nat>
  for +exportName: List<&2, Nat>
  for labels: Labels
  for slots: Slots
  for action: World.Intent
  KeepsSource(artifact, exportName, domain_face(artifact, exportName, labels, slots, action))

def domain_source_bound(artifact, exportName, labels, slots, action):
  match labels slots:
    case Labels{title, quote, claim, sponsor, request, home, completion, review, activity, actionLabel}
        Slots{quoteSlot, claimSlot, sponsorSlot, requestSlot, homeSlot, completionSlot, reviewSlot, activitySlot}:
      ({==}, {==})

