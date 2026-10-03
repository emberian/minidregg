# Shared version/activity interface for a community or an authored world.
# References identify immutable published source. Display personas are credits,
# never authenticated principals, electorate members, grants or payment accounts.
import Base
import ./CatalogReview.bend as Review

type Scope is Data:
  FictionCanon{}
  WorldRules{}
  CommunityTool{}

type VersionRef is Data:
  VersionRef{candidate: Review.Candidate, logicalExport: List<&2, Nat>}

type Credit is Data:
  Credit{principal: List<&2, Nat>, persona: List<&2, Nat>}

type PinnedUse is Data:
  PinnedUse{instance: Nat, instanceRoot: List<&2, Nat>, version: VersionRef}

type ActivityKind is Data:
  SourceProposed{}
  Endorsed{yes: Bool}
  DecisionClosed{}
  AdoptionPrepared{}

type Activity is Data:
  Activity{scope: Scope, version: VersionRef, round: List<&2, Nat>,
    credit: Credit, kind: ActivityKind}

type ActivityOutput is Data:
  NoActivity{}
  AppendActivity{event: Activity}

def version_eq(a: VersionRef, b: VersionRef) -> Bool:
  match a b:
    case VersionRef{candidateA, exportA} VersionRef{candidateB, exportB}:
      Bool.and(Review.candidate_eq(candidateA, candidateB), Bytes.eq(exportA, exportB))

# An existing instance keeps its immutable source pin. Adoption selects the
# default for fresh instances; migrating an old instance is a separate decision.
def preserve_uses(uses: List<&2, PinnedUse>) -> List<&2, PinnedUse>:
  uses

law preserved_uses_exact:
  for +uses: List<&2, PinnedUse>
  {preserve_uses(uses) == uses : List<&2, PinnedUse>}

def preserved_uses_exact(uses):
  {==}

# The producer binds logicalExport to the actual package export. This function
# retains that declaration; an arbitrary export label does not install a method.
def candidate_of(version: VersionRef) -> Review.Candidate:
  match version:
    case VersionRef{candidate, logicalExport}:
      candidate

def credit_principal(credit: Credit) -> List<&2, Nat>:
  match credit:
    case Credit{principal, persona}:
      principal

def credits_to(credit: Credit, actor: List<&2, Nat>) -> Bool:
  Bytes.eq(credit_principal(credit), actor)

law persona_never_changes_principal:
  for +principal: List<&2, Nat>
  for persona: List<&2, Nat>
  {credit_principal(Credit{principal, persona}) == principal : List<&2, Nat>}

def persona_never_changes_principal(principal, persona):
  {==}
