# Reusable coauthoring institution. Ballots and installation decisions come
# from the existing CollectiveAdoption program; there is no second proposal
# store, kernel, evaluator, actor authority, or payment system here.
#
# Native receiving supplies the actual current source/root images and actor.
# Returned predecessor/successor/activity data is lowered through the shared
# typed Plan: current-definition transition plus existing document append.
# Preparing a transition is not admitting it. Source/history documents remain
# native held resources; this program does not maintain a private shadow journal.
import Base
import ./CatalogReview.bend as Review
import ./ReusableWorkshop.bend as Workshop
import ./CollectiveAdoption.bend as Collective
import ./MarketMath.bend as Math
import ./WorldCoauthoring.bend as World

type Charter is Data:
  Charter{policy: List<&2, Nat>, proposers: List<&2, List<&2, Nat>>,
    editors: List<&2, List<&2, Nat>>}

# The single existing Proposal is inside ballots. Scope/export/credit are
# authored descriptive context, not a duplicate proposal or authority store.
type Offer is Data:
  Offer{scope: World.Scope, logicalExport: List<&2, Nat>,
    author: World.Credit, ballots: Collective.Ballots}

type Submission is Data:
  SubmissionRefused{}
  SubmissionPrepared{offer: Offer, activity: World.ActivityOutput}

type EndorsementTurn is Data:
  EndorsementTurn{cast: Collective.CastResult, activity: World.ActivityOutput}

type DecisionTurn is Data:
  DecisionTurn{resolution: Collective.Resolution, activity: World.ActivityOutput}

type AdoptionTurn is Data:
  AdoptionTurn{installation: Collective.Installation,
    preserved: List<&2, World.PinnedUse>, activity: World.ActivityOutput}

def offer_version(offer: Offer) -> World.VersionRef:
  match offer:
    case Offer{scope, logicalExport, author, Collective.Ballots{proposal, votes, closed}}:
      match proposal:
        case Collective.Proposal{round, base, candidate, basePrototype, candidatePrototype,
            baseKindRoot, instanceRoot, migration, policy, electorate, quorum}:
          World.VersionRef{candidate, logicalExport}

def offer_round(offer: Offer) -> List<&2, Nat>:
  match offer:
    case Offer{scope, logicalExport, author, Collective.Ballots{proposal, votes, closed}}:
      match proposal:
        case Collective.Proposal{round, base, candidate, basePrototype, candidatePrototype,
            baseKindRoot, instanceRoot, migration, policy, electorate, quorum}:
          round

def offer_policy(offer: Offer) -> List<&2, Nat>:
  match offer:
    case Offer{scope, logicalExport, author, Collective.Ballots{proposal, votes, closed}}:
      match proposal:
        case Collective.Proposal{round, base, candidate, basePrototype, candidatePrototype,
            baseKindRoot, instanceRoot, migration, policy, electorate, quorum}:
          policy

def offer_ballots(offer: Offer) -> Collective.Ballots:
  match offer:
    case Offer{scope, logicalExport, author, ballots}:
      ballots

def event(+offer: Offer, credit: World.Credit, kind: World.ActivityKind) -> World.Activity:
  match offer:
    case Offer{scope, logicalExport, author, ballots}:
      World.Activity{scope, offer_version(offer), offer_round(offer), credit, kind}

def proposal_source_known(+candidate: Review.Candidate, lookup: Workshop.Lookup) -> Bool:
  match lookup:
    case Workshop.Missing{}:
      False{}
    case Workshop.Found{catalogued, label}:
      Review.candidate_eq(candidate, catalogued)

def submit_choice(offer: Offer, allowed: Bool) -> Submission:
  match allowed:
    case False{}:
      SubmissionRefused{}
    case True{}:
      match offer:
        case Offer{scope, logicalExport, +author, ballots}:
          SubmissionPrepared{offer, World.AppendActivity{event(offer, author, World.SourceProposed{})}}

# final_catalog is a replaceable authored partial-spec demand. The source
# admission/package producer, not a request Boolean, binds publication provenance.
# Revision numbers strictly advance, policy is exact, and attribution must name
# the authenticated actor. In-fiction persona never supplies that identity.
def submit(charter: Charter, final_catalog: @+key: Review.Candidate -> Workshop.Lookup,
    +actor: List<&2, Nat>, scope: World.Scope, logicalExport: List<&2, Nat>,
    credit: World.Credit, +proposal: Collective.Proposal) -> Submission:
  match charter proposal:
    case Charter{charterPolicy, proposers, editors}
        Collective.Proposal{round, +base, +candidate, basePrototype, candidatePrototype,
          baseKindRoot, instanceRoot, migration, policy, electorate, quorum}:
      match base candidate:
        case Review.Candidate{baseSource, baseProgram, oldRevision}
            Review.Candidate{source, program, newRevision}:
          +ballots = {Collective.Ballots{proposal, Nil{}, False{}} : Collective.Ballots}
          submit_choice(Offer{scope, logicalExport, credit, ballots},
            Bool.and(World.credits_to(credit, actor),
              Bool.and(Collective.member(actor, proposers),
                Bool.and(Bytes.eq(charterPolicy, policy),
                  Bool.and(Math.lt(oldRevision, newRevision),
                    Bool.and(Collective.valid(ballots),
                      proposal_source_known(candidate, final_catalog(candidate))))))))

def endorsement_activity(+offer: Offer, credit: World.Credit,
    cast: Collective.CastResult, yes: Bool) -> World.ActivityOutput:
  match cast:
    case Collective.CastRefused{unchanged}:
      World.NoActivity{}
    case Collective.CastAccepted{expected, successor, yesCount, totalCount}:
      World.AppendActivity{event(offer, credit, World.Endorsed{yes})}

# Delegate distinct actor/round checks to Collective.cast. No endorsement is
# copied from persona, prose, or a passed yes-count. The exact ballot predecessor
# must be consumed atomically with the accepted successor by native receiving.
def endorse(+offer: Offer, +actor: List<&2, Nat>, persona: List<&2, Nat>,
    round: List<&2, Nat>, +yes: Bool) -> EndorsementTurn:
  match offer:
    case Offer{scope, logicalExport, author, ballots}:
      +cast = {Collective.cast(ballots, actor, round, yes) : Collective.CastResult}
      EndorsementTurn{cast, endorsement_activity(offer, World.Credit{actor, persona}, cast, yes)}

def decision_activity(+offer: Offer, credit: World.Credit,
    resolution: Collective.Resolution) -> World.ActivityOutput:
  match resolution:
    case Collective.Unresolved{unchanged}:
      World.NoActivity{}
    case Collective.Resolved{expected, successor, decision}:
      World.AppendActivity{event(offer, credit, World.DecisionClosed{})}

def decide(charter: Charter, +offer: Offer, +actor: List<&2, Nat>,
    persona: List<&2, Nat>) -> DecisionTurn:
  match charter offer:
    case Charter{policy, proposers, editors} Offer{scope, logicalExport, author, +ballots}:
      match Bool.and(Collective.member(actor, editors), Bytes.eq(policy, offer_policy(offer))):
        case False{}:
          DecisionTurn{Collective.Unresolved{ballots}, World.NoActivity{}}
        case True{}:
          +resolution = {Collective.resolve(ballots) : Collective.Resolution}
          DecisionTurn{resolution, decision_activity(offer, World.Credit{actor, persona}, resolution)}

def adoption_activity(+offer: Offer, credit: World.Credit,
    installation: Collective.Installation) -> World.ActivityOutput:
  match installation:
    case Collective.InstallRefused{}:
      World.NoActivity{}
    case Collective.InstallProposal{adoption, binding}:
      World.AppendActivity{event(offer, credit, World.AdoptionPrepared{})}

# final_review is the actual composed reviewer callback. Decision quorum does
# not replace it, and an editor's role does not grant native install/payment rights.
# Existing instances are returned unchanged; only the current default advances.
# Native lowering must prohibit writes to those pins and retain old source refs.
def prepare_adoption(charter: Charter,
    final_review: @+key: Review.Candidate -> Review.Recommendation,
    +offer: Offer, +actor: List<&2, Nat>, persona: List<&2, Nat>,
    current: Review.Candidate, currentPrototype: List<&2, Nat>,
    currentKindRoot: List<&2, Nat>, currentInstanceRoot: List<&2, Nat>,
    migration: List<&2, Nat>, uses: List<&2, World.PinnedUse>) -> AdoptionTurn:
  match charter offer:
    case Charter{policy, proposers, editors} Offer{scope, logicalExport, author, ballots}:
      match Bool.and(Collective.member(actor, editors), Bytes.eq(policy, offer_policy(offer))):
        case False{}:
          AdoptionTurn{Collective.InstallRefused{}, World.preserve_uses(uses), World.NoActivity{}}
        case True{}:
          +candidate = {World.candidate_of(offer_version(offer)) : Review.Candidate}
          +installation = {Collective.prepare_install(ballots, current, currentPrototype,
            currentKindRoot, currentInstanceRoot, migration, final_review(candidate)) : Collective.Installation}
          AdoptionTurn{installation, World.preserve_uses(uses),
            adoption_activity(offer, World.Credit{actor, persona}, installation)}

def OfferBinding(offer: Offer, version: World.VersionRef) -> Type:
  match offer version:
    case Offer{scope, logicalExport, author, Collective.Ballots{proposal, votes, closed}}
        World.VersionRef{selected, selectedExport}:
      match proposal:
        case Collective.Proposal{round, base, candidate, basePrototype, candidatePrototype,
            baseKindRoot, instanceRoot, migration, policy, electorate, quorum}:
          Pair({selected == candidate : Review.Candidate},
            {selectedExport == logicalExport : List<&2, Nat>})

law offered_version_exact:
  for +offer: Offer
  OfferBinding(offer, offer_version(offer))

def offered_version_exact(offer):
  match offer:
    case Offer{scope, logicalExport, author, Collective.Ballots{proposal, votes, closed}}:
      match proposal:
        case Collective.Proposal{round, base, candidate, basePrototype, candidatePrototype,
            baseKindRoot, instanceRoot, migration, policy, electorate, quorum}:
          ({==}, {==})

def cast_of(turn: EndorsementTurn) -> Collective.CastResult:
  match turn:
    case EndorsementTurn{cast, activity}:
      cast

# Whole existing CastResult survives the wrapper, including exact predecessor,
# successor and derived unique-vote counts. The shared cast law remains usable.
law endorsement_delegates_exact_cast:
  for +offer: Offer
  for +actor: List<&2, Nat>
  for persona: List<&2, Nat>
  for +round: List<&2, Nat>
  for +yes: Bool
  {cast_of(endorse(offer, actor, persona, round, yes)) ==
    Collective.cast(offer_ballots(offer), actor, round, yes) : Collective.CastResult}

def endorsement_delegates_exact_cast(offer, actor, persona, round, yes):
  match offer:
    case Offer{scope, logicalExport, author, ballots}:
      {==}

law refused_submission_has_no_activity:
  for offer: Offer
  {submit_choice(offer, False{}) == SubmissionRefused{} : Submission}

def refused_submission_has_no_activity(offer):
  {==}

law refused_endorsement_has_no_activity:
  for offer: Offer
  for credit: World.Credit
  for unchanged: Collective.Ballots
  for yes: Bool
  {endorsement_activity(offer, credit, Collective.CastRefused{unchanged}, yes) ==
    World.NoActivity{} : World.ActivityOutput}

def refused_endorsement_has_no_activity(offer, credit, unchanged, yes):
  {==}

law refused_install_has_no_activity:
  for offer: Offer
  for credit: World.Credit
  {adoption_activity(offer, credit, Collective.InstallRefused{}) ==
    World.NoActivity{} : World.ActivityOutput}

def refused_install_has_no_activity(offer, credit):
  {==}
