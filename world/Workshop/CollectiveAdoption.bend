# Domain decisions over kernel-authenticated samples. No signatures or grants are
# fabricated here. The native receiver atomically installs the COMPLETE successor.
import Base
import ./CatalogReview.bend as Review
import ./MarketMath.bend as Math

type Proposal is Data:
  Proposal{round: List<&2, Nat>, base: Review.Candidate, candidate: Review.Candidate,
    basePrototype: List<&2, Nat>, candidatePrototype: List<&2, Nat>,
    baseKindRoot: List<&2, Nat>, instanceRoot: List<&2, Nat>,
    migration: List<&2, Nat>, policy: List<&2, Nat>,
    electorate: List<&2, List<&2, Nat>>, quorum: Nat}

type Vote is Data:
  Vote{subject: List<&2, Nat>, yes: Bool}

type Ballots is Data:
  Ballots{proposal: Proposal, votes: List<&2, Vote>, closed: Bool}

type CastResult is Data:
  CastRefused{unchanged: Ballots}
  CastAccepted{expected: Ballots, successor: Ballots, yesCount: Nat, totalCount: Nat}

type Resolution is Data:
  Unresolved{unchanged: Ballots}
  Resolved{expected: Ballots, successor: Ballots, decision: Review.Decision}

type Installation is Data:
  InstallRefused{}
  InstallProposal{adoption: Review.Adoption, binding: Proposal}

def member(+subject: List<&2, Nat>, electorate: List<&2, List<&2, Nat>>) -> Bool:
  match electorate:
    case Nil{}:
      False{}
    case Con{head, tail}:
      Math.choose_bool(True{}, member(subject, tail), Bytes.eq(subject, head))

def used(+subject: List<&2, Nat>, votes: List<&2, Vote>) -> Bool:
  match votes:
    case Nil{}:
      False{}
    case Con{Vote{voter, yes}, tail}:
      Math.choose_bool(True{}, used(subject, tail), Bytes.eq(subject, voter))

def yes_count(votes: List<&2, Vote>) -> Nat:
  match votes:
    case Nil{}:
      0n
    case Con{Vote{subject, yes}, tail}:
      match yes:
        case False{}:
          yes_count(tail)
        case True{}:
          Succ{yes_count(tail)}

def total_count(votes: List<&2, Vote>) -> Nat:
  match votes:
    case Nil{}:
      0n
    case Con{vote, tail}:
      Succ{total_count(tail)}

def electorate_count(electorate: List<&2, List<&2, Nat>>) -> Nat:
  match electorate:
    case Nil{}:
      0n
    case Con{subject, rest}:
      Succ{electorate_count(rest)}

def unique_electorate(electorate: List<&2, List<&2, Nat>>) -> Bool:
  match electorate:
    case Nil{}:
      True{}
    case Con{subject, +rest}:
      Bool.and(Math.not(member(subject, rest)), unique_electorate(rest))

def valid_votes(votes: List<&2, Vote>, +electorate: List<&2, List<&2, Nat>>) -> Bool:
  match votes:
    case Nil{}:
      True{}
    case Con{Vote{+subject, yes}, +rest}:
      Bool.and(member(subject, electorate),
        Bool.and(Math.not(used(subject, rest)), valid_votes(rest, electorate)))

def valid(state: Ballots) -> Bool:
  match state:
    case Ballots{proposal, votes, closed}:
      match proposal:
        case Proposal{round, base, candidate, basePrototype, candidatePrototype,
            baseKindRoot, instanceRoot, migration, policy, +electorate, +quorum}:
          Bool.and(unique_electorate(electorate),
            Bool.and(Math.lt(0n, quorum),
              Bool.and(Math.le(quorum, electorate_count(electorate)), valid_votes(votes, electorate))))

def cast_choice(+state: Ballots, subject: List<&2, Nat>, yes: Bool, allowed: Bool) -> CastResult:
  match state allowed:
    case state False{}:
      CastRefused{state}
    case Ballots{proposal, votes, closed} True{}:
      +next = {Con{Vote{subject, yes}, votes} : List<&2, Vote>}
      CastAccepted{state, Ballots{proposal, next, False{}}, yes_count(next), total_count(next)}

# actor is supplied by the authenticated invocation, never a request-selected voter.
# round is the caller's exact intended round; wrong-round replay leaves state unchanged.
def cast(+state: Ballots, +actor: List<&2, Nat>, round: List<&2, Nat>, yes: Bool) -> CastResult:
  match state:
    case Ballots{proposal, +votes, closed}:
      match proposal:
        case Proposal{storedRound, base, candidate, basePrototype, candidatePrototype,
            baseKindRoot, instanceRoot, migration, policy, electorate, quorum}:
          cast_choice(state, actor, yes,
            Bool.and(valid(state), Bool.and(Bytes.eq(round, storedRound),
              Bool.and(Math.not(closed), Bool.and(member(actor, electorate), Math.not(used(actor, votes)))))))

def resolve_choice(state: Ballots, next: Ballots, decision: Review.Decision,
    allowed: Bool) -> Resolution:
  match allowed:
    case False{}:
      Unresolved{state}
    case True{}:
      Resolved{state, next, decision}

# Absolute YES quorum, not plurality; count of genuine unique ballots is separately visible.
# A zero quorum never resolves. Resolution closes the same admitted ballot image.
def resolve(+state: Ballots) -> Resolution:
  match state:
    case Ballots{+proposal, +votes, closed}:
      match proposal:
        case Proposal{round, base, +candidate, basePrototype, candidatePrototype,
            baseKindRoot, instanceRoot, migration, +policy, electorate, quorum}:
          resolve_choice(state, Ballots{proposal, votes, True{}},
            Review.Decision{candidate, policy, True{}},
            Bool.and(valid(state), Bool.and(Math.not(closed),
              Bool.and(Math.lt(0n, quorum), Math.le(quorum, yes_count(votes))))))

def install_choice(current: Review.Candidate, candidate: Review.Candidate,
    policy: List<&2, Nat>, proposal: Proposal, allowed: Bool) -> Installation:
  match allowed:
    case False{}:
      InstallRefused{}
    case True{}:
      InstallProposal{Review.Propose{current, candidate, policy}, proposal}

# Current root/prototype/instance/migration are authenticated by the same receiving sample.
# A ballot result cannot grant authority to install, and cannot change what it endorsed.
def prepare_install(+state: Ballots, +current: Review.Candidate,
    currentPrototype: List<&2, Nat>, currentKindRoot: List<&2, Nat>,
    currentInstanceRoot: List<&2, Nat>, migration: List<&2, Nat>,
    review: Review.Recommendation) -> Installation:
  match state:
    case Ballots{+proposal, votes, closed}:
      match proposal:
        case Proposal{round, +base, +candidate, basePrototype, candidatePrototype,
            baseKindRoot, instanceRoot, expectedMigration, +policy, electorate, quorum}:
          +decision = {Review.Decision{candidate, policy,
            Bool.and(valid(state), Bool.and(closed, Bool.and(Math.lt(0n, quorum), Math.le(quorum, yes_count(votes)))))} : Review.Decision}
          install_choice(current, candidate, policy, proposal,
            Bool.and(Review.candidate_eq(base, current),
              Bool.and(Bytes.eq(basePrototype, currentPrototype),
                Bool.and(Bytes.eq(baseKindRoot, currentKindRoot),
                  Bool.and(Bytes.eq(instanceRoot, currentInstanceRoot),
                    Bool.and(Bytes.eq(expectedMigration, migration),
                      Review.eligible(candidate, policy, review, decision)))))))

law refused_cast_unchanged:
  for +state: Ballots
  for actor: List<&2, Nat>
  for yes: Bool
  {cast_choice(state, actor, yes, False{}) == CastRefused{state} : CastResult}

def refused_cast_unchanged(state, actor, yes):
  match state:
    case Ballots{proposal, votes, closed}:
      {==}

# Every successful cast returns exactly one new ballot and derived counts.
# expected is the full predecessor consumed atomically by native admission.
def ExactCast(before: Ballots, -actor: List<&2, Nat>, -yes: Bool,
    result: CastResult) -> Type:
  match before result:
    case Ballots{proposal, votes, closed} CastRefused{unchanged}:
      {unchanged == Ballots{proposal, votes, closed} : Ballots}
    case Ballots{proposal, votes, closed} CastAccepted{expected, successor, yesCount, totalCount}:
      Pair({expected == Ballots{proposal, votes, closed} : Ballots},
        Pair({successor == Ballots{proposal, Con{Vote{actor, yes}, votes}, False{}} : Ballots},
          Pair({yesCount == yes_count(Con{Vote{actor, yes}, votes}) : Nat},
            {totalCount == Succ{total_count(votes)} : Nat})))

law cast_choice_exact:
  for +state: Ballots
  for +actor: List<&2, Nat>
  for +yes: Bool
  for allowed: Bool
  ExactCast(state, actor, yes, cast_choice(state, actor, yes, allowed))

def cast_choice_exact(state, actor, yes, allowed):
  match state allowed:
    case Ballots{proposal, votes, closed} False{}:
      {==}
    case Ballots{proposal, votes, closed} True{}:
      ({==}, ({==}, ({==}, {==})))

law cast_exact:
  for +state: Ballots
  for +actor: List<&2, Nat>
  for round: List<&2, Nat>
  for +yes: Bool
  ExactCast(state, actor, yes, cast(state, actor, round, yes))

def cast_exact(state, actor, round, yes):
  match state:
    case Ballots{proposal, +votes, closed}:
      match proposal:
        case Proposal{storedRound, base, candidate, basePrototype, candidatePrototype,
            baseKindRoot, instanceRoot, migration, policy, electorate, quorum}:
          cast_choice_exact(state, actor, yes,
            Bool.and(valid(state), Bool.and(Bytes.eq(round, storedRound),
              Bool.and(Math.not(closed), Bool.and(member(actor, electorate), Math.not(used(actor, votes)))))))

def ExactInstallation(-current: Review.Candidate, -candidate: Review.Candidate,
    -policy: List<&2, Nat>, -proposal: Proposal, result: Installation) -> Type:
  match result:
    case InstallRefused{}:
      Unit
    case InstallProposal{adoption, binding}:
      Pair({adoption == Review.Propose{current, candidate, policy} : Review.Adoption},
        {binding == proposal : Proposal})

law installation_exact:
  for +current: Review.Candidate
  for +candidate: Review.Candidate
  for +policy: List<&2, Nat>
  for +proposal: Proposal
  for allowed: Bool
  ExactInstallation(current, candidate, policy, proposal,
    install_choice(current, candidate, policy, proposal, allowed))

def installation_exact(current, candidate, policy, proposal, allowed):
  match allowed:
    case False{}:
      Unit{}
    case True{}:
      ({==}, {==})
