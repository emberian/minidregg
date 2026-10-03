# Candidate review is an endorsement about exact source, never proof of truth.
# Inputs come from the authenticated source/policy/request views. The module
# only proposes adoption; the current native source/root/law receiver decides it.
import Base

type Candidate is Data:
  Candidate{source: List<&2, Nat>, program: List<&2, Nat>, revision: Nat}

type Recommendation is Data:
  Recommendation{candidate: Candidate, policy: List<&2, Nat>, ready: Bool}

type Decision is Data:
  Decision{candidate: Candidate, policy: List<&2, Nat>, endorsed: Bool}

type Adoption is Data:
  Hold{}
  Propose{expected: Candidate, selected: Candidate, policy: List<&2, Nat>}

def candidate_eq(a: Candidate, b: Candidate) -> Bool:
  match a b:
    case Candidate{asource, aprogram, arevision} Candidate{bsource, bprogram, brevision}:
      Bool.and(Bytes.eq(asource, bsource),
        Bool.and(Bytes.eq(aprogram, bprogram), Nat.eq(arevision, brevision)))

def candidate_eq_sound(+a: Candidate, +b: Candidate, +e: Truth(candidate_eq(a, b))) ->
    {a == b : Candidate}:
  match a b:
    case Candidate{+asource, +aprogram, +arevision} Candidate{+bsource, +bprogram, +brevision}:
      +more = Bool.and_right(Bytes.eq(asource, bsource),
        Bool.and(Bytes.eq(aprogram, bprogram), Nat.eq(arevision, brevision)), e)
      %Bytes.eq_sound(asource, bsource, Bool.and_left(Bytes.eq(asource, bsource),
        Bool.and(Bytes.eq(aprogram, bprogram), Nat.eq(arevision, brevision)), e)) :
        {Candidate{asource, aprogram, arevision} == Candidate{_, bprogram, brevision} : Candidate}
      %Bytes.eq_sound(aprogram, bprogram,
        Bool.and_left(Bytes.eq(aprogram, bprogram), Nat.eq(arevision, brevision), more)) :
        {Candidate{asource, aprogram, arevision} == Candidate{asource, _, brevision} : Candidate}
      %Nat.eq_sound(arevision, brevision,
        Bool.and_right(Bytes.eq(aprogram, bprogram), Nat.eq(arevision, brevision), more)) :
        {Candidate{asource, aprogram, arevision} == Candidate{asource, aprogram, _} : Candidate}
      {==}

# Every field in the review and decision is bound; source-name equality alone
# cannot turn a review of revision A into authority to install revision B.
def eligible(+candidate: Candidate, +policy: List<&2, Nat>,
    review: Recommendation, decision: Decision) -> Bool:
  match review decision:
    case Recommendation{reviewed, reviewpolicy, ready} Decision{chosen, choicepolicy, endorsed}:
      Bool.and(ready, Bool.and(endorsed,
        Bool.and(candidate_eq(candidate, reviewed),
          Bool.and(candidate_eq(candidate, chosen),
            Bool.and(Bytes.eq(policy, reviewpolicy), Bytes.eq(policy, choicepolicy))))))

def PolicyBinding(-candidate: Candidate, -policy: List<&2, Nat>,
    review: Recommendation, decision: Decision) -> Type:
  match review decision:
    case Recommendation{reviewed, reviewpolicy, ready} Decision{chosen, choicepolicy, endorsed}:
      Pair({candidate == reviewed : Candidate},
        Pair({candidate == chosen : Candidate},
          Pair({policy == reviewpolicy : List<&2, Nat>}, {policy == choicepolicy : List<&2, Nat>})))

# The equality checker is proved sound above, so eligibility entails exact
# agreement on complete source/program/revision and both policy references.
law eligibility_binding:
  for +candidate: Candidate
  for +policy: List<&2, Nat>
  for +review: Recommendation
  for +decision: Decision
  for +e: Truth(eligible(candidate, policy, review, decision))
  PolicyBinding(candidate, policy, review, decision)

def eligibility_binding(candidate, policy, review, decision, e):
  match review decision:
    case Recommendation{+reviewed, +reviewpolicy, +ready} Decision{+chosen, +choicepolicy, +endorsed}:
      +pr = Bytes.eq(policy, reviewpolicy)
      +pc = Bytes.eq(policy, choicepolicy)
      +cr = candidate_eq(candidate, reviewed)
      +cc = candidate_eq(candidate, chosen)
      +t1 = Bool.and_right(ready, Bool.and(endorsed,
        Bool.and(cr, Bool.and(cc, Bool.and(pr, pc)))), e)
      +t2 = Bool.and_right(endorsed, Bool.and(cr, Bool.and(cc, Bool.and(pr, pc))), t1)
      +t3 = Bool.and_right(cr, Bool.and(cc, Bool.and(pr, pc)), t2)
      +t4 = Bool.and_right(cc, Bool.and(pr, pc), t3)
      (candidate_eq_sound(candidate, reviewed, Bool.and_left(cr, Bool.and(cc, Bool.and(pr, pc)), t2)),
        (candidate_eq_sound(candidate, chosen, Bool.and_left(cc, Bool.and(pr, pc), t3)),
          (Bytes.eq_sound(policy, reviewpolicy, Bool.and_left(pr, pc, t4)),
            Bytes.eq_sound(policy, choicepolicy, Bool.and_right(pr, pc, t4)))))

def choose(expected: Candidate, candidate: Candidate, policy: List<&2, Nat>, allowed: Bool) -> Adoption:
  match allowed:
    case False{}:
      Hold{}
    case True{}:
      Propose{expected, candidate, policy}

def prepare(expected: Candidate, +candidate: Candidate, +policy: List<&2, Nat>,
    review: Recommendation, decision: Decision) -> Adoption:
  choose(expected, candidate, policy, eligible(candidate, policy, review, decision))

# An exact indexed postcondition on every successful proposal. It retains the
# predecessor and chosen source/policy, even when eligibility is overridden.
# Native admission must check expected against the actual current source root.
def ExactProposal(-expected: Candidate, -candidate: Candidate, -policy: List<&2, Nat>,
    result: Adoption) -> Type:
  match result:
    case Hold{}:
      Unit
    case Propose{before, selected, selectedpolicy}:
      Pair({before == expected : Candidate},
        Pair({selected == candidate : Candidate}, {selectedpolicy == policy : List<&2, Nat>}))

law proposal_exact:
  for +expected: Candidate
  for +candidate: Candidate
  for +policy: List<&2, Nat>
  for allowed: Bool
  ExactProposal(expected, candidate, policy, choose(expected, candidate, policy, allowed))

def proposal_exact(expected, candidate, policy, allowed):
  match allowed:
    case False{}:
      Unit{}
    case True{}:
      ({==}, ({==}, {==}))

law prepared_exact:
  for +expected: Candidate
  for +candidate: Candidate
  for +policy: List<&2, Nat>
  for review: Recommendation
  for decision: Decision
  ExactProposal(expected, candidate, policy, prepare(expected, candidate, policy, review, decision))

def prepared_exact(expected, candidate, policy, review, decision):
  proposal_exact(expected, candidate, policy, eligible(candidate, policy, review, decision))

law unready_never_proposes:
  for expected: Candidate
  for candidate: Candidate
  for policy: List<&2, Nat>
  for reviewed: Candidate
  for reviewpolicy: List<&2, Nat>
  for chosen: Candidate
  for choicepolicy: List<&2, Nat>
  for endorsed: Bool
  {prepare(expected, candidate, policy,
    Recommendation{reviewed, reviewpolicy, False{}},
    Decision{chosen, choicepolicy, endorsed}) == Hold{} : Adoption}

def unready_never_proposes(expected, candidate, policy, reviewed, reviewpolicy,
    chosen, choicepolicy, endorsed):
  {==}
