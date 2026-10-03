# Protocol-strength exports: the result carries a checked source-contract term.
# These are affine Type values, not persistent Data or reusable closures.
# Native evidence erasure/encoding must be explicitly refined by the backend.
import Base
import ./CatalogReview.bend as Review
import ./ReusableWorkshop.bend as Workshop

def SameSource(-candidate: Review.Candidate, -policy: List<&2, Nat>,
    result: Review.Recommendation) -> Type:
  match result:
    case Review.Recommendation{selected, selectedpolicy, ready}:
      Pair({selected == candidate : Review.Candidate},
        {selectedpolicy == policy : List<&2, Nat>})

type CheckedRecommendation<-candidate: Review.Candidate, -policy: List<&2, Nat>> is Type:
  CheckedRecommendation{result: Review.Recommendation, contract: SameSource(candidate, policy, result)}

def review_exact(+candidate: Review.Candidate, +policy: List<&2, Nat>, +found: Workshop.Lookup) ->
    SameSource(candidate, policy, Workshop.review.fin(candidate, policy, found)):
  match found:
    case Workshop.Missing{}:
      ({==}, {==})
    case Workshop.Found{catalogued, label}:
      ({==}, {==})

def contracted_review(final_catalog: @+key: Review.Candidate -> Workshop.Lookup,
    +candidate: Review.Candidate, +policy: List<&2, Nat>) -> CheckedRecommendation<candidate, policy>:
  +found = final_catalog(candidate)
  CheckedRecommendation{Workshop.review.fin(candidate, policy, found), review_exact(candidate, policy, found)}

type CheckedAudit<-prior: Review.Recommendation, -audited: Bool> is Type:
  CheckedAudit{result: Review.Recommendation,
    contract: {result == Workshop.strengthen(prior, audited) : Review.Recommendation}}

# Any implementation of this exact dependent interface must establish the same
# strengthened verdict, including prior denial; matching a plain return type
# alone would not impose this obligation on an override.
def contracted_audit(+prior: Review.Recommendation, +audited: Bool) -> CheckedAudit<prior, audited>:
  CheckedAudit{Workshop.strengthen(prior, audited), {==}}
