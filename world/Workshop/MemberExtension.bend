# A separately authored member extension. Original workshop sources are intact.
# This supplies the audit demand, delegates to inherited review, and supplies
# an alternative presentation using the composed final review implementation.
import Base
import ./CatalogReview.bend as Review
import ./ReusableWorkshop.bend as Workshop

def audit(+candidate: Review.Candidate) -> Bool:
  match candidate:
    case Review.Candidate{source, program, revision}:
      match revision:
        case 0n:
          False{}
        case 1n+prior:
          True{}

def focused_review(inherited_review: @+key: Review.Candidate -> Review.Recommendation,
    member_audit: @+key: Review.Candidate -> Bool, +candidate: Review.Candidate) -> Review.Recommendation:
  Workshop.audited_review(inherited_review, member_audit, candidate)

# The new label is authored text "Reviewed" encoded as bytes. It is unrelated
# to approval/authority. The verdict is returned by finalSelf.review.
def alternate_presentation(final_review: @+key: Review.Candidate -> Review.Recommendation,
    +candidate: Review.Candidate) -> Workshop.Card:
  Workshop.presentation(final_review, candidate, [82n, 101n, 118n, 105n, 101n, 119n, 101n, 100n])

law zero_revision_denied:
  for source: List<&2, Nat>
  for program: List<&2, Nat>
  {audit(Review.Candidate{source, program, 0n}) == False{} : Bool}

def zero_revision_denied(source, program):
  {==}

law positive_revision_allowed:
  for source: List<&2, Nat>
  for program: List<&2, Nat>
  for prior: Nat
  {audit(Review.Candidate{source, program, 1n+prior}) == True{} : Bool}

def positive_revision_allowed(source, program, prior):
  {==}
