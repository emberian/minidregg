# Reusable source bodies for Objective Bend partial specs.
# Callable demands below are affine invocation closures. Persistent specs keep
# their immutable source references as Data; they must not copy these closures.
# The Objective Bend linker supplies finalSelf.catalog/review and strict-prefix
# super.review. Calling these functions does not itself confer world authority.
import Base
import ./CatalogReview.bend as Review

type Catalog is Data:
  EmptyCatalog{}
  CatalogRow{candidate: Review.Candidate, label: List<&2, Nat>, rest: Catalog}

type Lookup is Data:
  Missing{}
  Found{candidate: Review.Candidate, label: List<&2, Nat>}

def catalog_lookup.fin(candidate: Review.Candidate,
    label: List<&2, Nat>, otherwise: Lookup, same: Bool) -> Lookup:
  match same:
    case False{}:
      otherwise
    case True{}:
      Found{candidate, label}

def catalog_lookup(+selected: Review.Candidate, catalog: Catalog) -> Lookup:
  match catalog:
    case EmptyCatalog{}:
      Missing{}
    case CatalogRow{+candidate, label, rest}:
      catalog_lookup.fin(candidate, label, catalog_lookup(selected, rest),
        Review.candidate_eq(selected, candidate))

# Environment first: the partial-spec linker binds immutable admitted Data,
# then exposes the remaining exact Candidate -> Lookup method interface.
def catalog(catalog_data: Catalog, +candidate: Review.Candidate) -> Lookup:
  catalog_lookup(candidate, catalog_data)

# Review partial spec requires catalog. A third-party composed catalog override
# is observed because this callable is finalSelf, not this module's helper.
def review.fin(+candidate: Review.Candidate, policy: List<&2, Nat>, found: Lookup) -> Review.Recommendation:
  match found:
    case Missing{}:
      Review.Recommendation{candidate, policy, False{}}
    case Found{catalogued, label}:
      Review.Recommendation{candidate, policy, Review.candidate_eq(candidate, catalogued)}

def review(final_catalog: @+key: Review.Candidate -> Lookup, +candidate: Review.Candidate,
    policy: List<&2, Nat>) -> Review.Recommendation:
  review.fin(candidate, policy, final_catalog(candidate))

def review_with_policy(policy: List<&2, Nat>,
    final_catalog: @+key: Review.Candidate -> Lookup, +candidate: Review.Candidate) -> Review.Recommendation:
  review(final_catalog, candidate, policy)

# Audit extension requires an audit method supplied by the composing member.
# The callable inherited_review is super.review, resolved before this override.
# It delegates once, strengthens the verdict, and preserves exact source/policy.
def strengthen(prior: Review.Recommendation, audited: Bool) -> Review.Recommendation:
  match prior:
    case Review.Recommendation{candidate, policy, ready}:
      Review.Recommendation{candidate, policy, Bool.and(ready, audited)}

def audited_review(inherited_review: @+key: Review.Candidate -> Review.Recommendation,
    audit: @+key: Review.Candidate -> Bool, +candidate: Review.Candidate) -> Review.Recommendation:
  strengthen(inherited_review(candidate), audit(candidate))

type Card is Data:
  Card{candidate: Review.Candidate, label: List<&2, Nat>, review: Review.Recommendation}

# Presentation partial spec requires review; its callback is finalSelf.review.
# It receives only authorized label/reference data, never resident journals.
# Domain and source/history faces may wrap this same returned card differently.
def presentation(final_review: @+key: Review.Candidate -> Review.Recommendation,
    +candidate: Review.Candidate, label: List<&2, Nat>) -> Card:
  Card{candidate, label, final_review(candidate)}

def presentation_with_label(label: List<&2, Nat>,
    final_review: @+key: Review.Candidate -> Review.Recommendation,
    +candidate: Review.Candidate) -> Card:
  presentation(final_review, candidate, label)

law audit_source_exact:
  for +candidate: Review.Candidate
  for +policy: List<&2, Nat>
  for +ready: Bool
  for +audited: Bool
  {strengthen(Review.Recommendation{candidate, policy, ready}, audited) ==
    Review.Recommendation{candidate, policy, Bool.and(ready, audited)} : Review.Recommendation}

def audit_source_exact(candidate, policy, ready, audited):
  {==}

law denied_review_stays_denied:
  for +candidate: Review.Candidate
  for +policy: List<&2, Nat>
  for audited: Bool
  {strengthen(Review.Recommendation{candidate, policy, False{}}, audited) ==
    Review.Recommendation{candidate, policy, False{}} : Review.Recommendation}

def denied_review_stays_denied(candidate, policy, audited):
  {==}

law failed_audit_denies:
  for +candidate: Review.Candidate
  for +policy: List<&2, Nat>
  for +ready: Bool
  {strengthen(Review.Recommendation{candidate, policy, ready}, False{}) ==
    Review.Recommendation{candidate, policy, False{}} : Review.Recommendation}

def failed_audit_denies(candidate, policy, ready):
  match ready:
    case False{}:
      {==}
    case True{}:
      {==}
