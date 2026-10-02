# Law component source/codec integration sketch

2026-10-02, Codex. Companion to `Theory/LawComposition.lean` on the independent
`codex/law-composition` snapshot. Scoped shared-seat Lean checks pass the pure module, CanonicalPolicyAdmission,
PolicyRecordCodec v5, PolicyHistoryResolution, ResolvedLawCompilation, and
PolicyComponentResolution. No full consumer closure rebuild or native journey has
run; active receivers have not been switched to this schema.
Root decisions and full product contract are in claudesplosion's
`planning/law-composition-2026-10-02.md`.

## Small receiving interface

Keep `PolicyRecord`'s policy ID, revision, domain, semantics, and previous address.
Retain the predicate field for source constructors and append localSelector/parents;
`PolicyRecord.localComponent` reconstructs the shared component. The logical body is:

- `local : LawComposition.Component`
- `descendants : Option LawComposition.Component`

Both use the same typed component: explicit operation/physical-kind selector,
ordinary `Pred`, and `List PolicyRef`. References choose a facet and either the
snapshot's head or an exact revision/source digest. No function payloads.

The old local law becomes `Component {selector := {}, predicate := old.predicate,
parents := []}`; the export is `none`. Prove neutral-guard evaluation equals the
old predicate. Preserve old bytes/codec/profile interpretation through checked
carry; a newly encoded record has a new source identity. No claim that raw old
addresses or replay formats are valid in the new domain follows from this map.

`Theory/LawComposition` imports only Pred and typed authorization. Do not import
CanonicalPolicyAdmission into it: CanonicalPolicyAdmission is a consumer, and
that would create a dependency cycle. The pure graph checks are deliberately
separate from receiver source-authentication evidence.

## Canonical bytes

Use the existing shared stream codecs, not a new serialization framework:

1. Facet tags local=0, descendants=1; unknown tags refuse.
2. Selection tags head=0; pinned=1 followed by revision and digest.
3. PolicyRef: policy ID, facet, selection.
4. Selector: three optional lists (physical kind, request kind, verb). `none`
   selects everything; `some []` selects nothing. Preserve authored list spelling in source bytes; only the resolved graph is deduplicated and canonically ordered.
   Do not interpret an absent slot as another kind.
5. Component: selector, existing canonical Pred token stream, explicit references.
   Parent order confers no method precedence. Canonicalize exact duplicate refs
   and ordering for authoring, or retain spelling but canonicalize the derived
   graph; choose ONE canonical wire contract and prove encode/decode agreement.
6. Record: existing metadata and local component, optional descendant component.

The v5 codec preserves authored reference spelling; reordering source creates a
distinct source address, while the resolved effective conjunction is canonical. A head
and a pin remain different references even if they happen to resolve to the same
record at one snapshot. Deduplication by resolved key belongs to resolution.

Bump the record frame and semantics/profile identity; reject the previous frame
on the new decoder. Keep the prior decoder as a lineage input, not a fallback
that silently supplies new policy semantics. Generalize the source body's
round-trip proof and `PolicyRecord.source`; metadata successor checks still apply.

## Authenticating resolved nodes

Current concrete `CredentialAuthorityPolicyRegistry.loadPolicy` requires the
current revision, and `CredentialAuthorityDomain.retirePolicy` frees the old
policy-address entry. Head loading stays anchored there. A historical loader
starts from that authenticated current source and follows checked `previous`
records, verifying digest, identity, revision succession and profile/domain at
every step until the requested revision/digest. It is not a host-supplied
`revision -> bytes` table. The immutable source cells must remain available.

A lineage-aware carry must define how old profile/domain source records are
interpreted and authenticated. Do not simply relax same-profile checks globally.
The carry lane owns that bridge and retry/nullifier continuity.

Receiving source resolves every declared reference and implicit edge. Its
proof-relevant graph input must prove:

- each component is the exact selected facet of authenticated source bytes;
- each explicit parent reference produced its exact snapshot-resolved edge;
- no declared edge was omitted or invented;
- the target's synthetic root includes its current local component and mandatory
  room export chain; a library local component does not import its object's
  ambient room administration;
- exports include their defined containing-room export chain;
- all heads, parentage and physical source reads share one receiving snapshot.

`GraphInput` in the draft is pure data, not this authenticity witness. The current
`resolve` checks unique source keys, reachability through present dependencies,
cycles, and a directly checked decreasing rank over postorder. It does not yet
prove traversal completeness or connect these checks to canonical source bytes.
Those proof/receiver obligations must be completed before the result can authorize
anything.

The effective conjunction is an ordinary Pred and reuses PredCompile's support,
range, cast-injectivity and lower_sound/lower_complete machinery. Never replace
the predicate in a CommittedPolicy while retaining the old source digest.
The root source's membership address and the resolved effective manifest identity
are separate commitments; a checked adapter joins both to admission.

## First integration consumers

Extend observation/write preparation, policy install, and room placement through
one resolver. Preserve source-derived target pre/post projections, including the
reserved physical-kind selector slot. Old-law authorization precedes candidate
post-graph validation. Check each changed component/root's reachable candidate
closure, including joint batch changes; no global downstream satisfiability veto.
Add all selected-source/head/parentage dependencies to receiver read guards.

Diagnostics keep origin key and dependency path with existing LawLeaf data. A
shortest canonical path and root-first presentation remain work in the draft;
its canonicalOrder currently only sorts node identity. Do not mistake that
presentation TODO for missing mandatory conjunction terms.

## Proof/build work remaining

Scoped modules compile. Full dependency rebuilding and native consumer journeys
remain required, together with:

- establish resolve success completeness and absence of closureInvariant for
  authenticated finite input with an acyclic reachable graph;
- prove bounded DFS cannot exhaust its node-count depth on an acyclic input;
- prove output source/root/dependency coverage and acyclicity from checkClosure;
- prove canonical ordering preserves membership and has no duplicate keys;
- neutral selector carry equivalence is already proved and compiled;
- compile and verify the written pure fixtures: opposite parent orders with useful intersection,
  diamond deduplication, P@2 inheriting pinned P@1, self/head and long cycles,
  and a pinned/current intersection that deliberately denies every request.

PolicyComponentResolution now loads components and dependencies from actual
LoadedPolicy snapshots, source histories and authority parentage. It returns an
authenticated LoadedGraph with exact dependency-loading equations plus checked DAG
coverage. It does not yet install a portal or durable physical read guards.
The temporary legacy gate refuses non-neutral target metadata, but is not a
complete ambient restriction gate; do not enable non-neutral installs until the
receiving paths use composed admission.
