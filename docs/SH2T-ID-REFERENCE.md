# Recipient verified degree-2f sharing

`sh2t_id.rs` implements the Sh2t-Id protocol from section 6.1, printed pages
16–18, of ePrint 2024/1666. It uses the backend's actual recipient PrivateSend,
Bracha reliable broadcasts/reliable agreement and deterministic transition WAL.
There is no ideal degree-2f sharing or external validity callback.

The public profile is n=3f+1, 4<=n<=16, with n*n groups and a fixed `per_group`
number of polynomials. Native holder i evaluates at GF128(i+1); alpha0 is zero.
The original Generation is retained exactly. Private child invocations derive
from its bound protocol context and never replace a native custody descriptor.
Public parameters must fit the actual 65536-byte PrivateSend payload and the
16 MiB aggregate recursive WAL record. Larger pools require explicit batching.

The dealer supplies exactly 2f+1 coefficients per input polynomial. Independent
random degree-2f mask polynomials come from a retained OS-random seed through
separate domains. For each group/holder, SHA256 commits the value/mask vectors,
context, group and holder. A public n-by-n matrix commits each receiver's n
ordered group hashes at each holder. Holder i privately receives all its
value/mask evaluations and every holder's hashes for i's assigned n groups.

Each holder checks both its own matrix row and its assigned matrix column.
`AcceptedSharing` is created only after these checks and retained immutably before
RA Echo. Acceptance establishes consistent committed points; it does not establish
a degree relation or a zero constant term. Invalid private payloads produce typed
`RejectedSharing` and an authenticated holder complaint.

`request_private_reconstruction(group,receiver)` requires group/n==receiver
(zero-based indices). More than f completed requester broadcasts precede honest
private point transfers. The receiver checks each authenticated holder's point and
mask against the committed group hash and matrix block, retains the first valid
point for that holder, and interpolates after 2f+1 distinct valid supports. It
checks the resulting value AND mask polynomials at EVERY committed position.
The immutable result is one of:

- `Reconstruction::Verified`: full degree-2f polynomial coefficients, exact
  context/group/receiver, accepted holders, masks and public matrix evidence.
- `Reconstruction::Invalid`: retained candidate coefficients, masks, committed
  group hashes, accepted holders and exact evidence hash. This is the real
  committed nonpolynomial rejection path, not a shortage of points.
- `Reconstruction::AgreedAccusation`: actual RA-completed dealer/holder pair when
  an authenticated complaint and source dispute requests replace missing support.

The recipient's assigned group restriction is enforced at request AND received
point boundaries. Other parties never receive a reconstruction result through
this API. Early points have bounded authenticated-holder buffers and are checked
only against the recipient's completed delivery and request authorization.

A source opening request requires an authenticated holder complaint. More than f
request broadcasts deliver that holder's actual immutable PrivSend payload to all
parties. Each party rechecks the same matrix relation and obtains a typed Dealer
or Accuser result. Agreement accusations separately require source dispute input
and the authenticated complaint before honest RA Echo. These protocol events do
not manufacture native funded request, enrolled credential or declassification
authority. `private_view` and rejected evidence getters are private read access,
not permission to publish the retained values.

`sh2t_id_store::Store` journals full dealer polynomials and random seed, received
canonical wire messages, opening/reconstruction/dispute source events and entire
recursive outboxes. Transactional clone plus fsync precedes publication. Reopen
recomputes exact child contexts and compares every recorded outbox. Identical
dealer retries replay retained packets; changed inputs refuse. Identity binds the
original Generation, party and profile. The owner-private WAL assumes honest
crash storage; its checksum is not malicious rollback protection or a correlation
anchor.

This uses the existing reference GF(2^128), whose arithmetic is not a constant-time
online secret processor. The assumptions are static cumulative f corruption,
authenticated confidential reliable channels, classical SHA256 commitment/PRG
assumptions and the explicit PrivSend replacement's remaining simulation boundary.
No QROM/PQ qualification or full protocol simulator follows from hash usage.

The narrow receiving command is:

    cargo nextest run --release --locked --lib -E 'test(/sh2t/)'

The initial eight tests passed in a bounded Persvati release seat. The current
revision additionally exercises n=7,f=2 with two withheld parties and degree-four
reconstruction, plus retained invalid-evidence and original-Generation getters;
its separate receiving result belongs to the exact source receipt.

The checked-triples consumer must verify every returned polynomial has constant
coefficient zero and bind the exact public padded seed/group mapping. The sharing
module does not infer zero from a dealer's claim. TripleKingDN, distributed triple
checking, dispute localization and evaluator installation are separate consumers.
