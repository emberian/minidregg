# Proposed Mini release decision for public-history fn sharing

This is a design proposal, not an approved Ember policy, implemented Mini
authorization, or native assurance already delivered. It addresses agent
control of a *public-history* origin Store using the current full-prefix R
article. The disclosure facts and private-history limitation are recorded in
[FN-PUBLICATION-DISCLOSURE.md](FN-PUBLICATION-DISCLOSURE.md). No current
`mini_publish`, `grain-origin-prepare`, A outbox, or fn POST result establishes
the release decision described here.

## Existing boundary and reusable machinery

[`Kernel/FnEvidence.lean`](../Kernel/FnEvidence.lean) exports the exact original
signed call, receipt, genesis, and **every accepted origin record through that
receipt**. Its verifier independently replays that prefix. The current R
renderer in [`Host/GrainOriginSource.lean`](../Host/GrainOriginSource.lean)
classifies the named grain settlement, unchanged reserved parent witness, and
nonempty named publication; it does not select or redact historical records.
[`Host/GrainOriginPreparation.lean`](../Host/GrainOriginPreparation.lean) and
[`Host/GrainOriginCommand.lean`](../Host/GrainOriginCommand.lean) prepare a
private strict source and report the exact package, prefix, and source digests,
receipt, signed target list, and Newsgroups context. Their Boolean disclosure
intent and audience acknowledgement record an operator request, not consent
or a Mini grant. The [Host command](../Host/Main.lean) writes that source into
a private, new output directory; it does not sign or post it.

The hosted [`mini_publish` tool](../native/grain-runtime/src/main.rs) submits
one signed tool-grain settlement with allowed publication targets and a
current, unchanged parent witness. Its target allowlist and publication
receipt authorize those edits, not release of the earlier origin Store.
[`Kernel/AgentGrain.lean`](../Kernel/AgentGrain.lean) supplies the reserved
parent witness and generation-pinned worker caveat. The A-side
[`Kernel/FnOriginOutbox.lean`](../Kernel/FnOriginOutbox.lean) and Host op16
re-verify an already signed carrier and its Mini origin, then retain its exact
bytes in a tag-10 prepared atom. The
[`origin-publish` client](../native/resource-client/src/publisher.rs) pins that
carrier, submits the outbox with exact-call retry, exports it for exact-byte
comparison, and records an fn POST attempt before sending. None checks a
Store-wide release authorization today. The actual publisher path has been
exercised for one workroom content edit in
[the workroom evidence](evidence/2026-09-26-workroom-content-publisher/README.md);
that demonstrates transport and custody, not agent consent to disclose its
whole origin prefix.

## Proposed scope and two-stage decision

Start with a separately constituted **public-history origin Store**: its
genesis and every admitted record that a release may cover must be intended
for a public, peerable fn audience. A new Mini release authority should be
established as part of that Store's public-history charter before the history
it governs, with explicit delegations and an allowance for the hosted agent.
The charter and its admission policy must make the permitted Store and
release scope checkable. Declaring an existing mixed or private Store public
after contributors have written to it would not establish their consent.
Even a valid charter is an operational authority rule, not a theorem that
every participant understood or consented to all later peering.

The original grain publication is accepted at receipt **N**. A private
preparation then exports and verifies package **P(N)**, renders strict R,
and obtains the exact hybrid-signed carrier. Only after these bytes exist can
the agent decide whether to release them. A read-only `mini_share_preview`
should give the agent the original origin domain, semantics, genesis pin,
receipt and signed call identity; every signed target; package and prefix
lengths and domain-separated digests; source and **signed carrier** digests;
Message-ID; destination Newsgroups; and the explicit fact that the audience
is public and may expand through fn peering. The group is an authored routing
header, **not** access control over recipients. The preview must not itself
post or mutate either Store.

A separate `mini_share_confirm` should take the exact preview identity and
submit one ordinary signed Mini release transaction. Its source-authored
release payload should commit to all those byte identities, the named
publication target, the public-history charter and release-policy version,
the group and public/peerable audience statement, and an explicit
whole-prefix-release decision. This transaction should join a dedicated
release resource/allowance transition with a no-op current parent-grain
witness. The native receiver must check the agent's current signature,
capability, installed release policy, exact roots, and the parent witness in
one admission. The witness binds the current parent generation, reserved
status, remaining and reserved budget coordinates. A bounded release
allowance is consumed through the release resource or a delegated child tool
task. The worker witness cannot debit the parent's allowance; if release
must incur a parent charge, its controller must reserve and settle that
charge through the existing governed path. A stale generation, cancelled or
unreserved parent, revoked grant, insufficient release allowance, or
conflicting exact roots must refuse confirmation.

The release event is necessarily later than N: its payload cannot name the
exact signed carrier before carrier construction, and the carrier's P(N)
cannot contain a later event without changing its own bytes. Putting a
purported release in the same R prefix would introduce this circularity.
Under the present R profile the release record therefore authorizes local
posting but is **not independently visible to a recipient who has only R**.
A recipient-verifiable release certificate needs a new article/evidence
profile or another independently verifiable delivery of the later accepted
record. This proposal does not claim that property.

## Proposed publication gate and integration sites

Extend the source-owned outbox report and a new version of its retained
`Prepared` atom so Host op16 checks the accepted release call and receipt
against the independently pinned origin Store, matches the exact original
P(N), rendered source, signed carrier, group, Message-ID, and policy scope,
then records the release identity alongside the carrier. Historical tag-10
v1 atoms must keep their current decode/meaning and must not acquire a
retroactive release claim. The Host needs an exact, bounded verifier for the
new release command and current charter/grant; JSON supplied by Rust is not
an authority assertion. The existing `FnOriginOutbox` exact Message-ID
conflict/idempotence checks and the publisher's immutable carrier and POST
attempt journal can then be reused. The client should require the accepted
new outbox form before first POST, retain the exact release call/receipt with
the attempt, and never substitute a fresh carrier on retry.

This treats an accepted release as a one-shot authorization fixed at its
admission time. A later hard disconnect does not silently rewrite that
historical decision. If the product instead requires revocation until the
physical POST instant, it needs an additional fresh policy check and an
explicit policy for the check-to-network-send gap; Mini admission and an fn
HTTP POST are not one atomic transaction. The existing outbox and publisher
do not close that gap.

The first tool consumer is an agent-facing preview/confirm pair, backed by
the hosted runtime's exact signed Mini submit and uncertainty journal. It
selects a retained `mini_publish` receipt, rather than accepting arbitrary
client filesystem paths or treating a named publication grant as permission
to publish the Store. The host performs package replay, rendering, carrier
verification, release-record verification, and outbox admission. Rust
orchestrates custody and exact retries; it must not recreate the release
policy as a second semantic implementation.

## Minimum acceptance evidence before enabling automatic POST

* A designated public-history Store, delegated agent, active reserved
  parent, and sufficient release allowance produce one accepted exact
  release record. The outbox retains that record's identity with the exact
  carrier, and a retry posts no different bytes.
* Changing even one carrier byte, package/prefix digest, Message-ID,
  publication target, Newsgroups value, or public-audience declaration
  makes the release/outbox comparison refuse before POST.
* A stale parent generation or root, no longer reserved parent, spent
  allowance, or revoked release grant refuses native admission or the
  outbox gate as appropriate. A prior `mini_publish` grant alone fails.
* A lost Mini response uses exact-call lookup and same-call retry. An
  uncertain fn POST retains its attempt and exact carrier and follows the
  existing no-unjustified-repost rule. A changed retry cannot mint a new
  release or silently replace the carrier.
* Historical v1 outbox records, the existing R/Q exchange, and current
  operator-driven publisher fixture preserve their previous meaning and
  behavior; none is relabelled as agent-authorized sharing.

For a private workroom, this public-history construction is insufficient.
Publishing P(N) exposes unrelated genesis and accepted records even if the
named publication itself is harmless. A dedicated public Store narrows the
prefix by construction but does not prove that a copied private result came
from a private admitted operation. A selective origin proof or verified
cross-Store release transition is separate kernel and verifier work. Until
then, the automatic native-prefix path should only target a genuinely
public-history Store with explicit whole-prefix authority.
