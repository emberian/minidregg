# Authored collective and allocation domains

These are ordinary Bend source modules for authored worlds, community decisions,
resource exchange and service markets. Their effects must use the shared Mini
Plan and receiver; a successful domain decision never grants authority.

| Module | Purpose | Current qualification |
| --- | --- | --- |
| MarketMath | Exact structural natural arithmetic | Source and BendTT Book checked |
| CollectiveAdoption | Unique ballot use, derived tally, exact reviewed-source adoption proposal | Source and BendTT Book checked |
| SingleSellerAllocation | Descending bid price, original-index ties, last-filled price | Source and BendTT Book checked |
| UniformProRata | Lowest grid-index volume argmax and integer largest remainder | Source and BendTT Book checked |
| SingleSellerSettlement | Logical balance/preimage reference | Book checked; raw account balance writes are not a production route |
| SingleSellerTransfers | Earlier scalar-move grouping candidate | Source checked; superseded because scalar account targets are refused |
| CanonicalBookSettlement | Single-seller canonical book transfer batch | Source checked; new Book and native qualification pending |
| CanonicalUniformSettlement | Two-sided pro-rata batch through clearing pools | Source checked; new Book and native qualification pending |

The dependency modules Prelude and CatalogReview are shared with the authored
Workshop. Their identities are pinned in each sealed source package; imports
must not silently follow another revision.

## Decisions and actual effects

CollectiveAdoption retains the complete expected ballot predecessor and one
successor containing the new ballot. Tally values derive from that successor.
It validates unique electorate/ballot subjects and positive attainable quorum.
The proposal binds exact base/candidate source, executable program and revision;
prototype identities; kind/instance roots; migration; policy; electorate and
round. Installation derives endorsement from the retained valid closed state.
Current capabilities, laws, source roots and migration authority are still
receiver obligations. An endorsed Boolean supplied separately is insufficient.

SingleSellerAllocation has a general source proof that all filled quantities
plus the remainder equal the original supply. UniformProRata implements a
different rule and keeps its separate name. Its consumer checks exact per-side
volumes, per-order limits/capacity/backing and assets. Full generic fairness and
uniform-allocation optimality proofs are additional work.

Production money belongs to the single canonical resource book. Its closed
Operation.transfer takes natural source account, destination account, asset and
amount. CanonicalBookSettlement emits that operation shape from its computed
allocation. CanonicalUniformSettlement collects bid currency and ask goods into
two clearing pools, then distributes. The generic canonical Book batch validates
each operation against the preceding book and preserves asset conservation.

The source Account values must be derived from actual book membership and exact
balances. Coordinate identity is (account, asset), allowing one account to own
both money and goods. Duplicate reservation coordinates are refused. An
application cannot fabricate per-account physical roots or replace native
monetary operations with object-field writes.

The native joint receiver must install the book batch, room state, source-bound
evidence and private-return commitments atomically. Its generic book adapter is
under construction; these source modules do not establish a native receipt.

## Funding and disclosure

The intended generic financial preparation order is validated funding burn,
then application transfers, with one final book write. The source settlement
view must be explicitly derived from that fee-adjusted book while retaining
provenance from the original durable root and validated funding transition.
Using gross balances and charging afterward is not the same program context.

PrivateResult names an intended recipient, audience and key epoch. This is
typed result data, not a privacy certificate. Backend evidence, current release
authority and delivery remain distinct. Current arithmetic-only FHE profiles
do not implement private comparison, minimum, division or market allocation.

Structural natural arithmetic is an exact semantic reference. Realistic
atom-denominated markets need compact arithmetic with source refinement and an
explicit charge conversion. Silent machine overflow, floating tolerances and
an arbitrary small order ceiling are not substitutes.

## Checks

Run the portable source driver with the qualified Bend tooling directory:

    bun scripts/check-collective-source.ts TOOLING_DIR OUTPUT_DIR

It uses only sealed local imports and records source/package/Book identities.
It checks every published module, including explicitly superseded candidates.
It does not certify emitted Books.

Run the shared world/Workshop/check-core.lean against the emitted Book paths with the normal
repository Lean environment. It refuses opaque definitions and calls actual
BendTT Book.check. Follow the project resource/build coordination policy.

A useful receiving scenario has seller account 1 holding goods asset 7 balance
7 and payment asset 8 balance 10. Buyer 2 bids price 5, quantity 4, with payment
20 and goods 0. Buyer 3 bids price 3, quantity 5, with payment 15 and goods 2.
Clearing price is 3, quantities are 4 and 3. Transfers are (1,2,7,4),
(2,1,8,12), (1,3,7,3), (3,1,8,9). Final seller balances are 0 and 31;
buyer 2 balances 4 goods and 8 payment; buyer 3 balances 5 goods and 6 payment.
These expected values still need actual native qualification with stale-root,
revocation, account-membership, altered-amount, duplicate-use and atomicity
refusers. A source or kernel check must not be reported as that receiving test.


CollectiveDemonstration.actual_source_settlement evaluates the actual authored
settlement source and proves the four operation/two return result above, for
arbitrary native root, subjects, audiences and key epoch. The numeric example
is distinct from the general conservation theorem. Its sealed source check
passes; actual Book/native qualification remains separately recorded.
