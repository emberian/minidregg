# Authored workshop and community domains (upstream-Bend source)

The `.bend` modules here are **upstream Bend** source, checked through the
retiring BendTT path (sealed upstream parser and emitter, then `Book.check` in
`check-core.lean`). They are not Objective Bend. Objective Bend Core4 is Mini's
only Bend language; see [Objective Bend](../../docs/OBJECTIVE-BEND.md). What
survives from this directory is the **domain design**; the checked Books do not
carry over, and each domain must be ported to `.obend` to run on Core4.

## The domains

`Demonstration.bend` and `OrderedCapacity.bend`: a named nonmarket allocation
policy. Each request receives a prefix of the remaining inventory in frozen
request order; empty grants stay in the output; the conservation law keeps
complete token references and order, not only a quantity sum. Identifiers are
synthetic source inputs, not deployed rights.

`CatalogReview.bend`: recommendations and decisions bound to the complete source,
program, revision and policy. A successful adoption proposal preserves its
expected predecessor and selected candidate and still faces current native
authority.

`ReusableWorkshop.bend` and `MemberExtension.bend`: catalog, review, audit and
presentation, with a second author supplying a missing audit method and changing
presentation without editing the original modules. This was the Gen-1 example:
the Gen-1 linker that composed it into one checked BendTT Book was deleted on
2026-10-04. The review composition is ported to Core4 as
[ReviewBase](../../tests/objective-bend-source/ReviewBase.obend),
[ReviewMember](../../tests/objective-bend-source/ReviewMember.obend) and
[TwiceReview](../../tests/objective-bend-source/TwiceReview.obend).

`ContractedReview.bend`: dependent result interfaces carrying affine contract
terms. This relies on BendTT's dependent types; Core4 has no counterpart.

`WorkshopFaces.bend` over `WorldSurface.bend`: presentation faces selecting
individually admitted observation slots and independently prepared intents
(contract in [authored surfaces](../../docs/OBJECTIVE-BEND-SURFACE.md)).

`CollectiveAdoption`, `MarketMath`, `SingleSellerAllocation`, `UniformProRata`,
the settlement modules, `ResidentServiceCommons` and the coauthoring modules: see
[collective domains](../../docs/BEND-COLLECTIVE-DOMAINS.md),
[canonical settlement](../../docs/BEND-CANONICAL-SETTLEMENT-PLAN.md),
[service commons](../../docs/BEND-RESIDENT-SERVICE-COMMONS.md) and
[coauthoring](COAUTHORING.md).

`Prelude.bend` is the explicit pure library (Nat, List, Bool, Sigma) these modules
import as `Base`.

## Evidence, historical

On 2026-10-03 the seven Workshop consumer Books passed the pinned upstream
parser/checker (revision `947db722640c86247849343657bf2f7ef01cb7f1`), sealed import
adapter and BendTT emission, then BendTT `Book.parse` and `Book.check`, with no
opaque definitions. That checks the emitted BendTT programs. It says nothing about
Objective Bend, and it is not a theorem that any elaborator or native compiler
preserves their meaning.

## What porting needs

Core4 lacks several things these domains use: a Boolean eliminator and sums with
case (only `ifZero` on Nat branches), lists, label equality, effects, and checked
`requires`. Ranked in the [language guide](../../docs/OBJECTIVE-BEND.md#what-core4-lacks-the-roadmap).
List-of-Nat byte representations need checked byte, digest and text bounds;
truncation is not an encoding.
