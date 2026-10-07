/-
# Assurance.NativeAcceptedFixtureAuthority -- the HAND-WRITTEN authority of the native accepted fixture

No generator writes this module.  It states what the acceptance driver ASKED FOR
(`native/resource-client/objective-native-acceptance.py`), as `key = value` lines,
never what a run produced.  `Assurance.NativeAcceptedFixture.first_projection` checks
the re-run's projection (`Assurance.NativeAcceptedFixtureProjection`) against it, and
`scripts/native-accepted-fixture/generate.sh` refuses to write data whose projection
differs.  It is a Lean module (not a loose file) so that Lake rebuilds the check
whenever a line changes.  Changing it is its own commit with an
`Authority-Change: <reason>` trailer (`scripts/pipeline/check-fixture-authority.sh`).
-/
namespace Minidregg.Assurance.NativeAcceptedFixtureAuthority

/-- The authority lines. -/
def text : String := "
# AUTHORITY for Assurance.NativeAcceptedFixture -- HAND-WRITTEN. No generator writes this file.
# It states what the acceptance driver ASKED FOR, read from
# native/resource-client/objective-native-acceptance.py (`all`: world, publish, invoke --label first,
# ..., refuse --label r01-source-is-package --mutation source-atom --argument @package),
# never from a run. Changing it is its own commit with an `Authority-Change: <reason>` trailer
# (scripts/pipeline/check-fixture-authority.sh). The projection is
# Assurance/NativeAcceptedFixtureProjection.lean; `first_projection` checks the re-run against it and
# scripts/native-accepted-fixture/generate.sh refuses data whose projection differs.

# objective-first: `invoke --label first` (build_request: subject '7', roles = [notes], byte 7)
first.verdict = accepted
# the request's subject: the sponsor, subject '7'
first.subject = (some 7)
# roles = [notes]: one target incidence
first.targets = 1
# one signed envelope per incidence: the authority leg and the one target leg
first.receipts = 2
# every one of them signed by the request's subject (the sponsor's key)
first.receipts.signedBySubject = true
# the notes document (content, registry tag 1) carries the created atom and the result atom; the
# run's compute, bought by the request's capacity (proofWork), settles in the pay cell (tag 11)
first.writes = tag1, tag11
first.writes.targets = true
first.writes.payCell = true
# the authority cell is read, never written; no written cell is also guarded
first.guards.authorityCell = true
first.guards.writtenCells = false
# one invocation marker spent
first.nullifiers = 1
# the charge is the request's capacity: the driver's ENVELOPE, with proofWork = price(tariff, ENVELOPE)
# = base 1 + sourceTicks-tariff 1 * ENVELOPE.sourceTicks 100000 (world: --tariff-base/--tariff-tick
# unset, so both 1; every other tariff key 0)
first.charge.incidences = 8
first.charge.turnBytes = 2000000
first.charge.memoryTouches = 1000000
first.charge.storageBytes = 2000000
first.charge.witnessBytes = 2000000
first.charge.proofWork = 100001
first.charge.feeDebit = 0
first.charge.networkBytes = 0
first.charge.sideEffectCount = 8
first.charge.leaseByteBlocks = 0

# r01-source-is-package: a validly signed command naming the package as its source
refused.verdict = refused
refused.reason = objectiveSource
"

end Minidregg.Assurance.NativeAcceptedFixtureAuthority
