# Reds (owned by the builder, rewritten whole each round)

Tip: `76511e768bbc` (authority projection: the revoked set and the parents are read from the cell). Gate finished
2026-10-31T19:59Z; the umbrella stage is still running. green: `83e926874e38` (batch 4).
Builder: dregg-build2 `/srv/integ` (BUILDER_DRY=1 until the box has a GitHub write key; this file was written by hand
from its logs), logs `/srv/integ/builder`, gate `/srv/integ/gate-76511e76` (the first gate run on dregg-build2,
scripts/pipeline/gate from main 408962f1d).

| stage | signature | reruns? | same place as last round? | detail |
|---|---|---|---|---|
| gate:j14-apps | bootstrap: `minidregg-client-consent` dies, "durable log is not a turn log: a verification walk carries no World" | no (deterministic) | new | /srv/integ/ci/j-76511e/journey.log; cause ed875b899/042f2a0c1 (member-side); fix 86c9dbddb on main, not yet built |
| gate:tour | J2-J8 FAIL after J0/J1 PASS; JWF has no workspace | not rerun | new | /srv/integ/gate-76511e76/journey.log; same consent-provider exit |
| gate:enrol-resume | rc=1, "local consent refused before signing: the resident consent provider ended" | not rerun | new | /srv/integ/gate-76511e76/enrol-resume.log |
| gate:composed | scratch world: jworld FAIL enroll member-4 at `enroll plan member-4 ...` | not rerun | yes | /srv/integ/ci/c-76511e/log/world.err |
| gate:flatness | doc-new exit 1: local consent process "ended before answering" | not rerun | yes | /srv/integ/ci/f-76511e/submit/transcript/doc-new.err |

Every row above has the consent provider exiting at its first refresh, so they are expected to clear together with
86c9dbddb. The next builder round builds the main tip (which has 86c9dbddb, FORMAT (a) f28cd8457 and seam 1) and
re-records the fixtures for FORMAT's epoch move.

Suspects since green: `git log 83e926874..76511e768`; for these rows, `ed875b89` and `042f2a0c` perf(consent)
(owner: member-side).
