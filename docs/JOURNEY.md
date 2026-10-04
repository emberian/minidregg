# The journey is the definition of done

`native/resource-client/journey.sh MANIFEST.json NEW_RUN_ROOT` is the one
definition of done for the October 13 shellserver. It starts a fresh private
Store from the binaries the manifest pins (sha256-checked), runs J0–J8 ([the steps](#the-steps-j0j8-and-growth),
below), the growth measurement (G, between J6 and
J7), the 32-field typed-state check (K4), and list items 3–7 (M3–M7). It prints
one row per step (PASS / FAIL / UNBUILT, wall seconds, the artifact that decided
it), writes `journey-result.json`, and exits 0 only when every step passes. The
frontier is the first step that did not pass; it is read from a run, never
written by hand. Items 3–7 are UNBUILT until their lane adds
`native/resource-client/journey.d/m3.sh` … `m7.sh`; the hook contract (exported
variables, exit code, last-line artifact) is in the script's header, so landing
a hook turns a stub green without changing the script. The seven older
acceptance scripts are deprecated as gates: nothing they print is status, and a
behaviour of theirs that still matters becomes a journey step instead. They are
kept in this lane and not deleted:

| script | what it checks | where that lives in the journey |
|---|---|---|
| `newparticipant-acceptance.sh` | fresh one-sponsor genesis, service, sponsor workspace | **kept as J0's body**; `journey.sh` calls it |
| `acceptance.sh` | one-signer birth, content write, lost outcome recovered by exact retry, joint write | J2, J4, J6 (the joint write has no step yet) |
| `authority-acceptance.sh` | policy install, delegation, policy-refused owner mutation, child cannot manage, revocation, historical retry | J3, J5, J7, J8, J6 (revocation has no step yet) |
| `application-acceptance.sh` | two-participant app birth and observe, cross-session read refusal, restart replay | J5, J6; the running grain is M6 |
| `selected-release-acceptance.sh` | two Stores, owner-signed selected release, conflict / wrong signer / lost reply | none yet: list item 9 (second node over fn) |
| `selected-source-publisher-acceptance.sh` | source-side authorization and protected fn POST | none yet: list item 9 |
| `selected-source-drop-reply.sh` | test-only Host shim for the publisher gate | not a gate; goes when item 9 becomes a step |

## The steps J0–J8 and growth

The journey was fixed on 2026-09-29, before any tree ran it, as a tree-neutral
bake-off between Mini and Bread for the October 13 shellserver: the criteria and
the decision rule were written first so the result could not choose its own
yardstick. Each step is pass, fail, or not expressible.

| step | what happens |
|---|---|
| J0 | From clean state, start a private single-authority service with one sponsor identity. |
| J1 | Enroll an independently generated newcomer key. No operator edit to genesis or config on the newcomer's behalf. |
| J2 | The sponsor creates an ordinary resource under a law that permits ordinary use. |
| J3 | The sponsor delegates a narrower right to the newcomer: observe and mutate, without control or further delegation. |
| J4 | The newcomer signs a read, writes a field to 1, reads back 1. |
| J5 | A third key holding no grant attempts a read and a write. Both must be refused. |
| J6 | Stop the service and reopen the same Store. J1's receipt and J4's value are recovered. An exact retry of J4's call returns the original receipt and causes no second effect. |
| J7 | The sponsor replaces the law with one that still permits the newcomer's operation. The newcomer's EXISTING grant still works. |
| J8 | The sponsor installs deny-all. The newcomer's read and write are refused. The sponsor's own attempt to repair is refused too. |

J5, J7 and J8 encode decisions already made: observation needs authority, grants
survive a change of law, and a resource may lock its own management with no
owner bypass.

**Growth (G)** runs after J6 and before J7, on the same Store. At cumulative
accepted-record counts of 10, 100, 500 and 1000: the latency of one signed write
and one signed read (five samples each, median and worst), and cold reopen (stop
the service, start it, time until the first signed read returns). A level is
aborted, and that is recorded, if any single operation exceeds 600 seconds.

**Thresholds** for "a friend would call this interactive", at 1000 accepted
records: a signed write in at most 5 seconds, a cold reopen in at most 60
seconds. A tree that fails J5, J7 or J8 needs kernel changes to match the settled
semantics; one that fails the growth thresholds needs storage and recovery work;
one that cannot reach J0 in its time box has a build problem, and the time it
consumed is the measurement.
