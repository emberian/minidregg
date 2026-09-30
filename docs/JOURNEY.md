# The journey is the definition of done

`native/resource-client/journey.sh MANIFEST.json NEW_RUN_ROOT` is the one
definition of done for the October 13 shellserver. It starts a fresh private
Store from the binaries the manifest pins (sha256-checked), runs J0–J8 from
`claudesplosion/bakeoff/BAKEOFF.md`, the growth measurement (G, between J6 and
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
