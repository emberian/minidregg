# Same-Store GitWeb journey driver checkpoint

`scripts/spk-platform/journey.sh` is the single private action ledger for the
existing r3 fixture; its evidence directory is
`ROOT/continuations/gitweb-journey`. `status` reads the retained qualifier,
birth, app, INSTALL, and resident markers without writing to the Store. On
2026-09-27 its keyless r3 projection is `r3-journey-status.json`: signed-SPK
v2 qualification passed, the first birth was absent at its last exact op3
lookup, and no app/INSTALL/resident/browser/API/content milestone had been
accepted. The attempted first birth and its original 212,637-byte call remain
in the same private Store. No direct retry was launched by this driver.

The fresh-only `prepare.sh`, `run-base.sh`, and
`native-positive-base.sh` cannot resume the r3 Store. `resume-base.sh` instead
requires the original birth call/config/Host/client pins, an original confirmed
submit result, and a later exact op3 `replayed` result with identical
transaction, event, count, and image boundary. It checks the retained source
manifests, saves the receipt and exact source-derived continuation programs,
and claims one action before running any later native mutation. Its generated
programs start *after* the already-submitted birth, *after* the fresh-only
workroom invocation, and *after* run-base's fresh-Store preflight. It never
regenerates genesis, keys, the first call, or a fabricated `outcome.json`.
Completed workroom/application/handoff phases can be resumed from their saved
markers. A started phase without completion refuses an automatic rerun; an
uncertain Mini attempt needs its own exact lookup/recovery review.

The continuation pins the original Host SHA `95cd66117983796e4887f03f3ddd25b048d70713fb56ae93c36dbbc379139285`.
If profiling yields an optimized successor, this script refuses it. A
separate source-qualified profile/replay transition and review is required
before using that successor on the retained Store.

The driver exposes only the currently sourced stage transitions:

1. Adopt the original birth receipt and finish the retained base; verify the
   app/package/snapshot and all session readbacks before writing the INSTALL
   handoff.
2. Check a separately qualified v3 Mini Host against the same Store and
   original four-field app receipt, then prepare private INSTALL custody.
3. Run `spk-host install-prepare` and `install-complete` once each against the
   same journal. The action marker is durable before a native event.
4. Create the three source-delegated observe-only app grants, each with signed
   recipient readback. Prepare a human-only resident START candidate from a
   confirmed INSTALL.

The driver intentionally has no resident launch, browser dispatch, agent API
dispatch, final event22 ticket, or same-app content-publish action yet.
`prepare-resident` rejects nonempty v2 agent custody requests: that older path
cannot stand in for the required v3 agent route. The human browser caller and
agent API caller must both be accepted by native current state before the
GitWeb push/403/browser readback can be called integrated acceptance. The
private GitWeb package probe already demonstrated a real push/readback and
guest refusal in a separate physical fixture; it is the expected terminal
behavior, not an r3 result. A selected Git commit/file-to-Mini content atom
publication remains a further explicit join.

Source-only checks at this checkpoint: `sh -n`, ShellCheck, and diff-check pass
for both scripts. Exact copied r3 source hashes were `provision-member.sh`
`0cf312892f2453daa9a1313dafee188eefa48846543ad16df176eabcfe36a9c7`,
staged application source
`80dfaf29545fb86ea420517179b7eb24f3bdcb42da1eb0a82043e67750861c68`,
and original run-base
`c913a09d52cb15562f838acf46e7fa6aea8c1bf072c3eb76547a32338847adde`.
The exact source-body extraction produced 385 workroom, 318 application, and
75 handoff lines, all `sh -n` green. A read-only wrong-receipt invocation on
r3 refused with `original submit receipt is not confirmed` and created no
action directory. This is a source and refusal gate, not successful same-Store
base continuation or final hosted app acceptance.

Root review tightened retained-file custody to reject group as well as world
writes. This continuation pins the original Host2649 binary; a faster successor
requires an explicit source-qualified same-Store compatibility transition before
this script can use it. The original attempt's artifact identity must not be
rewritten merely to pass the pin check.
