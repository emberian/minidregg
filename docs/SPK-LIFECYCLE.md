# SPK application lifecycle: failed first create, recovery, lawful repeat

This is the story of app 8502 on the hbox r2 world (Store key `1fbc8d0353180211`)
from its first START (generation 2) to the lawful repeat CREATE (generation 4),
and the shape of the v4 failed-create retry that makes the repeat lawful.

**Status, said plainly.** The v4 retry is source in this tree. What has run, and
where, is in "Evidence" below. Nothing in this document was executed on the
public node. On hbox the SPK broker runs as root, which is a tenancy defect
(see "Tenancy findings"). The cutover for the live r2 world is written out at
the end and has **not** been executed; the root decides when.

## The app state machine (Kernel/ApplicationGrain.lean)

| transition | generation | phase after |
|---|---|---|
| beginStart | +1 | 3 (starting) |
| claimStart | same | 9 (claimed: the custodian may launch) |
| completeStart | same | 4 (running) |
| beginStop / claimStop / completeStop | +1 / same / same | 5 / 10 / 2 |
| reconcileFailedStart | +1 | 2 (stopped) |

A START is three durable steps, each with its own receipt: BEGIN (the
management subject's signed intent, event23 for v3), CLAIM (one-shot launch
reservation, event24; the fresh-tip callback hands the committed projection to
the physical custodian), COMPLETION (the custodian's signed physical report,
event25). First creation is marked by two nullifiers: the BEGIN-time
**firstAttempt** marker and the completion-time **created** marker. A v3 BEGIN
for a create refuses once firstAttempt is consumed, whether or not a created
marker exists. That is what makes "create" happen at most once under v3.

## What happened to 8502

1. **g2, first create (07:07–07:14 EDT 10-03).** v3 BEGIN (op66/67/22) and
   CLAIM (op68/69/26) were admitted; the store moved the app to generation 2,
   phase 9. The resident unit `mini-spk-a8502-g2.service` (then `User=hbox`,
   the pre-root-bootstrap design) exited `resident refused: Permission denied
   (os error 13)` before launching anything. No completion exists. The app sat
   claimed at phase 9 with firstAttempt consumed and no created marker: the
   "install wedge" for START.
2. **g3, governed failed-START recovery (11:50–12:54).** The failed-START
   receiver (event66 family, opcodes 206 plan / 207 assemble / 208 submit /
   209 lookup) admitted a signed report that the g2 incarnation is dead (same
   InvocationID, no cgroup, MainPID 0) and moved the app to generation 3,
   phase 2. Receipt: acceptedCount 78, confirmation `installed`
   (`g2/failed-start-recovered-v1.json`, ingress SHA-256 `252bb442…`). The
   recovery certifies a dead incarnation, never the absence of effects: the
   volume g2 was given may hold partial state.
3. **g4 under v3 is refused (14:25).** The resident's v3 BEGIN plan (op66) got
   `launch BEGIN first-attempt or created marker refuses action`
   (`g4/begin-attempt/op66-frame.bin`). Correct: v3 must not create twice. The
   OnFailure supervisor then failed three times (`grain refused: No such file
   or directory`) and hit its start limit. No shortcut was taken: no marker was
   cleared and no created marker was faked.

## The v4 failed-create retry

Three new events, each a strict superset of its v3 analog, plus a selector
naming the recovery that licenses the repeat:

- **Selector** (`Kernel/ApplicationFailedCreateRetryEvidence.lean`): the
  accepted recovery's index and its full ingress. `retryToken selector` is a
  codec-66 nullifier with its own frame, distinct from the recovery's own
  marker, so one recovery licenses exactly one repeat.
- **Retry BEGIN, event69** (`…RetryBeginV4Ingress/Admission`): a v3 BEGIN plus
  the selector. The signed operation nonce is derived from the v3
  authorization bytes *and* the selector, so a signature for one recovery
  cannot be replayed against another. Admission re-runs every v3 check (current
  management law, installed package, descriptor/action shape) and additionally
  requires the BEGIN to repeat the original create exactly (same app, volume,
  package root, create index, command digest, `priorCreate = none`) from the
  recovered stopped state, with firstAttempt consumed, created **not**
  consumed, the recovery marker consumed and the retry token **not** consumed.
- **Retry CLAIM, event70** (`…RetryClaimV4Ingress/Core/Projection`): the
  ordinary current-claim admission plus the full original v4 BEGIN. Its intent
  consumes the retry token. It never clears the v3 firstAttempt marker. The
  fresh-tip handoff is `RETRY-CREATE-CLAIM-COMMITTED/v4`.
- **Retry COMPLETION, event72** (`…RetryCompletionV4*`): the custodian's
  physical running report for the retry claim; installs the created marker.

**Chronology, not structure, is the gate.** Each lower admission re-admits its
predecessor at a structural prefix of the same Store, which is not enough on
its own. `Kernel/NativeHostReplay.lean` keeps a `RetryHistory` minted only by
the replay walk's after-step: `recoveries` (event66 records admitted in this
walk), `beginsV4`, `claimsV4`. A retry BEGIN is admitted only if the recovery
at its index is in `recoveries` with identical ingress and record bytes; a
retry CLAIM only if its BEGIN is in `beginsV4`; a retry COMPLETION only if its
claim is in `claimsV4`. The live receivers
(`Kernel/ApplicationLifecycleRetry{Begin,Claim,Completion}V4Receiver.lean`)
admit against the same `Verified` walk and require exact post-CAS readback.

**Uncertainty.** As everywhere in Mini, an uncertain submit is never
resubmitted. The only recovery is the exact-ingress lookup
(`Kernel/ApplicationLifecycleRetryV4Lookup.lean`): op23 / op27 / op39 with the
retained ingress bytes; the claim lookup also requires the retry token in the
record.

**Wire.** No new opcodes. Ops 66/67, 68/69, 70/71 (plan/assemble), 22/23,
26/27, 38/39 (submit/lookup) dispatch on the canonical frame that decodes, as
op66 and op23 already did for v2/v3.

**Not yet covered (fails closed).** A retried incarnation is not entered into
the replay's `createdV3`/`runningV3` lists, so a STOP of the retried g4 and a
continue-START of g5 refuse until `RunningAt`/`CreatedAt` accept
`CompletionAtV4`.

## Evidence

As of commit 87b6c9b5 the v4 retry is **authored only**: no module has been
compiled, no test run, nothing executed on any world. The lane paused before
the hbox build window opened. Observations of the live r2 world above were
read-only (unit journals, attempt files); controls in the lane dir
`evidence/control-r2-before.txt` and `evidence/control-r2-units-before.txt`.

## Tenancy findings

- `mini-spk-broker serve` refuses to run unless euid is 0
  (`native/spk-host/src/broker.rs`, "mini-spk-broker runs as root"), and
  `spk-host resident-bootstrap` refuses unless root
  (`resident_privilege.rs`). The broker writes `/run/systemd/system` and drives
  the system manager. A broker as an unprivileged user is not a configuration
  of this code; it is a redesign (per-session uids, an unprivileged launcher
  with a root-held, minimal setuid helper).
- The resident unit name is pinned by Mini as `mini-spk-a<app>-g<gen>.service`
  with no Store or deployment identity. Two Stores on one host with the same
  app id collide, and a scratch copy of a Store collides with its original
  (the live r2 world already holds a failed system unit
  `mini-spk-a8502-g4.service`). This is the K-SPK deployment-id defect named
  in `deploy/spk-host/README.md`; it blocks any scratch replay of r2's app
  lifecycle on hbox.

## Cutover for the live r2 world (NOT executed; the root decides)

1. Build from the integrated tree: native Host (`scripts/build-native-host.sh`),
   `spk-host`, `mini`; run `cargo nextest ... -E 'test(retry_v4_)'`.
2. Stage the binaries root-owned under
   `/var/lib/mini-bigstep-hbox-r2/var/lib/mini/recovery/<new-dir>/`.
3. Add drop-ins (next number after 91/92) pointing the r2 store at the new Host
   and the broker template at the new `spk-host`; restart the store. The first
   operation pays the full replay audit (~614 s on 78 records against a flat
   600 s response deadline): warm the session with a read-only lookup first.
4. Generation 4's directory already holds the refused v3 attempt
   (`g4/begin-attempt/op66-frame.bin`, `lifecycle-begin-v3-active.json`), and
   the resident's v3 freshness checks refuse to proceed in it. Deciding how a
   host-refused, effect-free plan attempt is closed is part of the cutover; it
   must not be done by deleting the attempt files.
5. Reset the failed supervisor through the broker's `stop` verb and start
   `mini-spk-a8502-g4.service`. Expected receipts: retry BEGIN acceptedCount
   79, retry CLAIM 80, retry COMPLETION 81, app phase 4.
6. Known gap after success: STOP of the retried g4 and continue-START of g5
   refuse until the replay's running/created lists accept CompletionAtV4.
