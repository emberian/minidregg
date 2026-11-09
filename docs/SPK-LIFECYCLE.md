# SPK application lifecycle: START, failed-START recovery, the failed-create retry

How a Sandstorm application grain is started under Mini's Lean receivers, what a
failed first create leaves behind, and the v4 retry that makes a second create
lawful afterwards. The retry is **wired and unit-tested at the source level**
(Lean receivers in `Host/Main.lean`, Rust natives in `native/spk-host`); no run of
it on any box is recorded in this repository.

## Versions that exist

| version | Lean | on the live op 22 submit path |
|---|---|---|
| v1 | `Kernel/ApplicationLifecycle{Begin,Claim,Completion}*.lean` | no |
| v2 | `Kernel/ApplicationLifecycle{BeginV2,ClaimV2,CompletionV2}*.lean`, `…V2Lookup.lean` | BEGIN and CLAIM no; the CompletionV2 frame is the live COMPLETION ("fresh completion requires canonical launch-bound v2 ingress", `Host/Main.lean` `applicationLifecycleCompletionSubmitSession`) |
| v3 | `Kernel/ApplicationLifecycle{BeginV3,ClaimV3}*.lean`, `…V3Lookup.lean` | yes: fresh BEGIN "requires canonical launch-bound v3 ingress" (`Host/Main.lean` `applicationLifecycleBeginSubmitSession`; CLAIM likewise in `dispatchLifecycleClaimSubmitSession`) |
| v4 retry | `Kernel/ApplicationLifecycleRetry{Begin,Claim,Completion}V4*.lean`, `…RetryV4Lookup.lean`, `Kernel/ApplicationFailedCreateRetryEvidence.lean` | yes: the same op 22/26/38 submit and 23/27/39 lookup try the v4 frame first (`Host/Main.lean`: `applicationLifecycleBeginSubmitSession`, `applicationLifecycleBeginLookupSession`, `applicationLifecycleClaimLookupSession`, `applicationLifecycleCompletionSubmitSession`, `applicationLifecycleCompletionLookupSession`, and for op 26 `dispatchLifecycleClaimSubmitSession` → `dispatchLifecycleRetryClaimV4SubmitSession`) |

The Rust side is `native/spk-host/src/lifecycle_v3_*.rs` (including the STOP
lane) and `lifecycle_v4_retry{,_claim,_completion}_native.rs`; the resident
service reads the retry lane's markers (`native/spk-host/src/resident_service.rs:44`,
`:348`; `native/spk-host/src/grain.rs:879-917`). The product's "install an
application" step uses v3 (`docs/DEMO-EXPERIENCE-2026-10-27.md`, step 7); the
member's request cell is `Kernel/AppsRequest.lean`, and the lifecycle receivers
are the custodian's side of it. The operation bytes are in
`protocol/host-operations.json` (22/23, 26/27, 38/39 submit/lookup; 44/45, 50-53
plan/assemble; 66-71 launch plan/assemble; 206-209 failed-START recovery).
The retry adds **no opcode**: the same bytes dispatch on the frame that decodes.

## The app state machine

`Kernel/ApplicationGrain.lean:388-403` is the transition table (phase after:
beginStart 3, claimStart 9, completeStart 4, beginStop 5, claimStop 10,
completeStop 2, reconcileFailedStart 2; every `begin*` and
`reconcileFailedStart` adds one to the generation, the rest keep it).

A START is three durable steps, each with its own receipt: BEGIN (the management
subject's signed intent), CLAIM (a one-shot launch reservation; the fresh-tip
callback hands the committed projection to the physical custodian), COMPLETION
(the custodian's signed physical report). First creation is marked by two
nullifiers: the BEGIN-time **firstAttempt** marker and the completion-time
**created** marker. A v3 BEGIN for a create refuses once either is consumed
(`Kernel/ApplicationLifecycleBeginV3Admission.lean:78-89`, theorem
`consumed_first_attempt_refuses_create` at `:95`; the authoring refusal text is
`Host/ApplicationLifecycleLaunchBeginAuthoring.lean:242`). That is what makes
"create" happen at most once under v3. A CLAIM that never completes (the
physical launch failed before anything ran) leaves firstAttempt consumed and
created not: a wedge for a v3 create.

## Failed-START recovery

The failed-START receiver (`Kernel/ApplicationFailedStartRecovery*.lean`, event66,
opcodes 206 plan / 207 assemble / 208 submit / 209 lookup,
`protocol/host-operations.json`) admits a signed report that the claimed
incarnation is dead and moves the app to the next generation, stopped
(`reconcileFailedStart`). It certifies a dead incarnation, never the absence of
effects: the volume that incarnation was given may hold partial state.

## The v4 failed-create retry

Three events, each a strict superset of its v3 analog, plus a selector naming the
recovery that licenses the repeat:

- **Selector** (`Kernel/ApplicationFailedCreateRetryEvidence.lean`): the accepted
  recovery's index and its full ingress. `retryToken selector` (`:49`) is a
  nullifier distinct from the recovery's own marker, so one recovery licenses
  exactly one repeat.
- **Retry BEGIN, event69** (`Kernel/ApplicationLifecycleRetryBeginV4Admission.lean`,
  `…Receiver.lean`): a v3 BEGIN plus the selector. The signed operation nonce
  is derived from the v3 authorization bytes and the selector, so a signature for
  one recovery cannot be replayed against another. Admission re-runs the v3
  checks and additionally requires the BEGIN to repeat the original create
  exactly from the recovered stopped state, with firstAttempt consumed, created
  not consumed, the recovery marker consumed and the retry token not consumed.
- **Retry CLAIM, event70** (`…RetryClaimV4{Ingress,Core,Projection}.lean`): the
  ordinary current-claim admission plus the full original v4 BEGIN. Its intent
  consumes the retry token and never clears the v3 firstAttempt marker. The
  fresh-tip handoff tag is `DREGG/APPLICATION/RETRY-CREATE-CLAIM-COMMITTED/v4`
  (`Kernel/ApplicationLifecycleRetryClaimV4Projection.lean:34`).
- **Retry COMPLETION, event72** (`…RetryCompletionV4*.lean`): the custodian's
  physical running report for the retry claim; it installs the created marker.

**Chronology, not structure, is the gate.** `Kernel/NativeHostReplay.lean` keeps
a `RetryHistory` (`:866`: `recoveries`, `beginsV4`, `claimsV4`) minted only by
the replay walk's after-step. A retry BEGIN is admitted only if the recovery at
its index is in `recoveries` with identical ingress and record bytes
(`admitBeginV4At`, `:2275`); a retry CLAIM only if its BEGIN is in `beginsV4`; a
retry COMPLETION only if its claim is in `claimsV4` (`:2639-2647`). The live
receivers require exact post-CAS readback.

**A retried incarnation is a normal one afterwards.** A retry completion that
created the volume enters the same `createdV3`/`runningV3` chronology as a v3
completion (`createdV3After`, `runningV3After`; theorems
`createdV3After_retry_completion` `:2991`, `runningV3After_retry_completion`
`:3013`), so a STOP of the retried incarnation and a continue-START after it
select it.

**Uncertainty.** An uncertain submit is never resubmitted. The only recovery is
the exact-ingress lookup (`Kernel/ApplicationLifecycleRetryV4Lookup.lean`;
op 23 / 27 / 39 with the retained ingress bytes); the claim lookup also requires
the retry token in the record.

## STOP and its reconcile

A STOP is BEGIN (op 22), CLAIM (op 26) and COMPLETION (op 38), driven by
`lifecycle_v3_stop_service::run` against the generation's hostd journal
(`Running` → `Fenced` → `Stopped`). A rerun of `spk-host grain stop` resumes from
what the attempt directories retain; nothing is resubmitted.

- **A definite refusal did not happen.** An op 26 the Host answered with a refusal
  (`effect: no-record`) is looked up by op 27 on its exact ingress. Absent after an
  answered submit, the attempt is set aside whole (`stop-claim-absent-<nonce>`,
  decision `absent-set-aside`) and STOP authors a fresh claim
  (`lifecycle_v3_stop_recovery::reconcile_running`). Only an absence after a *lost*
  reply stays undecided. `claim image boundary differs from loaded image` is such
  a refusal: the claim's world root is no longer the current one, as when several
  grains STOP at once.
- **A committed claim arms its fence.** When op 26 committed, the permit
  (`stop-claim/committed-v3.bin`) and the fence marker (`stop-fence-requested.json`)
  are retained. If the fence never entered `Fenced` (its pre-stop check refused, or
  the process ended first), the next run reselects the same committed claim from
  the current Host and arms that same fence (`resume_committed_exact`); a `Fenced`
  journal resumes with `resume_fenced_exact`.
- **The pre-stop check admits a dead unit, never a live stranger.** The manager
  stop may reach only the claimed incarnation. A crashed claimed incarnation (same
  InvocationID, failed) is admitted. So is a unit whose InvocationID moved on to a
  later incarnation that has also ended (`failed` or `inactive`, MainPID 0, no job,
  no manager cgroup, the recorded cgroup unpopulated): systemd never reuses an
  InvocationID, so nothing of either incarnation runs and the stop only resets the
  failed state. A later incarnation that runs is refused (`unit invocation drift
  before stop`; `hostd::UnitStopAudit::before_stop_observed`). On demo-dry,
  2026-11-09, three grain units restarted by name started later incarnations that
  failed at bootstrap; the STOPs their supervisors began committed their claims
  and then refused at this check.

## Checks that exist

- Rust unit tests named `retry_v4_*` in `native/spk-host/src/lifecycle_v4_retry*_native.rs`
  and `grain.rs:1666` (the retry lane's markers read as their own lane).
  Narrow run: `cargo nextest run --manifest-path native/spk-host/Cargo.toml -E 'test(retry_v4_)'`.
- The retry modules are in the umbrella the Lean RSS table measured
  (`scripts/pipeline/lean-module-rss.tsv`, e.g. `Kernel.ApplicationLifecycleRetryCompletionV4Receiver`).

Not recorded anywhere in this repository: a journey that drives a real failed
create through recovery and the retry.

## Tenancy

Resident tenancy (operator broker under `systemctl --user`, the root-installed
one-shot volume helper, bwrap-made user namespaces, store-id-checked unit names)
is described where it is deployed from: `deploy/spk-host/USER-TENANCY.md` and
`docs/SPK-RESIDENT-PRIVILEGE-BOUNDARY.md`. The native grain author emits the
resident config and runs the resident's own decoder before a unit is installed;
`scripts/spk-platform/prepare-resident-config.sh` delegates to
`spk-host grain prepare-resident` (`native/spk-host/src/grain.rs:1596`).
