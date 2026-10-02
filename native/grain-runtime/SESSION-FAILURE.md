# Retrospective failed-session closure

`grain-runtime session-failure ADMIN_SOCKET PRIVATE_REQUEST`

The request is an owned regular mode0600 JSON file:

```json
{
  "type":"mini-hermes-session-failure-reconciliation-v1",
  "residentState":"/private/controller-state/resident",
  "expectedResidentSha256":"SHA256_OF_EXACT_RESIDENT_FILE_BYTES",
  "expectedBindingSha256":"CANONICAL_JSON_SHA256_OF_JOURNAL_BINDING",
  "expectedSessionSha256":"CANONICAL_JSON_SHA256_OF_JOURNAL_HERMES_SESSION",
  "expectedCurrentFingerprint":"EXACT_CURRENT_SOURCE_HERMES_STATE_FINGERPRINT",
  "failureEvidence":"/private/retained-observed-failure.json",
  "failureEvidenceSha256":"SHA256_OF_EXACT_FAILURE_EVIDENCE_FILE",
  "historicalRuntime":"/private/history/bin/grain-runtime"
}
```

Canonical hashes use compact sorted-key JSON (serde_json Value); Python equivalent
`json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()`.
The current fingerprint uses the existing source `hermes_state_fingerprint`
representation of state.db and optional state.db-wal. It is checked before and
after fresh signed queries and immutable state copying.

This receiver intentionally handles the bounded historical form
`mini-hermes-observed-acp-failure-v1`: one scoped worker in an exact controller
invocation, a typed -32003 failure, and its source-confirmed local wait/fence log.
It re-reads trusted journalctl invocation records and requires exact retained
worker/error records, correct source executable/unit metadata and chronology.
An arbitrary edited error note, missing trusted log, multiple prompt workers,
lost reply or absent typed failure is refused. More complex histories must use
the future source-owned per-prompt failure artifact.

The historical runtime must still match the retained image hash. The exact
settled provider replay request/response/meter hashes are checked, and the final
user text in that request must match the current resident's uniquely bound failed
pending prompt. Existing resident_reconcile supplies the shared strict
pending/completion identity check.

The resident flock spans inspection, archival and publication. Fresh source
quiescence must report precisely the two stranded session/resident prompt markers,
all configured native purses unreserved, current physical stop evidence, and no
other retained effects, holds, attempts or active clients. The only session
integrity discrepancy admitted is the expected stale fingerprint, independently
replaced by the twice-observed exact current fingerprint.

An immutable directory under `STATE/failed-session-reconciliations/` retains full
controller before/after, unchanged resident, request, raw failure, trusted invocation
records, settled provider request/response/meter, fresh quiescence, current DB/WAL
copies and typed decision before one atomic controller-journal publication. Only
session.pendingPrompt=false, session.stateFingerprint=current and
session.loadVerified=false change. Native receipts and all other state remain
exact. The response names the archive and decision operationId.

The resident pending prompt is deliberately preserved. The existing
`resident-reconcile failed` receiver can subsequently close it with fresh evidence.
The stored completed counter, lastInput and completion are never rewritten by this
command; historical false-completion correction is a separate auditable outcome.
A fresh source session/load remains required before another model prompt.

If the final reply is lost, inspect retained decision and controller-after before
any repeat. This initial receiver does not blindly replay a completed closure;
the expected prior session hash deliberately rejects already changed state.

## Explicit historical identity limitation

Normal requests must have `legacyForensicAdmission: null`; their source completion
`residentOrigin` must exactly match the current durable journal origin, resident
prompt ID/text digest, failure operation and session. The forward resident wire
carries that ID to source admission, immutable operation/session records, worker
ACP metadata and the completion frame. A later identical prompt cannot borrow an
older origin. Pre-admission failures without origin remain unresolved.

Old wire records lack this causal receipt. The separate legacy admission is an
explicit operator forensic assertion, not source-derived identity:

```
legacyForensicAdmission: {
  type: "mini-hermes-legacy-forensic-admission-v1",
  expectedJournalSha256: CANONICAL_CURRENT_FULL_JOURNAL_SHA,
  residentPendingSha256: CANONICAL_EXACT_PENDING_SHA,
  promptOperationId: EXACT_OPERATION,
  sessionId: EXACT_SESSION,
  residentPromptId: EXACT_RETAINED_ID,
  assertion: EXPLICIT_REVIEWED_IDENTITY_LIMITATION_AND_FORENSIC_ASSOCIATION
}
```

The current full journal, resident and session must match before queries allocate
any new counter. The decision preserves this assertion and labels identityBasis
`operator-forensic-assertion`. It grants no exception to fresh native/process
closure, trusted complete invocation evidence, replay/artifact checks, DB capture,
or the prohibition on clearing other uncertainty. The private qualification
request preparation helper is deliberately restricted to reviewed task8781 /
operation94 / invocationc2fdf82ef7ca45fcaed78e7715d155c6; it only prepares a new mode0600
request and does not invoke a receiver.

Publication failures are classified by exact current bytes. If rename occurred,
the Runtime adopts the known after-state even if directory sync reports an error;
it cannot overwrite the closure from stale memory. Unknown bytes freeze current
and subsequent mutation through a retained uncertainty marker and the common
open/save/input hooks. A typed investigation is required before clearing that
marker; this command supplies no generic reset.
