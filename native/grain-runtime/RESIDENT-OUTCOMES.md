# Historical completion supersession

`grain-runtime resident-outcome ADMIN_SOCKET PRIVATE_REQUEST` reviews one explicit
historical claim. It never rewrites resident.json or infers a generic failed turn
from absent output. The first supported classification is
`unsupported-completion`: an explicitly paired managed-provider checkpoint records
zero admitted provider requests and no settled generation evidence while its
resident frame claims completion.

Request (owned regular0600 file):

```json
{
  "type":"mini-hermes-completion-supersession-v1",
  "residentState":"/private/controller-state/resident",
  "expectedResidentSha256":"EXACT_CURRENT_RAW_RESIDENT_SHA",
  "expectedBindingSha256":"CANONICAL_CURRENT_JOURNAL_BINDING_SHA",
  "historicalResident":{"path":"/private/history/resident.json","sha256":"EXACT_RAW_SHA"},
  "historicalController":{"path":"/private/history/journal.json","sha256":"EXACT_RAW_SHA"},
  "forensicPairing":{
    "type":"mini-hermes-historical-completion-pairing-v1",
    "historicalOperationId":78,
    "sessionId":"EXACT_HISTORICAL_SESSION",
    "completedOrdinal":1,
    "completionSha256":"CANONICAL_HISTORICAL_LAST_COMPLETION_SHA",
    "assertion":"Explicit operator assertion pairing these exact historical checkpoint bytes and the recorded completion ordinal; the old wire lacks source prompt origin, so this association is forensic rather than a source-generated causal receipt."
  }
}
```

Canonical hashes use compact sorted-key JSON. The old and current configurations
must preserve the exact managed authorities and transport; only the three admitted
operational settings (contextWindowTokens, maxIterations and maxRequestBytes) may
differ. Different Host/authority lineage needs its own receiving support. The
historical checkpoint must have no pending holds/effects or admitted provider
requests. A historical frame carrying the new source origin is intentionally
outside this legacy receiver and must use that stronger identity instead.

The current resident lock, exact raw-state hash and fresh complete native/process
checkpoint gate classification. A stale session fingerprint also blocks it. An
operator assertion does not waive these checks. The archive preserves historical
and current journals/resident, the original request, fresh quiescence and a typed
decision under `RESIDENT/outcome-reviews/review-OPERATION/`. The decision reports
identityBasis=operator-forensic-pairing and supersedingOutcome=unsupported-completion.

Only after that archive is durable does a unique ordinal selection appear at
`RESIDENT/outcome-corrections/completed-ORDINAL.json`, pinned to the decision hash.
The immutable ledger rejects duplicate ordinals, changed decisions, unknown files
or corrections beyond the raw recorded count. A malformed interrupted selection
blocks consumption for explicit retained recovery; it is never treated as absent.

Consumers derive `qualified = recorded - valid superseded ordinals`. Resident
prompt limits and completion status use qualified counts; status also reports
recordedCompletions. The raw completed counter, lastInput and original frame remain
unchanged. The existing unchanged-input check still prevents automatic replay of
the prior assignment. Classification itself sends no prompt, payment or tool call.

After a lost reply, inspect the exact ordinal selection and immutable decision.
An already selected ordinal is never subtracted twice. This ledger classifies
past evidence; it does not claim that later agent work succeeded or authorize a
new model budget.
