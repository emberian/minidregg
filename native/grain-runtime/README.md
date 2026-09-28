# Mini grain runtime

`grain-runtime` is the physical controller for one already-born Mini
`AgentGrain` task. The Lean native host decides every transition. The Rust
controller reads the task through signed `mini query`, authors a `grain-intent`
through the Lean host via `mini submit`, and retains each exact signed attempt.
It never treats its local journal as authority to spend or mutate a resource.

Build this small crate independently:

```sh
cargo build --manifest-path native/grain-runtime/Cargo.toml
```

Run the controller as a persistent service, then connect from a terminal or
SSH forced command:

```sh
native/grain-runtime/target/debug/grain-runtime serve /absolute/task-config.json
native/grain-runtime/target/debug/grain-runtime connect /absolute/controller.sock
```

The connector's first line must be `attach hard` or `attach soft`. The line
interface then accepts `run NAME`, `hermes PROMPT`, `status`, `recover`, and
`disconnect`. Local operator reconciliation uses a separate private admin
socket, inaccessible through the forced-command connector:

```sh
grain-runtime admin /var/lib/mini/grains/task-7001/admin.sock 'reconcile parent audited'
grain-runtime admin /var/lib/mini/grains/task-7001/admin.sock 'reconcile provider audited'
grain-runtime admin /var/lib/mini/grains/task-7001/admin.sock 'reconcile effects'
```

Hard EOF or explicit disconnect signals the owned process group immediately;
the persistent controller then stops its remaining members and sends Mini a
signed `interrupt` generation fence. A soft transport close leaves its current
reserved command or Hermes prompt running, then settles its configured charge.
An abnormal worker or controller loss still interrupts a soft reservation;
the held allowance must be reconciled before the task can reattach. `cancel`
remains a distinct terminal native operation and is not a controller command.
Each command name and all arguments come from the operator's fixed allowlist.

An operator may separately enable model-free foreground MCP calls with
`foregroundTool: {"reserve":"100","charge":"0"}` and the existing `toolTask`.
This parent allowance is explicit; it does not copy a Hermes prompt budget or
claim measured model usage. A shell caller first obtains and retains a random
request ID, then sends one named tool call on the same controller socket:

```sh
grain-runtime tool-id
grain-runtime tool /absolute/controller.sock soft REQUEST_ID_32_HEX mini_grain_status /absolute/arguments.json
grain-runtime tool-result /absolute/controller.sock REQUEST_ID_32_HEX
grain-runtime tool-ack /absolute/controller.sock REQUEST_ID_32_HEX
```

`arguments.json` contains the tool's JSON arguments (for status, `{}`). The
request ID must be known before sending. `tool-result` uses a read-only
attachment and can recover an exact retained result after a lost response or
controller restart. Repeating `tool` with the same ID never sends the work
again, even after an explicitly acknowledged result has been evicted. A
different request body under that ID is refused. `tool-ack` is an explicit,
idempotent client acknowledgement; only acknowledged results can be evicted
from the bounded journal. An uncertain Mini or HTTP outcome remains fenced for
exact lookup or operator audit, without automatic resubmission.

Example configuration shape (IDs and paths must match an independently
bootstrapped native Mini deployment):

```json
{
  "mini": "/opt/mini/bin/mini",
  "host": "/opt/mini/bin/minidregg-host",
  "hostConfig": "/opt/mini/deployment/pinned-config.json",
  "hostSocket": "/run/mini/host.sock",
  "controlSocket": "/var/lib/mini/grains/task-7001/controller.sock",
  "custodyKey": "/opt/mini/secrets/task-controller.key",
  "stateDir": "/var/lib/mini/grains/task-7001",
  "cwd": "/srv/mini/task-7001",
  "task": "7001",
  "subject": "71",
  "capability": "81",
  "queryCapability": "82",
  "policyControlCapability": "83",
  "toolTask": {
    "task":"7002", "subject":"72", "capability":"84",
    "queryCapability":"85", "custodyKey":"/opt/mini/secrets/tool-controller.key",
    "parentCapability":"86", "parentObserveCapability":"87",
    "reserve":"100", "charge":"10",
    "allowedPublications":[
      {"kind":"object","target":"8001","capability":"88","observeCapability":"89"}
    ],
    "allowedReads":[
      {"name":"inbox","kind":"object","target":"8002",
       "observeCapability":"90","maxResultBytes":4194304}
    ]
  },
  "commands": [
    {"name":"inspect-fn","program":"/opt/fn/bin/fn-read-task",
     "args":["fn.agents"],"reserve":"100","charge":"10"},
    {"name":"hermes-acp","program":"/usr/bin/sandbox-exec",
     "args":["-f","/opt/mini/hermes.sb","/opt/hermes/bin/hermes-acp"],
     "reserve":"10000","charge":"10000"}
  ]
}
```

An optional `providerTask` gives a hosted Hermes prompt a separate Mini
authority and a controller-held provider key. It requires a distinct subject,
task, and custody key; the parent grain policy must name both the tool and
provider subjects at the prompt generation. The selected `hermes-acp` command
must be the scoped Linux `bwrap` launcher with fixed `--network none` and an
upstream `hermes-acp` executable. For example, alongside the tool task above:

```json
"providerTask": {
  "task":"7004", "subject":"9", "capability":"101",
  "queryCapability":"101", "custodyKey":"/opt/mini/secrets/provider-task.key",
  "parentCapability":"75", "parentObserveCapability":"75",
  "reserve":"3", "charge":"1",
  "model":"pinned-model", "upstreamUrl":"https://openrouter.ai/api/v1/chat/completions",
  "providerKeyFile":"/var/lib/mini/grains/task-7001/provider.key",
  "gatewayBind":"127.0.0.1:18762",
  "maxRequestBytes":1048576, "maxResponseBytes":8388608,
  "timeoutSeconds":30, "maxIterations":2
}
```

`maxIterations` is optional for provider-backed Hermes prompts. It accepts
an integer from 1 through 6; omission preserves the generated six-iteration
profile. This limits Hermes turn iterations, while the signed provider reserve,
worker wall deadline, and external provider spending cap remain separate bounds.
The controller listens on an owned mode-0600 Unix socket directly in its
private `stateDir`. The launcher bind-mounts only that socket into the worker's
private network namespace; a pinned `/agent/grain-provider-bridge` serves the
profile's `gatewayBind` loopback port inside that namespace. The worker can
still reach its separately mounted Mini MCP Unix socket. Neither socket gives
the worker the provider key. The bridge acknowledges a completed local HTTP
socket write on the same Unix connection before provider delivery is recorded;
a missing acknowledgement retains the held allowance. This does not prove
Hermes consumed the response.

Older deterministic HTTP loopback fixtures may explicitly set
`"localFixtureHostNetwork":true` and use `--network host`. That setting is
refused for an HTTPS upstream and is not a route for real provider credentials.

The real provider key stays in the private controller state directory. Each
worker receives only a new prompt token and a generated local Hermes profile.
Before forwarding one exact request, the controller retains its bytes, gets
a signed provider-task reserve with a parent-generation witness, and checks
the confirmed reserve's signed image boundary again at the durable send
boundary. It retains the response or uncertainty before acknowledging the
worker; an uncertain send is never retried automatically. A completed local
response has a retained, digest-checked replay entry before its fixed signed
settlement clears the hold. An SDK retry with the same exact request bytes in
the same prompt receives those cached response bytes without another upstream
send; at most 16 responses are indexed per prompt. A failed or unacknowledged
local delivery keeps the provider hold for reconciliation. A new explicit
prompt rotates the token and replay scope, so this is not cross-prompt
deduplication. Admin
`reconcile provider audited` checks the retained request/response digests and
signed held allowance, then settles the configured charge or refuses if it
cannot identify the held reservation. `reconcile provider abort` clears only
a definitively unreserved, unsent attempt. External effects require separate
`reconcile effects` acknowledgement. These are configured allowance units,
not a measured provider invoice.

Set `"metering":true` and `"charge":"0"` on `providerTask` to use the pinned
Host provider tariff instead of the configured fixed charge. Before reserve,
the controller checks the signed provider resource and the Host profile's
provider resource and model. Metered tasks also require operator-pinned
`"maxInputTokens"` (1–131072) and `"maxOutputTokens"` (1–8192). The former
must be a supported hard context ceiling for this exact provider/model and
the generated Hermes profile uses it as `context_length`; the latter is
inserted as `max_tokens` into the exact request before Reserve and forwarding,
or a worker-supplied lower value is preserved. The gateway accepts only the
supported text/function Chat Completions fields under this profile, rejects
unknown vendor extensions, output-limit aliases, and multi-completion
requests, and requires `stream_options.include_usage=true` for streams. If
the final response lacks actual terminal usage, the later quote path retains
the hold and refuses settlement.
The controller uses the pinned tariff rates to check the maximum input plus
output charge against the signed reserve before native admission. These
ceilings bound Mini's pre-send allowance under the operator's provider/model
accounting premise; they are not a universal tokenizer or a guarantee about
an external provider invoice. A separately configured provider-account spend
cap is still needed before a paid run. After an actual response, it retains
the exact request, body, and raw final-response headers, including one upstream
`Content-Type`. Read-only `mini meter` asks the Host to quote the retained
bytes and signed reserve; only the source-authored charge may be signed into
settlement. A missing terminal usage report, malformed headers, or uncertain
send keeps the allowance held and prevents another upstream request. Audited
recovery can quote a complete retained response after a worker fence, then
settle that charge; a confirmed settlement's exact Mini receipt is retained
before the hold is cleared. A proven no-send can settle zero. Provider usage
is a provider-reported claim under the operator tariff, not an invoice or an
atomic lease over external delivery.

For a scoped worker, optional command `wallTimeSeconds` is a fixed integer
from 1 to 1800; omission retains the launcher's 600-second cap. A hosted
provider's `hermes-acp` command requires at least 120 seconds. The generated
Hermes profile sets its per-MCP-call timeout to 60 seconds less than that
worker cap (540 seconds by default). For any other scoped Hermes worker, its
private mounted `/workspace/.hermes/config.yaml` must explicitly set
`timeouts.mcp.tool_call` to at least the same value. The controller parses
that exact config and refuses before Mini reserve if it is absent, nonfinite,
or too short; a larger value is still bounded by the worker unit lifetime.
This bounded private-config parse uses pinned `serde_yaml` 0.9.34, which is
deprecated; YAML supplies no Mini authority or admission decision.
The ACP `mcpServers` parameters do not set this upstream timeout. A timed-out
MCP call can still commit in Mini; the controller retains its exact attempt
and requires signed recovery,
without resending it. A longer deadline does not turn configured charges into
measured usage.

For a provider task, the gateway's Reserve and BeforeSend waits end at the
worker's absolute wall-clock deadline, measured before the wrapper starts.
Revocation or expiry also blocks a late controller acknowledgement before the
upstream HTTP send. Provider admission requires `hostSocket` and a pinned Mini
client with the read-only `mini continuity` command; the controller refuses
configurations without that socket before reserving allowance.

`hermes PROMPT` speaks ACP JSON-RPC to the actual upstream `hermes-acp`
process and registers the keyless `mini-grain` MCP proxy. Its
session ID is retained in the controller journal. Later prompts start a new
confined worker and use ACP `session/load` with that exact ID; they do not
silently start another conversation. The controller pins the workspace and
checks the closed upstream `state.db`/WAL fingerprint between prompts. The
upstream transcript is worker-authored state, not a Mini-signed record. If the
first prompt never creates a retained database row, loading fails, or the
database changes outside the controller, the task reports a retention issue.
An interrupted prompt stays marked in the journal. After physical stop and
Mini reconciliation, the controller accepts expected writes to the private
transcript store and tries `session/load` with the same ID. It reports that
the interrupted turn may be partial; if upstream never wrote a usable row,
the load fails rather than silently creating a new conversation.
For new publications, a confirmed Mini settlement records the generated tool
source, exact call and native outcome digests with its transaction/event IDs
in the same durable journal update that clears the tool hold. Before a later
Hermes prompt, the controller performs a read-only lookup of up to four
unreported exact calls and adds their verified receipt records (4 KiB total) as
fixed data beside the user prompt. It explicitly says the original MCP result
may not have reached Hermes and that later edits may supersede the historical
transition. A new conversation still receives unsurfaced grain receipts, tagged
as belonging to a prior session, without copying the old session ID or prose.
It neither fabricates a tool response nor resubmits the operation.
The records remain unsurfaced until that later ACP prompt completes. Earlier
journals without these receipt records, including the retained r6 timeout
fixture, require a separate typed migration; file discovery alone is not proof.
After the grain is idle and fully reconciled, `conversation new` explicitly
selects a fresh conversation while retaining the prior session ID in the
journal. It does not reset Mini authority, allowance, or unresolved effects.
The Linux worker sees `/workspace` as its ACP cwd and `HOME`; macOS sets a
private task-local `HERMES_HOME` under the configured workspace.

The `mini_grain_status` tool reads signed grain views. `mini_read_resource` reads
only an operator-named allowlisted resource using a separate observe grant;
it returns the complete bounded native view. Each read retains exact signed
bytes at `stateDir/resource-read-N/attempt/view.bin`. The configured
`maxResultBytes` bounds the native view up to 4 MiB; a final serialized MCP
result over 256 KiB refuses with the retained attempt path rather than
truncating. An allowlisted `fnInboxSummary:true` uses the Lean typed inbox
presentation for provenance and actions while keeping the same exact signed
view bytes. Its `mini_publish` tool
uses a separate signed tool task, reserves allowance, and atomically settles
that task with allowlisted resource publications and a pinned parent-grain
no-op witness. The parent witness is authored by Lean and checked in the same
native transaction; a later generation cannot authorize the old prompt's
publication.
On success, `mini_publish` retains the signed current tool-grain query fields
(`grain`, `targetRoot`, `authorityRoot`, `imageBoundary`) and adds
`publicationReceipt`. The nested receipt contains the exact confirmed
`transactionId`, `eventId`, `acceptedCount`, `imageBoundary`, and
`publicationTargetIds`, with `promptOperationId` and `toolOperationId` for the
current tool call. Its scope is `historical-accepted-transition`: those IDs
identify the accepted publication, not the current contents of its targets.
The controller selects the new journaled receipt for this prompt and Hermes
session; it does not select a prior matching target. Sending an MCP result does
not prove Hermes retained it or mark the journal receipt `reported`. If delivery
is lost, a later prompt may receive the same receipt again in the labeled
recovery data after exact read-only lookup.
If Mini definitively refuses a publication, the controller submits a signed
zero-charge settlement and disconnect for the delegated tool task. A confirmed
cleanup clears the held allowance, so Hermes may make another allowlisted read
and retry with a fresh root in the same prompt. An unresolved release or
disconnect retains its exact pending attempt or held allowance and blocks
further tools until exact lookup or owner reconciliation. The MCP error reports
which cleanup transition confirmed; it never treats a missing response as a
negative native receipt.

An operator-pinned `toolTask.resourceWorkspace` also exposes named Mini
resources through `mini_workspace_list`, `describe`, `read`, `propose`, `submit`,
and `recover`. The workspace client resolves typed proposals against current
signed state; the controller reserves and settles the delegated tool task for
submissions. A pinned birth context and namespace root additionally enable
`mini_workspace_create`. See [RESOURCE-WORKSPACE-MIGRATION.md](RESOURCE-WORKSPACE-MIGRATION.md)
for the compatibility boundary with fixed resource-birth families and the
evidence required before removing them.

Before attach or soft-to-hard mode change, the controller
compares the whole signed installed predicate with source-authored canonical
managed-law bytes for the configured worker subjects and permitted prior
generation. A custom or unrecognized law refuses automatic renewal. It then
installs the next-generation worker law through signed native policy control
before attach, so a controller crash after attach still leaves `interrupt`
admitted. An old grain with no configured worker policy has no automatic
policy-upgrade route; if its installed law refuses `interrupt`, the controller
remains fenced for explicit owner audit.
Hermes still retains its built-in tools; ACP permission requests are refused,
and an operator-selected OS confinement wrapper is mandatory. The Linux
`deploy/grain-host/bwrap` launcher runs each worker in a transient systemd
cgroup through its sibling `launch-gate`, mounts a single broker socket into
the sandbox, and withholds Mini keys and controller state. The runtime
requires the launcher's exact gate protocol before reserving allowance. It
durably arms a unique gate before spawning the wrapper, then fences that gate
after the immediate process-group signal and before clearing a child record.
It also kills the unit and checks MainPID and the full cgroup for remaining
processes. On restart, a gate-backed child can be fenced and audited without
signalling a possibly recycled PID; older child records still require an
operator physical audit. Gate tombstones remain in the private state directory.
Set a command's `systemdScope` to `true` only when its program is the
`deploy/grain-host/bwrap` launcher and `serve` runs as the matching active
`mini-grain-controller@TASK.service`; the runtime checks that unit's MainPID
before admitting a scoped worker.

The controller journals separate parent and tool pending operations before invoking `mini submit` and
a pre-spawn child marker before creating a worker. A successful `mini submit`
or exact `mini retry --mode lookup` confirms the native operation. If a crash
leaves an active-child marker, startup refuses to signal its saved PID/PGID:
the number may have been recycled. A paired launch gate permits recovery to
fence a late start, kill the unique unit, and verify its empty cgroup before
clearing that marker. An older marker without the exact gate protocol requires
an operator physical audit. If a custody subprocess might still create
`call.bin` after a controller crash, recovery likewise refuses to infer that
no operation occurred from a missing file; that uncertainty requires an
operator audit and reconciliation before the task can be relaunched. A settled
local command leaves its charge in the journal until Mini confirms settlement.
Completion and hard interruption have one atomic ordering point after physical
stop. If the controller dies before it records completion, recovery treats the
durable held allowance as uncertain and fences it through Mini; it never
infers a successful command from the missing child record.
The controller also journals the fixed charge before every reserve. After a
hard fence, admin `reconcile parent` or `reconcile tool` verifies the signed
held amount, reserve receipt, generation, and event boundary before settling
through Mini at the fixed configured charge. If later Mini events make origin
proof ambiguous, the operator must use the explicit `audited` form after
reviewing the exact retained attempt. Admin `reconcile worker audited`
records an explicit physical-process assertion; for a scoped worker it also
checks the controller MainPID, unique unit, and currently empty cgroup. Admin
`reconcile effects` separately acknowledges external uncertainty after all
signed holds resolve. All decisions and results remain in the journal.

The process-group test proves a normal descendant in the same session stops;
the Linux launcher has a separate host probe for a descendant escaping with
`setsid`. A process on another machine and provider effects remain outside
that physical boundary. A tool call already submitted when hard EOF is
detected can commit before the parent generation trip; its exact signed attempt
is retained for lookup, and external effects remain a reconciliation matter.

The `reserve` and `charge` values are operator-provided allowance units, not
measured provider bills. `fn_read` is not advertised until a fixed-config
NNTP path is wired and tested. The provider gateway retains the exact native
reserve call, confirmed outcome and four-field receipt anchor before any
upstream send. Immediately before sending, it checks current signed parent
and provider state and calls read-only `mini continuity` on those retained
canonical bytes through the pinned persistent Host socket. The returned
provider cell and full anchor must match the journal. This permits unrelated
ordinary Mini events after reserve but refuses a later provider write; it is a
check at send time, not an atomic lease across the external HTTP request.
Missing or changed evidence keeps the provider allowance held for audit.

The [local-provider acceptance](../../native/hermes-test-provider/evidence/2026-09-26/gateway-r1/)
used real upstream Hermes with a deterministic local HTTP endpoint and signed
Mini provider reserve, tool publication and fixed-charge settlement. That
earlier runtime used the conservative whole-image boundary; the op17
continuity consumer requires a separate source-matched native run before its
receiving claim. The existing
Mini/fn two-Store evidence is in fn's `planning/evidence/two-store-join-1a9dd747-2026-09-24.md`;
this runtime does not reinterpret that synthetic acceptance as a hosted agent.
