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

Hard EOF or explicit
disconnect signals the owned process group immediately; the persistent
controller then stops its remaining members and sends Mini a signed generation
fence. A soft attachment lets the current reserved command or Hermes prompt
finish after the connector closes, then settles its configured charge. A later
connector can reattach to the same task. Each command name and all arguments
come from the operator's fixed allowlist.

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
must be the scoped Linux `bwrap` launcher with fixed `--network host` and an
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
  "timeoutSeconds":30
}
```

The real provider key stays in the private controller state directory. Each
worker receives only a new prompt token and a generated local Hermes profile.
Before forwarding one exact request, the controller retains its bytes, gets
a signed provider-task reserve with a parent-generation witness, and checks
the confirmed reserve's signed image boundary again at the durable send
boundary. It retains the response or uncertainty before acknowledging the
worker; an uncertain send is never retried automatically. Admin
`reconcile provider audited` checks the retained request/response digests and
signed held allowance, then settles the configured charge or refuses if it
cannot identify the held reservation. `reconcile provider abort` clears only
a definitively unreserved, unsent attempt. External effects require separate
`reconcile effects` acknowledgement. These are configured allowance units,
not a measured provider invoice.

For a scoped worker, optional command `wallTimeSeconds` is a fixed integer
from 1 to 1800; omission retains the launcher's 600-second cap. A hosted
provider's `hermes-acp` command requires at least 120 seconds. The generated
Hermes profile sets its per-MCP-call timeout to 60 seconds less than that
worker cap (540 seconds by default). A timed-out MCP call can still commit in
Mini; the controller retains its exact attempt and requires signed recovery,
without resending it. A longer deadline does not turn configured charges into
measured usage.

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
After the grain is idle and fully reconciled, `conversation new` explicitly
selects a fresh conversation while retaining the prior session ID in the
journal. It does not reset Mini authority, allowance, or unresolved effects.
The Linux worker sees `/workspace` as its ACP cwd and `HOME`; macOS sets a
private task-local `HERMES_HOME` under the configured workspace.

The `mini_grain_status` tool reads signed grain views. `mini_read_resource` reads
only an operator-named allowlisted resource using a separate observe grant;
it returns the complete bounded native view. Its `mini_publish` tool
uses a separate signed tool task, reserves allowance, and atomically settles
that task with allowlisted resource publications and a pinned parent-grain
no-op witness. The parent witness is authored by Lean and checked in the same
native transaction; a later generation cannot authorize the old prompt's
publication. The controller renews the parent worker policy after every
attach through a signed native policy install before allowing a prompt.
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
NNTP path is wired and tested. The provider-task controller path and local
gateway have focused Rust tests; signed native provider reserve plus the
plural-worker parent policy and a real Hermes prompt through that gateway
still need end-to-end acceptance. The completed upstream Hermes publication
used an earlier runtime without `providerTask`. The existing
Mini/fn two-Store evidence is in fn's `planning/evidence/two-store-join-1a9dd747-2026-09-24.md`;
this runtime does not reinterpret that synthetic acceptance as a hosted agent.
