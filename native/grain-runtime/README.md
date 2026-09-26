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
interface then accepts `run NAME`,
`hermes PROMPT`, `status`, `recover`, and `disconnect`. Hard EOF or explicit
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

`hermes PROMPT` speaks ACP JSON-RPC to the actual upstream `hermes-acp`
process and registers the keyless `mini-grain` MCP proxy. Its
`mini_grain_status` tool reads a signed tool-task view. Its `mini_publish` tool
uses a separate signed tool task, reserves allowance, and atomically settles
that task with allowlisted resource publications and a pinned parent-grain
no-op witness. The parent witness is authored by Lean and checked in the same
native transaction; a later generation cannot authorize the old prompt's
publication. The controller renews the parent worker policy after every
attach through a signed native policy install before allowing a prompt.
Hermes still retains its built-in tools; ACP permission requests are refused,
and an operator-selected OS confinement wrapper is mandatory. The Linux
`deploy/grain-host/bwrap` launcher runs each worker in a transient systemd
cgroup, mounts a single broker socket into the sandbox, and withholds Mini
keys and controller state. The controller signals the process group first,
kills the unit, and observes it inactive before clearing the child record.

The controller journals separate parent and tool pending operations before invoking `mini submit` and
a pre-spawn child marker before creating a worker. A successful `mini submit`
or exact `mini retry --mode lookup` confirms the native operation. If a crash
leaves an active-child marker, startup refuses to signal its saved PID/PGID:
the number may have been recycled. If a custody subprocess might still create
`call.bin` after a controller crash, recovery likewise refuses to infer that
no operation occurred from a missing file. Both conditions need an operator
process audit and reconciliation before the task can be relaunched. A settled
local command leaves its charge in the journal until Mini confirms settlement.

The process-group test proves a normal descendant in the same session stops;
the Linux launcher has a separate host probe for a descendant escaping with
`setsid`. A process on another machine and provider effects remain outside
that physical boundary. A tool call already submitted when hard EOF is
detected can commit before the parent generation trip; its exact signed attempt
is retained for lookup, and external effects remain a reconciliation matter.

The `reserve` and `charge` values are operator-provided allowance units, not
measured provider bills. `fn_read` is not advertised until a fixed-config
NNTP path is wired and tested. Hosted provider custody, metering, and TLS
evidence remain separate receiving work. The existing
Mini/fn two-Store evidence is in fn's `planning/evidence/two-store-join-1a9dd747-2026-09-24.md`;
this runtime does not reinterpret that synthetic acceptance as a hosted agent.
