# Joined platform receiving on a supplied world

`joined-member-journey.py` exercises a source-pinned deployment through existing
forced Mini-shell SSH sessions and owner adapters. It never bootstraps a second
world or copies participant/provider secrets. Existing two-member cases remain
useful component tests; the platform workload accepts arbitrary provisioned
member, group, resident and app inventories.

```sh
python3 joined-member-journey.py check /private/receiving.json
python3 joined-member-journey.py run /private/receiving.json --output /private/fresh-run
python3 joined-member-journey.py sweep /private/receiving.json --output /private/fresh-sweeps
python3 -m unittest discover -p test_joined_member_journey.py
```

`check` launches no processes. `run` and `sweep` mutate only the supplied deployment
using its authenticated participant workspaces. Output directories must be fresh.
Results retain exact commands, stdout/stderr, timings, admitted transactions,
hook requests/results and artifact hashes. Synthetic providers and scripted
users never satisfy the real-provider, mainnet or human receiving rows. Exit 2
means environmental or adapter rows remain incomplete; failed native commands
stop that run with their evidence retained.

## Inventory and selected workloads

The spec keeps `type: mini-joined-member-journey-v1`, the pinned `manifest`,
`manifestSha256`, `deployment.config`, `deployment.configSha256`, absolute
`deployment.socket`, and a fresh `prefix` of at most24 characters. The manifest
pins actual Mini/Host/Store/verifier files and their SHA256 values; every supplied
workspace must reference that same Host, configuration, Store and socket.

Use actual subject IDs as member keys. Every member contains `subject`, absolute
`workspace`, `home`, optional independent `budget`, and an SSH binding:
`identityFile`, `knownHostsFile`, `destination`, `port`. SSH uses forced Mini-shell,
strict known-host validation, no agent/forwarding and batch authentication. Each
session's `whoami` must match its workspace/home/subject/socket pins.

For example, with five already provisioned subjects1000..1004:

```json
{
  "members": {"1000": {"subject": "1000", "workspace": "/private/member-1000", "home": "/private/home-1000", "ssh": {"identityFile": "/private/ssh-1000", "knownHostsFile": "/private/known-hosts", "destination": "member-1000@localhost", "port": 2222}}},
  "rooms": {
    "engineering": {"owner": "1000", "members": ["1000", "1001", "1002"]},
    "garden": {"owner": "1003", "members": ["1003", "1004"]},
    "overlap": {"owner": "1001", "members": ["1001", "1002", "1003"]}
  },
  "residents": {"resident-task-700": {"room": "engineering", "owner": "1000", "subject": "700", "hook": {"executable": "/private/hermes-hook", "sha256": "..."}}},
  "apps": {"app-800": {"room": "engineering", "owner": "1000", "inputPath": "/private/app-attach.json", "hook": {"executable": "/private/spk-hook", "sha256": "..."}}},
  "workload": {"members": ["1000", "1001", "1002", "1003", "1004"], "concurrency": 4},
  "maxConcurrency": 16,
  "sweeps": [{"population": 2, "concurrency": 1}, {"population": 5, "concurrency": 4}, {"population": 20, "concurrency": 4}, {"population": 100, "concurrency": 16}]
}
```

This excerpt omits required pins and four repetitive member bindings; it is not a
complete executable spec. A selected population must already exist in the member
inventory. Sweeps run only the explicitly selected population/concurrency pairs,
never a Cartesian expansion. A sweep with no supplied rooms creates a shared
group and, once population permits, overlapping and disjoint groups. With supplied
rooms it selects applicable groups, requiring every selected member to participate.
Concurrency is bounded by the operator's `maxConcurrency` (default16), at most64.
One workspace has at most one write in flight per group.

Room keys identify workload groups before creation. Once the room resolves, hook
`rooms` is keyed by actual room cell ID; memberInventory is keyed by actual subject
ID. Duplicate display names are supported for separate owners: invitations import
under distinct receiver-local aliases, exported as `memberRoomNames`. An alias is
never used as shared deployment identity. The current central room schema exposes
499 historical non-founder roster slots (500 including founder); rejoining the
same subject reuses its history. The harness checks that exact schema boundary,
while separate rooms can contain a larger global population. It does not imply a
500-user platform ceiling.

## Same-Store hook contract

Adapters are executable files with SHA256 pins and optional string `args`; they
receive `--request PATH --result PATH`. Shared adapters live under `hooks` with
roles `paid-entry`, `hermes`, `spk`, `restart`, `growth`, `group-boundary`. Resident
and app inventory rows can override their own `hook`; several instances in a room
are each invoked. No missing adapter becomes a pass.

The request retains `type: mini-joined-member-hook-request-v1` and includes:

- exact deployment `identity`, `manifest`, `deployment`, all selected `members`;
- actual-ID `memberInventory` and `rooms`, plus supplied `residents` and `apps`;
- selected `workload`, scoped `roomKey`, `room`, `roomTarget`, `documentTarget`;
- `owner`, `memberKeys`, `memberRoomNames`, and `subjects` mapping inventory keys
  to the exact actual subjects for this group;
- `role`, `phase`, `instanceId`, `instance`, `evidenceDirectory`.

A result has `type: mini-joined-member-hook-result-v1`, unchanged `identity`, exact
`role`/`phase`, `status: pass`, and nonempty `artifacts: [{path,sha256}]`. Hermes/SPK
must also return exact `roomTarget`, the exact `subjects` **mapping**, and, for a
configured instance, the matching `instanceId`. Ordered two-member arrays are
not this generalized contract.

Hermes reports `delivered` and `providerMode`; a synthetic delivery is useful
source receiving but leaves the real-provider row pending. SPK before-restart
returns `appId`, `writeRead`, `shared`; after-restart returns the same `appId` and
`retainedData`. Attach input must use the supplied native config, public/private
sockets and already provisioned identities/capabilities. It cannot initialize or
copy a sibling Store. Restart restarts the controlled current deployment and
retains its exact identity. Growth measures1000 admitted records, write<=5s,
**cold** reopen<=60s. Group-boundary uses the supplied actual document cell and
`boundaryActor`; it returns `refusedSubject` and `refused`, proving an uninvited
subject's native refusal without importing a grant. Paid-entry returns the actual
rail and `creditedSubjects` mapping; a synthetic rail leaves mainnet pending.

Each group performs native invite/publish/import, resolves one shared document,
submits concurrent distinct-member writes, reads every effect, checks missing
control authority, transcludes and inspects source law. After controlled restart
it compares exact transaction IDs and single effects; shared apps must retain
data. It kicks and rejoins an actual member, checking other-member progress and
retained data. A separate sacrificial document checks owner lockout under an
unsatisfiable law. Adapter evidence must additionally cover independent budgets,
held/disconnected resident/app fairness and native admission boundaries; scheduler
component tests cover principal sharing and durable uncertain holds.

The harness is orchestration, not a theorem or capacity certification. Retain
human sessions privately and keep environmental outstanding rows visible.

For a root service composition, `deployment.binding` is `{path,sha256}` for the
single `mini-service-deployment-binding-v1` descriptor. The descriptor and its
ancestors must be root owned with no group/other write permission. Its
`deployment.config` and `deployment.manifest` `{path,sha256}` fields must match
the journey; `deployment.rolePaths` declares the actual `host`, `store`, and
`verifier` paths, whose bytes must equal the immutable candidate role hashes.
This permits an explicitly declared deployed path for an identical native role.
The configuration and member workspaces must still reference those exact paths.

The descriptor separately records actual `deployment.cli: {path,sha256}` and
`deployment.memberCommands` rows with `subject`, `launcher`, `mini`, `host`,
`authorizedKeys`, and `publicKey`. All fields except `subject` and `host` use
`{path,sha256}`. Each member's actual restricted SSH command must invoke exactly
the declared launcher, CLI, Host, config, socket, workspace, and home. Its SSH
public key must match the inventory identity file. The actual CLI bytes must
equal the selected candidate Mini bytes: changing a manifest cannot relabel an
older executable. Upgrade wrappers explicitly during a coordinated service cut.
Without a binding, the original exact manifest-path requirements still apply.

The authorized-keys hash is the current receiving snapshot. Regenerate the
descriptor and journey binding pin after enrollment or a roster lifecycle
change, before resuming receiving. The harness checks this observation on every
operation; it does not change the root service loader's roster lifecycle policy.
