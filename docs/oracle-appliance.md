# Oracle7 / veri7vn appliance

The appliance brings Oracle7's question answering and specialist tools into a
Mini grain. It combines a pinned Oracle7 slim release, reviewed source repairs,
selected veri7vn kernels, Workbench and companion providers. The source and
appliance recipes live in [veri7vn](https://github.com/emberian/veri7vn);
Mini owns package admission, isolation, agent authority and lifecycle.

The next runtime uses veri7vn's Rust `oracle-host` for both conversational
queries and direct operations. It shares the native data image, runs extracted
kernels, and contains the remaining Python Engine in bounded tenant-owned
workers. The [Rust package adapter](../deploy/oracle/rust-host-package.md) connects
that distribution to Mini's existing signed inventory, shared data and authority
bridge. It can admit the native image as an explicit package resource. This
candidate still needs signed receiving qualification; the measurements and
deployment descriptions below concern the earlier Python-based packages.

## What callers can do

Use conversational queries for supported calculations and sourced facts, or
discover a direct operation with its input schema and limits. The packaged
providers include specialist calculations, symbolic mathematics, relations,
weather, table and passage analysis, simulations, forecast checks, image
descriptors and sprite composition. Some workflows remain partial: a named
component does not imply unrestricted browser execution, external connectors,
device access or every upstream asset library.

Agents use `mini_oracle_discover` and `mini_oracle_call` on an established
application lifetime route. Discovery reports the deployed package's actual
operations and availability. Calls retain answer evidence and request identity;
an exact retry returns its retained result. Current Mini admission and purse
settlement still apply. The [agent guide](oracle-agent-tools.md) supplies the
configuration and request examples.

## Runtime, data and state

- **Signed runtime SPK:** Linux Python environment, Oracle code, selected kernels,
  providers, launcher and the Mini bridge. The new v7 package is about 97 MB compressed.
- **Shared public data:** 26 files, about 15 GB, published once by the operator.
  The runtime's signed declaration binds their inventory digest. Mini mounts the
  matching revision read-only at `/opt/oracle-data`; the app cannot choose a host
  path or another dataset. No chunking or reassembly is needed.
- **Private state:** each grain has a separate writable `/var` for conversation
  and request history. The new hosted build divides this into private workspaces
  for each authenticated source session, with separate request journals. The
  installed v5 package predates this pool and retains one workspace per grain.

Publication hashes the data; startup checks protected custody metadata. This
assumes a trusted operator and filesystem. Only deliberately published public
data is supported. A private dataset would need its own access-control design.
The [packaging guide](oracle-shared-data-packaging.md) describes the existing
contract without requiring changes to the SPK format.

## Shared hosting

The new hosted build serves many users and agents from one grain. Mini derives
the tenant identity from the authenticated principal and source session; callers
cannot select another tenant by changing a request or conversation ID. A new
source session gets a new workspace. Two agents using the very same source
session intentionally share its workspace.

The worker pool bounds resident computation independently of tenant count. The
initial class-L configuration permits one resident Oracle worker and 128
persistent workspaces. Idle workers retire before a replacement starts; busy
capacity returns a retryable refusal. Increasing concurrent workers also needs
an appropriate memory budget. Runtime files and the public dataset remain
shared and read-only, while each resident worker has separate process state.

Completed requests replay from disk without starting a worker. Oracle loses
some conversational context when its worker exits, so a new turn after eviction
requires a fresh conversation ID and supplied context. The service reports this
explicitly rather than silently answering without the earlier context.

A completed Linux run exercised arithmetic queries in 32 tenant workspaces with
one observed resident Engine worker. Peak total cgroup memory was 750,977,024 bytes (about 716 MiB)
under the 2 GiB limit. All 32 exact retries returned their retained replies;
conflicting reuse was refused. Restart replay and stale-conversation refusal
started no Engine, and both shutdowns completed. This was a runtime qualification
under shared host load, not a complete Mini receiving journey. The
[qualification report](https://github.com/emberian/veri7vn/blob/dev/project/lanes/U7-tenancy-qualification.md)
records the sampling limits and evidence.
Switching tenants still pays worker startup: first calls took 7.51–103.05 seconds
on that contended host, while exact retries took 1.22–25.98 milliseconds.

The new browser page offers questions, operation discovery and direct calls
through the same routes agents use. It retains exact request bytes for manual
retry and makes conversation resets explicit. These changes are signed in
[version 7](../deploy/oracle/runtime-v7.md), whose complete archive and signature
passed independent verification. A real Linux Engine/bridge run also passed
tenant separation and exact replay through restart. Mini receiving and the
full agent lifecycle still need qualification. Version 7 requires a fresh grain;
it refuses a legacy shared journal rather than guessing its tenant owner.
See the [bridge contract](oracle-appliance-bridge.md) for the identity boundary.

Version 7 also defers operation-catalog construction until the first discovery
or new direct call. Ordinary queries and retained replays avoid that cost;
capabilities reports unknown counts until construction succeeds. A real Engine
check passed discovery, direct calls and byte-identical retries. Observed
readiness was 10.8 seconds, with 8.4 seconds paid later on first discovery;
these are measurements under shared host load, not latency guarantees.

## Checked state — 28 October 2026

The [checkpoint and design review](oracle-appliance-review-2026-10-28.md)
separates the passing runtime checks from unfinished hosted qualification,
records the final Host-selection checks, and identifies the remaining latency
and browser usability work.

For new shared deployments, the operator can select `agentRouteProfile:
"shared-64-v1"` in the private SPK host profile. It allows 64 active controller
routes and 1,024 retained route revisions per app, with at most 64 MiB of route
history. Existing profiles default to eight active routes and 64 revisions.
The Oracle shared-data provisioner selects the shared profile; its
`ORACLE_AGENT_ROUTE_PROFILE=standard-v1` override retains the smaller budget.
Same-Store provisioning accepts the same explicit `agentRouteProfile` input.
These are controller routes, not individual queries or people in a room.
Each controller still needs its own UID, sockets, native session and grant;
the larger budget grants no additional authority and creates no extra Oracle
Engine. It is a configuration capacity, not a measured concurrency guarantee.

The earlier v4 receiving run installed and started two grains, answered through
Mini's admitted API, demonstrated independent conversation state and exact reply
replay, and completed a clean STOP and missing-data refusal. Its full recovery
journey did not pass; the [retained result](oracle-shared-data-2026-10-27.md)
records the failure and scope.

The fresh v7 qualification admitted an agent session and its persistent lifetime
grant, migrated the payer route and completed native STOP and successor START.
Its physical world was subsequently removed by unrelated cleanup while recovery
was paused. Its logical Store and admission evidence survived that cleanup; the run is
not a complete receiving result and its removed physical identity cannot resume.
A replacement qualification reached genesis. The Hermes composition passed
controller enrollment and signed readiness, but its completed model turn still
needed native receiving. The build server was then deleted with operator
approval. Agent answers, browser use and the complete restart journey remain
open; no qualification process remains on that deleted server.

The detached build volume still exists, but its contents have not been mounted
or verified after the deletion. Old remote evidence paths are historical
locations, not a guarantee of recoverable installed worlds. Earlier stopped
v5 and v7 runs have a
[recovery record](evidence/oracle-hosted-recovery-2026-10-27.json) that names their
outstanding custody and results. The lifetime-grant repair now admits the
source's owner, controller and read-only observer through a dedicated frame;
ordinary births retain their own restriction. The
[factory evidence](evidence/oracle-grant-factory-2026-10-27.json) and
[provisioning checks](evidence/oracle-provisioning-configuration-2026-10-27.md)
record the narrower validation. Provisioning uses explicit configuration,
fixed enrollment phases and the shared genesis template.
[ROWS-OWED](ROWS-OWED.md#oracle-appliance) tracks the remaining receiving work,
its owned worlds and the actual browser driver.

The same-world Hermes integration is also on `main`. Agent creation can include
a separate dispatch purse; a reusable attachment helper joins the actual
application, session and persistent grant to that controller. The isolated
controller installer now supports the worker setup, and `J14_ORACLE=1` builds
its own composed world instead of requiring a preissued route fragment.
Focused checks cover these interfaces; the composed native journey is still
being qualified. The [agent guide](oracle-agent-tools.md) explains the binding.

The veri7vn U5 v2 source composition has 351 direct operations. Its focused
57-request Engine run observed 37 completed tasks, 13 appropriate refusals or
clarifications, seven valid tasks still incomplete, and no wrong answers. It
includes conversation, geometry and transfer-time repairs beyond installed v5;
that composition is now included in signed v7 with the newer tenant adapter,
but has not yet completed the new Mini receiving journey. Versioned
operation counts are not specialist-panel scores or proof of every answer.

Repeated STOP-history inspection on a retained Store fell from roughly 425 s to
0.414 s with identical output. First inspection still pays the history walk;
see the [replay record](oracle-replay-2026-10-27.md) and
[cold-replay investigation](oracle-cold-replay-investigation-2026-10-27.md).
No result here establishes a public deployment.

## Where to continue

Use [deploy/oracle](../deploy/oracle/README.md) for preparation, signing and import;
its versioned receipts identify actual artifacts. Use the
[acceptance guide](oracle-shared-data-acceptance.md) and retained v5 evidence for
the lifecycle checks. The [market/deployment design](ORACLE-GRAIN-2026-10-27.md)
is a separate consumer of this package; its older pins are not the latest
appliance qualification. Broader upstream coverage and the remaining kernel
refresh are tracked in
[veri7vn's current checkpoint](https://github.com/emberian/veri7vn/blob/dev/project/CONTINUE-2026-10-27.md).
