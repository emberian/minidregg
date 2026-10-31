# A separate controller account for one test world

The normal world installer can provision one controller per registered Store.
This is explicit operator setup, not Mini admission. A controller gets its own
named UID, private group, home and four role keys. The UID and GID come from
the intersection of the operator's existing subordinate delegations. It does not receive Store
files, the Store operator's keys, or the primary private operator socket.

Run these verbs through the same authorized `install-user-world` entrypoint:

```text
controller-create STORE HELPER
controller-resume-create STORE HELPER
controller-stage STORE HELPER BUNDLE BIN_DIR UPSTREAM_PRIVATE_SOCKET PUBLIC_SOCKET
controller-start STORE HELPER
controller-stop STORE HELPER
controller-config STORE HELPER NEW_CONFIG_OR_BUNDLE
controller-tool STORE HELPER REQUEST_ID TOOL ARGUMENTS_JSON
controller-tool-result STORE HELPER REQUEST_ID
controller-tool-ack STORE HELPER REQUEST_ID
controller-journal STORE HELPER
controller-status STORE HELPER
controller-service-logs STORE HELPER
controller-consent-storage STORE HELPER
controller-runtime-upgrade STORE HELPER OPERATOR_BINARY
controller-mini-upgrade STORE HELPER OPERATOR_BINARY
controller-consent-memory STORE HELPER MIB
controller-status-proxy-upgrade STORE HELPER OPERATOR_MINI
controller-worker-runtime-access STORE HELPER
controller-worker-observe STORE HELPER
controller-reconcile STORE HELPER worker-audited
controller-reconcile STORE HELPER parent-audited
controller-reconcile-prompt STORE HELPER PROMPT_OPERATION_ID
controller-enroll STORE HELPER REQUEST_FILE
controller-export STORE HELPER
controller-reserve-export STORE HELPER DISPATCH_ATTEMPT_ID
controller-remove STORE HELPER
```

`controller-create` returns `controllerHome`, `controllerUid`, `listenerSocket`,
`reverseSocket`, `operatorSocket` and `operatorPeerUid`, along with the allocated
account, group, unit names and home inode. Account names are fixed to
`mini-c-STORE`. The installer selects one unused UID/GID from the operator's
existing `/etc/subuid` and `/etc/subgid` intersection; it grants no new range.
It creates the private group with that exact GID before creating the named
account with both explicit IDs. Account creation uses `useradd --system` without
`--add-subids-for-system`, so it grants no subordinate ranges. Before creation,
the installer checks the bounded `useradd -D` output requires
`CREATE_MAIL_SPOOL=no` and no implicit supplementary groups. It does not change
host defaults or pass defaults-file settings as unsupported `-K` login.defs
keys. Existing accounts/groups, app ranges,
controller reservations, other principals' overlapping delegations and a
different calling operator refuse. Numeric subid-owner aliases are supported.
A controller name or numeric UID with its own stale subordinate grants also
refuses: the new controller must not inherit authority to map the operator.

A permanent root-owned reservation is written under
`/etc/mini-spk-controller-reservations/STORE.json` **before** either account or
group creation. Pending setup, failure, controller removal and world removal
never release that identity. Both future app allocation and controller
allocation enforce these reservations and retained removal receipts under the
same global installation lock. Malformed or unsafe registry data fails closed.
The installer bounds registry counts, delegation input, candidate enumeration
and NSS snapshots rather than silently truncating a range.

`controller-resume-create` handles the specific interruption after the permanent
reservation and private group were created, but before the account exists. It
requires the exact root-owned `pending.json` and lifecycle lock as the entire
controller directory; matching world/deployment/operator reservation; the
reserved group name/GID with no members or aliases; no passwd entry, UID/GID
use, live identity process or controller unit; and still-exclusive subordinate
delegation. It then creates the account with the **same recorded identity** and
finishes normal setup. It never allocates again, deletes partial state, adopts
an existing account or accepts partially populated home/configuration files.
The original pending record and permanent reservation remain. Recovery after a
later creation step is outside this narrow verb and fails closed.

The provisioning operator is explicitly trusted: it generates the controller's
keys, supplies its code/configuration and already owns the delegated ID range.
It can create a separate user namespace and assume this subordinate controller
identity. This design protects Store/operator resources **from** the controller
and app; it does not protect controller custody from its provisioning operator.
Other users' overlapping subordinate ranges are excluded. The controller gets
no subordinate grants of its own.

The home is `WORLD/controller/home`, mode 0700. The forward app listener lives
outside it, in an operator-owned 0700 directory. The reverse custody listener
also lives outside the home, in a controller-owned 0711 directory: the current
runtime requires searchable ancestors and installs an operator-specific ACL on
the socket itself. Neither directory grants another account write access.

Stage only this explicit bundle, with no additional files or symlinks:

- `controller.json`, `host-config.json`;
- `custody/controller.key`, `tool.key`, `dispatch.key`, `provider.key` (32 bytes each);
- `state/shared-app-refs/app-birth.bin` and `bootstrap-ticket.bin`;
- optionally `state/shared-app-refs/agent-ticket.bin` and the four files
  `state/oracle-grant/{seal.json,call.bin,submit-marker.json,receipt.json}`.

`BIN_DIR` supplies `grain-runtime`, `mini`, `minidregg-host` and the source-matched
`minidregg-client-consent` for new version-2 allocations. All source files
must belong to the registered operator, be regular single-link files under
protected, non-symlink ancestors, and have no set-ID bits, writable group/other
bits or file capabilities. Each binary is bounded to 256 MiB. Configurations are
bounded to 512 KiB/1 MiB and each accepted-source file to 1 MiB. The installer
records exact hashes and copies binaries under root custody. Supplied binaries
never run as root. Empty `workspace` and the named state/custody directories are
allowed; arbitrary bundle directories are not.

The completed root setup also writes a small 0644 `WORLD/controller/namespace.json`.
Before parsing resident JSON, native bootstrap checks its root custody, exact
world/deployment/host/operator binding and named passwd/private-group identity.
It maps exactly the registered operator, app and controller single IDs through
`newuidmap`/`newgidmap`. A world without a controller keeps its original two-ID
map. A partial allocation without its completed receipt refuses; caller-supplied
controller numbers do not select namespace mappings. The app and resident still
drop all capabilities, supplementary groups and identity-switch privileges.
Forward and reverse peer checks compare the real mapped controller UID; root
ancestors use retained inode provenance, never a numeric overflow UID.

An already validated immutable receipt is a namespace snapshot. Removal racing
that read need not prevent the reader finishing its map, and running residents
retain their existing mappings. Permanent nonreuse prevents those mappings from
aliasing a later app/controller. This is not linearizable START-versus-remove,
not a controller-liveness check and not source-grant revocation. A later fresh
START with agent routes but no registered controller refuses before BEGIN.

The runtime system unit runs as the controller, with no supplemental groups,
no new privileges, a private temporary directory, a read-only system view and
writes limited to its home and reverse-socket directory. The operator proxy
runs as the Store operator. Both have a 2 GiB memory ceiling, no swap, one CPU,
128 tasks and a three-hour lifetime. Unit names and executable arguments are
fixed by the installer; substituted or already-loaded units refuse.

The activated operator socket is inside `HOME/operator`, controller-owned
0700/0600. Systemd creates the listener as root, so its measured connection peer
is **UID 0**, even though the proxy service runs as the Store operator.
`dispatchTask.operatorPeerUid` pins 0 separately from the application host UID.
See [the proxy contract](../../docs/oracle-controller-operator-proxy.md).
The public Host socket gets only a dedicated controller connect ACL and the
necessary ancestor traversal ACLs. Existing extended ACLs refuse rather than
having their masks widened. The primary private listener and Store files stay
unchanged. ACL intent and completion receipts retain exact inode identities.

New allocations also have a separate full consent service. Its activated socket
is `HOME/consent/peer.sock`, under a controller-owned 0700 directory with mode
0600. The service runs as the Store operator; the systemd-created listener's
peer UID remains 0. It runs only the root-copied `mini serve-controller-consent`
with a fixed provider, exact provider/configuration SHA-256 pins, controller UID
and `WORLD/controller/consent/anchors`. The service configuration is an
operator-owned 0600 copy of the exact `HOME/host-config.json` bytes. The
controller gets no Store/verifier/key access through this setup.

The runtime and fixed helper children select that service explicitly using
`MINI_CONSENT_SOCKET`, `MINI_CONSENT_PEER_UID`, `MINI_CONSENT_SHA256` and
`MINI_CONSENT_CONFIG_SHA256`, alongside the existing fixed `MINI_LOCAL_HOST`,
`MINI_CONSENT_HOST` and `MINI_CONSENT_CONFIG` selections. The ordinary runtime's
mini subprocesses inherit these values. Native consent retains this selection
in its per-attempt pins; the transport checks the exact config/provider binding
and controller peer, with no local or thin fallback. A controller config update
keeps the fixed host-config path; it does not change the service settings.

The consent service keeps `ProtectSystem=strict`, with two write exceptions:
its own operator-private consent anchor directory and the exact private parent
of the configured `storageRoot`. The existing SQLite helper opens the database
read/write, takes a write-capable lock, and may atomically replace the sibling
`storageRoot.head-anchor`; the parent must therefore permit creation and rename.
This grants the trusted operator-side provider write access to that **entire
private parent**, including other entries there, not just SQLite or the anchor.
It grants the controller no filesystem access. The provider/configuration remain
exactly pinned, and native Lean consent remains the authority for requests.

Setup requires a canonical path with no symlink ancestors, a real operator-owned
0700 Store and parent, and private regular single-link database/anchor/lock
files. It pins ancestor/Store directory identities and persistent database/lock
inodes. Each use revalidates owners, modes and those identities. The source
helper legitimately replaces a well-formed private `MINIANC2` anchor, so its
inode may change; its private parent and current file custody/format are checked
and the native helper still checks its continuity. The writable path comes only
from the exact pinned host configuration, with control characters, aliases and
systemd specifiers refused. The verifier may use its private temporary directory. Stop/start and controller configuration
updates preserve the `binding`, `frontier` and `lock` files. Missing/corrupt
retained state is a native refusal, not permission to replay from an empty
frontier. Removal first copies these exact bounded files, including an
incomplete initialization, to a root-private
`/var/lib/mini-spk-controller-history/STORE-consent` archive and records their
hashes. A changed archive refuses removal.

Existing version-2 stages need the explicit `controller-consent-storage` verb
while all recorded units are inactive, both manager PIDs are zero and no
controller process remains. It derives the Store path from the unchanged pinned
configuration and changes only the consent unit's `ReadWritePaths` plus the
stage's filesystem pins. Exact old/new unit and stage bytes and an immutable
intent are retained under root custody. Interruptions after any archive,
intent, unit, stage or manager-reload step can resume only those same byte
states; unrelated edits or changed Store identities refuse. No restart, source
request or config rewrite occurs. New stages include these checks directly.

`controller-runtime-upgrade` changes only the stopped controller's root-pinned
`grain-runtime`, its matching private home copy, and the stage's runtime hash.
The source is an operator-owned bounded regular executable with the same custody
checks as initial staging. All five units must be inactive, with no manager or
controller process. Exact prior/new binary and stage bytes remain in root-private
hash archives. An immutable intent permits interrupted root-copy, home-copy and
stage publication to finish only from those exact old/new states. Recoverable
archives and intents are first written to private staging files; a short write
can resume only from the exact prefix of the already-bound expected bytes.
File and directory sync precede publication. Conflicting final/staged bytes
remain preserved and refuse. It preserves
identity, configuration, journal, keys, other binaries and unit definitions.
This installs explicitly selected operator code; a matching source/qualified
native build remains a separate deployment obligation.

`controller-status` produces a stopped-state proof: all controller units and
the registered public listener must be stopped. Capture it before restarting
the world's public services. It refuses a running listener even when the
controller itself is stopped; use `controller-service-logs` for service
diagnostics instead of treating this proof command as a live health check.

`controller-mini-upgrade` applies the same stopped, archived replacement to
the controller's Mini executable and private home copy. The separate
`controller-status-proxy-upgrade` selects an auxiliary pinned Mini for the
worker status proxy: its second activated socket accepts status reads while
the ordinary public socket keeps its existing role. `controller-consent-memory`
sets only the stopped consent service's memory ceiling, in 256 MiB increments
from 256 to 16384 MiB. These operations retain exact old/new stage and unit
or executable bytes; they preserve native history and do not restart services.

Worker controllers need their own user manager to launch sandboxed workers.
`controller-worker-runtime-access` exposes only `/run/user/UID` in the service's
private home/runtime view. `controller-worker-observe` derives the exact worker
unit from the retained journal and reports the manager's observed state and
the unchanged journal hash. Observation alone does not settle a reservation.

After the native worker, parent settlement and external-effects audits have
closed every retained obligation, `controller-reconcile-prompt` can close the
exact failed resident prompt without replaying it. It preserves the original
undecided record and writes a separate resolution binding that record, the
native audit chain and the original reserve evidence. The result means there
is no deliverable answer; it does not assert that no effects occurred. A missing
or unrelated audit refuses. The resident then consumes that terminal result
through its normal recovery path before selecting another request.

After `controller-config` installs and retains a target configuration,
`controller-enroll` runs only the native
`grain-runtime application-enroll stopped HOME/controller.json REQUEST` as the
controller. Its operator-owned 0600 request is at most 8192 bytes, with the
native protocol, `bootstrap-dispatch` or `application` mode, expected current
binding hash and target raw configuration hash. The installer checks the target
against the exact installed config and root-retained revision, then copies the
request to an immutable SHA-named private `HOME/enroll-requests` file. Native
code checks source authority and publication; the installer does not edit the
journal or synthesize enrollment.

The runtime stays stopped. The wrapper checks and starts only the exact consent
socket/service and operator proxy socket needed for source reads and restores
helpers previously inactive afterward, including after refusal. Previously
active helpers remain active. It holds the exclusive per-controller lifecycle
lock across the child, while releasing the global allocator lock. There is one
1800-second child execution with bounded output and owned-process cleanup; no
automatic retry. Native output and exit status pass through. A helper cleanup
failure is an additional transport failure, not evidence that native enrollment
was undone. The retained request/native record supports an explicit identical
request recovery when the native command permits it. A nonzero native exit can
occur after a journal rename failure and therefore does not prove the
binding stayed unchanged. Failed or successful binding transitions are never
rolled back by the installer.

Stage returns the consent service/socket/provider/config/identity and storage pins. Start
adds its observed systemd invocation, MainPID, process start ticks, exact
executable inode and socket owner/mode. This is labeled **process and socket
readiness only**; independent source admission is established by the actual
native request, not by systemctl or an invented health response. Version-1
allocations retain their original three units and three binaries for supported
stop/export/removal; setup does not silently retrofit an old failed attempt.

Stage the initial configuration, start the controller, and earn the session
birth through `mini_create_application_session`. After the real event22/event27
receipts exist, prepare and register the source-bound app route, and obtain the
actual host unit from `grain start`. Stop the controller before installing its
final configuration with that unit. `controller-config` accepts either one
configuration file or a bundle containing `controller.json` and the optional
final grant files above. Existing grant bytes are immutable; only byte-equal
copies are accepted. Every configuration revision is retained by hash. Configuration publication
also retains the exact previous/target hashes and grant-file hashes in an
immutable intent. It accepts only that old or new current config on recovery;
an already-current target is idempotent, while a historical noncurrent revision
without a matching publication intent refuses. The renamed config's home
directory is synced before success, so subsequent native journal enrollment
cannot rely on an acknowledged but unsynced config rename. Restart uses the
existing native journal, not a fabricated birth record.

Tool IDs are exactly 32 lowercase hexadecimal characters. The four supported
tools are `mini_create_application_session`, `mini_oracle_discover`,
`mini_oracle_call` and `mini_grain_status`. Arguments are bounded to 256 KiB and
copied to a new controller-owned 0600 regular file **after dropping privilege**.
An existing request ID refuses. A per-controller shared lock spans the command
and its exact reap; stop, configuration replacement and removal need the
exclusive lock, so cleanup cannot race a new command after a process census. Tool-result and acknowledgement use the same
fixed runtime and native control socket. A call has a 20-minute deadline and
16 MiB combined output bound; failure after sending still requires exact
request recovery, never an automatic resend. No general command runner exists.

`controller-service-logs` returns private bounded system journals for only the
fixed service units in the checked root receipt/stage. It validates the actual
manager unit, owner and fragment, selects its observed invocation when present,
and otherwise labels the result as recent history for that fixed unit. Each
service is limited to 256 records, 1 MiB of output and 20 seconds. Exact bytes are
returned as base64 with hashes, never interpreted as commands or admission.
Callers cannot supply a unit, invocation, path or journal expression. The
read-only verb uses the shared lifecycle lock and is useful after a failed
startup when the controller's private state journal cannot explain systemd
stderr. Save its output as private evidence, not public chat/log prose.

`controller-journal` returns only the native controller journal. `controller-export`
returns bounded state evidence (at most 512 regular files / 32 MiB, with hashes
and base64 bytes), excluding the separate custody directory and its keys.
For a successful call's authority probe, prefer `controller-reserve-export`:
a canonical decimal u64 selects exactly
`state/agent-lifetime-reserve-{ID padded to 16 decimal digits}/` and its eight
`source.json`, `pin.json`, `request.bin`, `plan.bin`, `plan.frame`, `call.bin`,
`receipt.json`, `submit-marker.json` files. It keeps the same evidence protocol,
hashes and base64 encoding, with 32 MiB total and 12,102,760 bytes per file.
It cannot select another directory or export keys. This avoids making an
increasingly large full-state export a prerequisite for a later successful call.
These exports contain controller activity and should remain private evidence.

Stop/remove validate the recorded account, home inode, unit files, binaries and
manager unit identity. Removal refuses unrelated live processes, mounted
subtrees, replaced ACL objects or changed ACLs. It removes only this account and
its recorded units, then retains a cleanup receipt under
`/var/lib/mini-spk-controller-history`. Ordinary world removal refuses while a
controller allocation remains. Interrupted setup retains its pending records;
an incomplete ACL mutation or account allocation outside the exact supported
pending-create shape needs operator repair, not an ownership guess or destructive retry.

The unprivileged tests are:

```sh
python3 -B deploy/spk-host/tests/test_controller_world.py
```

They exercise source-file custody, links, bounds, capability refusal, private
immutable copying, fixed unit users, request-ID reuse, actual Linux ACL grant/
restore, delegated-range intersection, foreign/NSS/stale-grant exclusions,
permanent and pending reservations, failure before account creation, and the
exact reserve evidence export, full-consent service pins, both configuration
copies, legacy layout compatibility, and retained partial anchor state. Actual account/systemd setup and the complete source-admitted tool
journey remain separate receiving tests.

The entrypoint executes only its SHA-256-pinned Python companion bytes, read once
through a bounded (96 KiB) no-follow descriptor. Deploy both files together. The existing
operator-writable source entrypoint remains explicitly trusted root setup; this
pin prevents ambient sibling substitution and read/execute races, rather than
pretending to isolate root from an operator authorized to replace that entrypoint.

`controller-status STORE HELPER` observes a stopped controller without starting
it. It validates the registered units, both runtime copies, retained controller
configuration and consent settings, then returns `stageSha256`,
`runtimeSha256`, `controllerConfigSha256`, the exact stage `consent` object,
`stopped: true` and `stoppedUnits`. If a public listener is registered, that
listener must also be stopped; the result includes its verified registration.
This is an observation under the installer lock, not a promise that another
operator process will never start a service afterward.

`controller-public-listener STORE HELPER OPERATOR_BINARY` registers the qualified
public-proxy Mini independently of the controller's Mini and runtime. Stop the
controller and its helper units, then stop the participant public proxy and
wait for its owned socket to disappear. Registration holds the same native
`host.lock` flock, verifies the original root-recorded ancestor ACLs, and
requires an absent public socket. It retains the original socket identity as
history; it never adopts a replacement socket. The exact input binary is copied
to root-owned `controller/public-listener/mini` with mode 0555. The immutable
registration selects the controller UID and precreates the operator-private
`host.controller` pin (`MINI-PUBLIC-CONTROLLER/v1`, decimal UID, final newline).
A bounded interrupted copy can be resumed only with the same exact input.

Use the returned `publicListener.binary`, `socket` and `controllerUid` to run
`mini serve-public-proxy --socket SOCKET --upstream PRIVATE_SOCKET --config CONFIG
--controller-uid UID`. The qualified native listener validates the execute-only
controller ACL on its parent and recreates the write-only socket ACL on every
bind. It retains the public envelope filter; its private upstream and Store gain
no controller ACL. Existing private startup remains the default when no
controller has been explicitly pinned. The controller's client binaries and
source-admission state do not change when its public listener is upgraded.

For a registered listener, controller removal requires that public service to
be stopped and its socket absent. Under the same native lock, removal validates
the exact registration, binary, UID pin, ancestor inodes and ACLs; it restores
only recorded ancestor ACLs and removes only the exact UID pin. The old socket
receipt and new listener registration remain in the root cleanup history.
A changed pin, replaced ancestor, unexpected socket or interrupted ACL teardown
fails closed and retains the remaining records for operator repair. The public
service's mode/config/lock files are retained. It can return to ordinary private
startup after successful controller teardown; removal is not a live listener
reconfiguration operation.
