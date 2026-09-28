# A/B event22 ticket issuer: bounded schema gate

`scripts/spk-platform/issue-agent-ticket.sh` prepares `hermes-a` or `hermes-b`
from the fixed allocation and owner-private candidate app/session birth receipts.
It requires the retained signed-SPK package and permission-schema inspections,
compares their canonical bytes to the qualified artifacts, and selects the
single source-inspected API interface. The ticket's package, interface and
schema roots and versions therefore come from the qualified SPK, rather than
the historical web-ticket example. An explicit operator policy selects a
non-obsolete signed role and records its exact permission list.
The source-current grain plan's parent task and generation must equal the
ticket's original agent origin. A changed source parent is refused before
Mini op56; `parent-generation-schema.log` records the focused schema fixture.

Host authors the request and previews current signing slots. The operator
approval pins those exact slots and protected signer keys. Mini op56/57 then
replans against current history, signs and retains the ingress; op54 submits
at most once, and op55 is the only retry/recovery path. The stage rechecks
executable, config, request, preview, signer-role, qualification and retained
birth evidence hashes before approval or sealing.

`sh -n` and ShellCheck passed. The isolated Linux schema fixture in
`/home/hbox/mini-agent-ticket-schema-r1` exercised A's full staged path and
repeated lookup, B's separate ticket/parent coordinates, and refusal of a
cross-route scope, changed accepted-session receipt, changed role permissions,
and repeat seal. Its Host/Mini are synthetic transport fixtures; these logs do
**not** claim native event22 admission or accepted r3 agent sessions. Current
r3 app/session recovery is owned separately, and this issuer must not run on
the live Store until its accepted handoff exists.
