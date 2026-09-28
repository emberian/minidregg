# A/B event22 ticket issuer: bounded schema gate

`scripts/spk-platform/issue-agent-ticket.sh` prepares `hermes-a` or `hermes-b`
from the fixed allocation and owner-private candidate app/session birth receipts.
It requires the retained signed-SPK package and permission-schema inspections,
compares their canonical bytes to the qualified artifacts, and selects the
single source-inspected API interface. The ticket's package, interface and
schema roots and versions therefore come from the qualified SPK, rather than
the historical web-ticket example. An explicit operator policy selects a
non-obsolete signed role and records its exact permission list.
The grain plan's parent is the issuer's reserved grain witness and can differ
from the ticket recipient's agent origin. `Kernel/ApplicationShareIssueSource`
and `Kernel/ApplicationShareIssueGrainAdmission` do not equate the two;
`GrainResourceBirthController.SourceShape` checks the grain parent's reserved
state independently. The issuer now compares the source plan's parent
task/capability/observe selector to the exact request and operator policy,
while comparing the ticket origin task/generation to the allocated agent and
staged scope. The older `parent-generation-schema.log` exercised a stricter
shell comparison that was removed; it is historical, not the current rule.
`independent-parent-schema.log` covers issuer parent7901 generation1 with
ticket recipient7920 origin generation0, and refuses an altered plan origin.
That test uses a schema-shaped Host mock; source admission and enrollment
remain separate requirements.

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
r3 app/session births are accepted, but the descriptors remain unenrolled;
this issuer must not run on the live Store until the authorized enrollment and
historical origin sequence is fixed and the INSTALL writer hands off.
