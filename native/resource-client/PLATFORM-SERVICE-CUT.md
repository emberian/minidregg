# Supplied Store service cut

`platform-service-cut.py prepare --request INPUT --output FRESH_DIRECTORY`
creates a proposed descriptor, SYSTEM units and restricted SSH roster from the
existing constructor's runtime and journey. It creates no Store, member, grant,
unit or public binding. The input protocol is
`mini-platform-service-cut-input-v1` with absolute `runtime`, `manifest`,
`cli`, `launcher`, `authorizedKeys`, `manifestSha256`, `storeUnit` and
`ingressUnit`. Candidate manifest, CLI and launcher need root-owned ancestors
without group/other write permission. Deployed Host, Store and verifier paths
remain explicit and must hash to the candidate roles; the existing config and
workspaces remain bound to those paths. The declared roster must include every
current SSH key, so publishing a subset cannot silently remove a member.

The service owner reviews/publishes the units, proposed roster and
`mini-service-deployment-binding-v1` descriptor at one coordinated cut. The
proposal records the executable that will actually run and the source identity;
it does not relabel the currently running CLI. Root controller registration
still requires protected root executable custody independently of this descriptor.

Only after app/controller writers are quiescent and the service owner signals
the cut, execute `platform-service-cut.py stop --output PROPOSAL_DIRECTORY` as
the retained runtime's owner. It stops the exact public process group, asks the
operator's native status/drain protocol for an instance/PID/config/Host-bound
zero-work boundary, durably records that reply, then stops the exact operator
group. It does not signal SSH, apps, controllers or other deployments. Drain
refusal or timeout retains the journal and operator. Retrying uses the same
proposal and retains separate command/output evidence. The service owner then
starts the SYSTEM units and publishes the new executable/roster inventory;
normal service readiness and signed member commands qualify the resulting cut.
