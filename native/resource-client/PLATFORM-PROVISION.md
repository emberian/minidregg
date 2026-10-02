# Fresh joined platform provisioning

`platform-provision.py` creates one fresh private Store using the canonical workroom
bootstrap, then enrolls independently generated member keys on that Store. The
fixed operator roles 7/8 sponsor native births and lifecycle custody; they do not
limit the member population. Members have actual allocated subject IDs, their own
funded account, workspace, session home, and an SSH key restricted to that exact
Mini session. Only the birth context crosses from sponsor to member home.

Run on the designated Linux build/deployment host as the unprivileged operator.
`check PLAN` validates pins and allocation/group bounds and launches nothing.
`start PLAN` requires a fresh root, an unused loopback SSH port, native binaries
from a pinned manifest, and source recipes that support policy before genesis.
It leaves all prior roots intact. Logs, seeds and authorized keys are private.

Example plan (paths and SHA must refer to the supplied candidate family):

```json
{
  "type": "mini-platform-provision-v1",
  "root": "/home/ember/build/receiving/platform-r1",
  "sourceRepo": "/home/ember/build/mini-datamodel-20260930/c-c2/src",
  "manifest": "/home/ember/build/candidate/manifest.json",
  "manifestSha256": "REPLACE",
  "sshPort": 19201,
  "members": [{"name":"member-0"},{"name":"member-1"},{"name":"member-2"},
              {"name":"member-3"},{"name":"member-4"}],
  "rooms": {
    "shared": {"owner":"member-0","members":["member-0","member-1","member-2","member-3","member-4"]},
    "overlap": {"owner":"member-1","members":["member-0","member-1","member-2"]},
    "other": {"owner":"member-3","members":["member-3","member-4"]}
  },
  "sweeps": [{"population":2,"concurrency":1},{"population":5,"concurrency":4}]
}
```

The default sponsor balance covers the declared population, and each member
receives 1000 units. `sponsorBalance`, `toolBalance`, `parentBudget`, `toolBudget`,
`parentTask`, `toolTask`, `maxMembers`, `maxConcurrency` and per-member `funding`
are explicit operator allocations. They are bounded receiving inputs, not product
capacity promises. The optional `operatorPolicy` accepts grain tariff,
provider-services and evaluator policy; lifecycle management and completion
custody are generated before the first profile/genesis. The default grain tariff
is base2/perBirth1, shared by the initial native birth.

Outputs are `journey.json` keyed by actual subjects, `platform-inputs.json` with
same-Store sockets, native authority, custody paths and actual member inventory,
and retained `runtime.json`/`source-pins.json`. `joined-member-journey.py check`
validates the emitted inventory. Its restart hook stops only owned Store services,
reopens the same configuration and verifies a source signed observation; the hook
retains an immutable restart artifact. `stop --state ROOT/runtime.json` stops the
owned SSH and Store process groups without deleting roots. Process identity uses
kernel start time, uid and executable inode, since sshd updates its argv title.

Resident, SPK and group-boundary adapters must attach to the emitted same-Store
inventory; they are explicit missing journey hooks until configured. For SPK,
`scripts/spk-platform/same-store-profile.py` initializes the SPK image on these
same sockets/config, and `same-store-hook.py` consumes its retained profile and
actual room/namespace authority. Creator/payer8 can sponsor an application owned
by an actual enrolled room founder. No second Store or copied member secret is
an admissible substitute. Synthetic provider and fixture-member checks leave
real-provider and human-transcript rows pending.

The contract tests launch no native Mini calls; the Linux process case only checks
owned process signalling. Actual receiving evidence must come from `start` and a
joined run against the supplied candidate family.
