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

For a fresh root-custodied service frame, the service owner may prepare an empty
0700 directory owned by the Store operator beneath the immutable frame. Set
`preparedEmptyRoot: true` to accept that directory; the constructor refuses any
contents, symlink, other owner, or broader mode. It rechecks before its first
publication. `nodeDirectory: "node"` places the single native Node there instead
of the default `world`. The retained runtime records its actual `nodeRoot`, and
the service descriptor consumes that path. This mutable Store subtree does not
provide authority for the root-owned candidate or controller registration.
An optional `sshLauncher: {path,sha256}` selects the staged immutable SSH wrapper.
Its bytes must match the source recipe exactly and its entire canonical ancestry
must be root-owned and unwritable by other users. Forced commands record that
actual executable path; selecting a candidate never relabels a different wrapper.

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

The copied hook bundle pins executable source under `ROOT/hooks`, so later worktree
edits cannot invalidate a live restart hook. The native group-boundary adapter
imports an owner's real document capability ID as an outsider's local discovery
hint and requires a definitive native refusal signed by that outsider; it does
not grant authority or move seeds.

Resident and SPK adapters must attach to the emitted same-Store
inventory; they are explicit missing journey hooks until configured. The growth
bar also remains an explicit adapter until its 1000 accepted records and measured
write/reopen bounds run on this same deployment. For SPK,
`scripts/spk-platform/same-store-profile.py` initializes the SPK image on these
same sockets/config, and `same-store-hook.py` consumes its retained profile and
actual room/namespace authority. Creator/payer8 can sponsor an application owned
by an actual enrolled room founder. No second Store or copied member secret is
an admissible substitute. Synthetic provider and fixture-member checks leave
real-provider and human-transcript rows pending.

The contract tests launch no native Mini calls; the Linux process case only checks
owned process signalling. Actual receiving evidence must come from `start` and a
joined run against the supplied candidate family.

For paid construction, selected member rows set `entry: "paid"` and optional
positive `weeks` (default2); `funding` becomes their requested starter credit.
The plan supplies `paidEntryAdapter: {path,sha256}` and a separate `payObserver`
allocation with canonical positive Nat256 strings: `subject`, `keyId`,
`account`, `spendCapability`, `controlCapability`, `factoryObserveCapability`,
`capability`, `payControlCapability`, and `enrolCapability`. These allocations
must be distinct and cannot collide with the provisioner's operator resources.

The sole genesis enrolls that observer with its own native signing key and
account before bootstrap. The observer is separate from the factory controller:
its source confinement must not restrict the operator's room/grain authority.
The retained paid adapter then performs native v2 quote/deposit/watch/wait on
the supplied config/sockets/Store and returns actual identity-derived subjects,
workspace paths, current/NEXT keys, and SSH keys. The constructor uses those
exact workspaces and keys for forced SSH; it does not sponsor-enroll or fund a
second identity for a paid member. Ordinary `entry: "sponsored"` remains the
default and can coexist in the declared population.

The immutable paid result identity must equal the final journey identity; its
retained adapter becomes the supplied `paid-entry` hook. Synthetic RPC receiving
proves the source payment/entry path and leaves mainnet pending. It does not
provide external chain evidence. Preserve a partially completed paid root and
its exact status/receipts after failure; create a fresh root for a new rehearsal.
