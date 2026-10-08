# Operator SPK deployment

Prerequisites: systemd user manager, linger for the operator, cgroup v2 with
memory/pids/cpu delegation, unprivileged user namespaces, bubblewrap supporting
`--disable-userns`, and the distribution `uidmap` package (root-owned
`/usr/bin/newuidmap` and `newgidmap`). `/etc/subuid` and `/etc/subgid` must grant
the operator the selected range. The installer refuses missing mapping helpers
and overlapping app uids in root-installed world registries.

Build `spk-host`, `mini-spk-broker`, and `mini-spk-volume-helper`. As an explicit
root install step, run `install-user-world install SOURCE_HELPER HELPER_PATH
STORE DEPLOYMENT_HEX HOST_HEX OPERATOR_UID SUBUID_START COUNT`. The store is the
native Host's `profile.storeTag`, never a guessed config hash. This creates the
protected volume root, operator state/runtime directories, a root-owned registry
and a sudoers rule for exactly the helper binary. `visudo -cf` validates the rule
before publication. Allocate disjoint subordinate uids for every world.

Install the broker user template as `mini-spk-broker@.service` in the operator's
user unit directory, stage binaries under `~/.local/libexec`, and write an
operator-private `broker/config.json` using `mini-spk-broker.example.json`.
Start `systemctl --user enable --now mini-spk-broker@STORE.service`. Resident
units are generated user units; their sole constructor requires the store id.
The socket is operator-owned 0600 in `WORLD/runtime-STORE/broker.sock`.
The v1 root broker config and global socket are refused; re-emit v2 configs
and native grain profiles for a fresh deployment. This does not migrate a live
Store or erase uncertain lifecycle attempts.

The helper is a one-shot exec, never a daemon. Its strict JSON verbs are create,
mount, unmount, freeze, thaw, destroy and read-only volumes-status. The six volume
verbs include store/deployment, grain, exact volume path, registered namespace
uid, volume id and quota. Volumes-status includes store/deployment and the exact
volume registry root. The
root-owned registry selects all paths; a cross-world path refuses. Freeze means
one retained freeze/copy/thaw transaction, with durable repair obligations on
process loss; it never leaves a caller-controlled frozen filesystem lease.
Root checks, loop ext4, nosuid/nodev/noatime, bounded mounted /var and exact
preimage custody remain in this boundary. Each exec logs its caller uid.
Volumes-status accepts only the exact store volume root and enumerates root-owned
registrations, never operator placement hints. It reports mounted status, settled
freeze obligations and retained complete pause metadata. The broker still checks
each current incarnation and its complete settled pause before checkpoint copying.

`two-world-journey.sh full BASE_BIN OWN_RUST_BIN NEW_RUN_ROOT [SIGNED_SPK]`
uses this same installer for its separately logged ROOT SETUP/ROOT CLEANUP.
Its runtime uses sudo solely for that helper and standard uid mapping; both
brokers and residents run under uid 1001. EXIT teardown removes scratch
registries, sudoers files and the scratch helper and asserts removal. The
optional SPK input defaults to the pinned sntfy fetch cache outside src.
`custody` mode exercises only physical ext4/freeze/cross-world refusal; it is
not an SPK lifecycle qualification.
