# Operator SPK deployment

Prerequisites: systemd user manager, linger for the operator, cgroup v2 with
memory/pids/cpu delegation, a bubblewrap that can create a user namespace
(`deploy/grain-host/resolve-bwrap` names it: on a host restricting unprivileged
namespaces, the AppArmor-profiled `/usr/local/libexec/mini-grain-bwrap`), supporting
`--disable-userns` and `--userns-block-fd`, and the distribution `uidmap` package (root-owned
`/usr/bin/newuidmap` and `newgidmap`). `/etc/subuid` and `/etc/subgid` must grant
the operator the selected range. The installer refuses missing mapping helpers
and overlapping app uids in root-installed world registries.

Build `spk-host`, `mini-spk-broker`, and `mini-spk-volume-helper`. As an explicit
root install step, run `install-user-world install SOURCE_HELPER HELPER_PATH
STORE DEPLOYMENT_HEX HOST_HEX OPERATOR_UID SUBUID_START COUNT`. The store is the
native Host's `profile.storeTag`, never a guessed config hash. This creates the
protected volume root, operator state/runtime directories, a root-owned registry
and a sudoers rule for exactly the helper binary. `visudo -cf` validates the rule
before publication. `SUBUID_START` is a preference: several worlds and their controller
accounts share one operator's delegated range, so under the global allocator lock the
installer takes the first free `COUNT`-aligned range at or after it (then from the start of
the delegation), skipping every registered world, controller reservation, removed-controller
receipt and existing account; the registry and the `ROOT SETUP` line carry the range
allocated. Only a delegation with no free range refuses (`app range exhausted`).

Install the broker user template as `mini-spk-broker@.service` in the operator's
user unit directory, stage binaries under `~/.local/libexec`, and write an
operator-private `broker/config.json` using `mini-spk-broker.example.json`.
Start `systemctl --user enable --now mini-spk-broker@STORE.service`. Resident
units are generated user units; their sole constructor requires the store id.
The socket is operator-owned 0600 in `WORLD/runtime-STORE/broker.sock`
(`BROKER-RUNTIME-UPGRADE.md`). The broker refuses to run as root
(`native/spk-host/src/broker.rs:1219`) and refuses any config whose protocol is
not `mini-spk-broker-config-v3` (`broker.rs:643`); v3 requires `bwrap` and
`bwrapSha256` (`broker.rs:193-196`), because the resident namespace is
bwrap-created. A fresh deployment re-emits v3 configs and native grain
profiles; nothing here migrates a live Store or erases uncertain lifecycle
attempts.

The helper is a one-shot exec, never a daemon. Its strict JSON verbs are
`create`, `mount`, `unmount`, `freeze`, `thaw` and `destroy`
(`native/spk-host/src/volume_helper.rs:78`), each carrying store, deployment,
grain, exact volume path, registered namespace uid, volume id and quota
(`volume_helper.rs:81-92`), plus the read-only `volumes-status`
(`volume_helper.rs:206`), which accepts only the exact store volume root. The
root-owned registry (`/etc/mini-spk-volumes/STORE.json`, written by
`install-user-world`) selects all paths; a request whose path differs refuses,
and a caller whose `SUDO_UID` is not the registered operator refuses
(`volume_helper.rs:125-128`). Freeze is one retained quiesce (cgroup freeze of the
grain's resident units)/copy/thaw transaction with a durable repair obligation on process loss
(`volume_helper.rs:189-190,297-300`). Each exec logs its caller uid
(`volume_helper.rs:201,256`). The broker checks each current incarnation and its
settled pause before checkpoint copying.

`scripts/spk-platform/two-world-journey.sh full BASE_BIN OWN_RUST_BIN NEW_RUN_ROOT [SIGNED_SPK]`
uses this same installer for its separately logged ROOT SETUP/ROOT CLEANUP.
Its acceptance phase uses sudo solely for the helper and standard uid mapping;
both brokers and residents run as the operator named by `MINI_OPERATOR_UID`
(default 1001). EXIT teardown removes scratch
registries, sudoers files and the scratch helper and asserts removal.
`custody` mode exercises only physical project-quota directory/freeze/cross-world refusal; it is
not an SPK lifecycle qualification.
