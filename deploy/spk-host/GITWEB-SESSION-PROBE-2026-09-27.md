# Copied-volume GitWeb session component probe — 2026-09-27

This persvati test exercised the physical fd 3 RPC driver against the signed
GitWeb SPK. It used **synthetic session projections**, not Mini admission or a
source-owned current session claim. No public listener, Mini Store, paid
provider, or live 780x/9301/fn service was involved. It is a component test
for session lifetime and permission attenuation; the endpoint still refuses
unauthorized dispatch.

The signed SPK SHA-256 was
`2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa`.
The earlier qualified resource 991003 volume was quiescent and retained commit
`27c7e7dbe3c66cc5d8381748d0b0e5fbae05bafc`. We created **separate**
resource 991013 with the reviewed `spk-var-volume` helper SHA-256
`e8e822235919da7c0f3972c156d59c337a00debdb1ad0485da2524ad7604ab5d`,
copied the quiescent mounted data as root, and verified that both branch tips
equaled that commit before and after the run. The new backing file remains
root-owned 0600, 512 MiB, and the ext4 mount remains available for inspection.
Resource 991003 was not launched or written.

The tested `rpc_adapter.rs` SHA-256 was
`d68620cca1abe0adcba5d672a53c18bf6916a8021bb6cb3cf4fc4911587ce36f`;
the new `gitweb-session-smoke.rs` SHA-256 was
`d4e61905b06823af4d5aca9b533596b1d27ab636ccb9c705149ba0094b5edd29`.
The crate `Cargo.toml` and `Cargo.lock` SHA-256 values were respectively
`9836ec6e65de368d5262d5c760f751d4e1b0baacf2f97e62dd33cb680ea43861`
and `2fd7f108d990e53b743a332cf2f94e1a6131a1ac1618232aaa949877e577bf26`.
A bounded two-job Linux release build and strict Clippy passed. The exact
root-owned tested ELF at
`/opt/minidregg-gitweb-session-20260927/bin/gitweb-session-smoke`
had SHA-256 `22c98fb674857b8dcf7eee164dd3287bce460297200dc132e071c3fc3505d523`.
The focused RPC driver tests had passed 3/3 on the same adapter source before
the final harness-only change; the final harness was release-built and
Clippy-checked, not separately covered by Nextest.

One stopped-by-default transient unit
`mini-spk-gitweb-session-991013-final.service` ran under locked UID 995 with
`NoNewPrivileges=yes`, `PrivateNetwork=yes`, `KillMode=control-group`,
`MemoryMax=1G`, `TasksMax=64`, `CPUQuota=100%`, and `RuntimeMaxSec=300`.
Its argv pinned the signed package image, copied `/var`, `/usr/bin/bwrap`,
512 MiB volume cap, and retained commit. The harness used only the signed
`continueCommand`; it did not rerun the create action or issue a mutating Git
POST. The packaged bridge and nginx lived in the inner private network
namespace; there was no host TCP port for this test.

The real app returned GitWeb summary HTML for the retained commit twice under
one unchanged Web projection, with exactly one app-side WebSession creation.
Changing its effective bits from `[read,write]` to `[read]` created a second
WebSession. More directly, the **same subject and API session resource** saw
Git receive-pack advertisement status 200 under `[read,write]`, then status
403 after `[read]` attenuation and app-side session replacement. A separate
read-only subject still received upload-pack advertisement containing the
retained commit. The last deliberately expired **read-only GET** poisoned
the driver and a subsequent call was refused. This establishes deadline
poisoning, not behavior after an uncertain delivered write.

The unit exited successfully in 1.698 seconds, consumed 1.666 seconds of CPU,
and peaked at 175.2 MiB. It is now inactive, MainPID 0, empty ControlGroup;
no UID 995 process or host TCP listener on the app's tested ports remained.
The bounded safe result is retained in
[`probe.log`](../../docs/evidence/2026-09-27-spk-gitweb-session/probe.log).

This does not authorize a Mini lifecycle BEGIN or HTTP dispatch. The current
native projection and one-shot launch claim must be integrated into the same
driver before a product path can serve requests. The fixture does not prove
general SPK compatibility or full Sandstorm syscall equivalence.
