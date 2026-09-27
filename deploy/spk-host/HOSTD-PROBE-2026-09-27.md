# Private SPK hostd component gate — 2026-09-27

This staged component does **not** start an application or grant a browser/API
request. Its versioned `mini-spk-hostd-v1` Unix endpoint exposes exact physical
status only. `begin` and `dispatch` return `unavailable` until source-owned
Mini admission is wired; a caller cannot send an `accepted` Boolean.

Source hashes: `native/spk-host/src/hostd.rs`
`c54a6e876b2b99d8c919216dc66f5a96d5a88d67dd44965a55cf180035228874`,
`src/endpoint.rs`
`00607e86be816164e4fa1c3e5636d65437141802614a25953ebf093f824da66e`,
`src/bin/spk-hostd.rs`
`47cc29403782a9c37a2068232c133dca46c68eeb250aca7f2028369c5b503691`,
and `src/lib.rs`
`ecc84b3fd77e26e49059359a1dc1d38b05223a32dd4f315e87eae1f4cb0eb523`.
An isolated persvati Linux build used the pinned `native/spk-host/Cargo.lock`.
Focused Nextest passed 8/8, strict library/binary Clippy passed, and the
release `spk-hostd` ELF SHA-256 was
`01b7330d34a13f529fefe91cc6241b7a5700eec6bec6bc354b646c03658207af`.
The build and test logs remain in private
`/tmp/minidregg-gitweb-smoke-20260927/hostd-{build,nextest,clippy}.log`.

The journal persists a per-operation identity and phases `armed`,
`launchRequested`, `entered`, `running`, `fenced`, `stopped` under a private
flock with file and directory fsync. Tests exercise exact replay versus
conflicting BEGIN, uncertain spawn without retry, durable fence before stop,
and a fence waiting for the spawn lock. These are component fault injections,
not a qualified production systemd app-launch gate: the injected spawn callback
is not yet time-bounded, and there is no native BEGIN adapter.

The harmless transient user unit `mini-spk-hostd-probe-20260927.service`
(InvocationID `1f549400c4e84257b95d8f479c69d3c7`) ran only
`spk-hostd serve-status /run/user/1000/spk-hostd-probe-20260927`, with
`RuntimeMaxSec=30`, `MemoryMax=256M`, `TasksMax=16`. The private directory was
owner mode 0700 and `hostd.sock` mode 0600. A bounded framed request with
request ID `aa…aa` for app 91/generation 2 received the same ID and explicit
`unavailable: no native-verified BEGIN recorded`. The service was then stopped;
`ActiveState=inactive`, `MainPID=0`, empty ControlGroup, and the exact socket
pathname removed. No SPK, Mini Store, browser request, or application process
was touched by this gate.
