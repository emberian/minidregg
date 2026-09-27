# Fresh signed GitWeb platform fixture preparation

This cut prepares private inputs for one new Mini Store and the signed GitWeb
INSTALL journey. It does **not** create that Store, submit BEGIN/CLAIM/completion,
install a package, launch an SPK, or mint a dispatch ticket. The v0 grain-backed
share-issue fixture is a separate Store and is not installation evidence.

## Source and identity

The three scripts in `scripts/spk-platform/` reuse the reviewed workroom,
member, app/session-birth, and positive-fee sources. `prepare.sh` checks their
exact SHA-256 hashes before copying anything. It checks the real signed GitWeb
SPK SHA-256
`2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa`
(14,045,864 bytes) and source-authored descriptor bytes SHA-256
`a853b57cb79ce72f965d97b682a17c83e1396ef8e8f2f65d130e3207dbec7e7f`.
The descriptor root is
`87005803221096792113550003106028498326059648433438765766069915491574610318393`.
The signed member and schema derivation are in
`docs/evidence/2026-09-27-gitweb-mini-identity/README.md`; the physical
installer must compare them to one signature-verified SPK parse.

All private outputs must live under a fresh operator-owned
`/var/lib/minidregg/spk/fixtures/<name>` with protected ancestors. The scripts
generate a new completion custodian seed there and inject its public key plus
fixed management pins into the workroom operator config **before bootstrap**.
All path arguments are absolute and lexically canonical; the scripts refuse
embedded or trailing `.`/`..`, duplicate separators and trailing `/`. Before
creating a seed, Store or journal they walk every relevant output ancestor,
requiring root/operator ownership, no symlink and no group/world write access.
Fresh outputs refuse both existing files and dangling symlinks. These shell
checks guard preparation paths; the native installer performs its own stronger
protected-path validation before physical use.
The resulting pinned config, source overlays, SPK and descriptor stay in that
fresh fixture. Completion and management seed bytes are never public evidence.
No existing Store is modified.

The initial fixture allocation is app 8401, package manifest 8402, snapshot
manifest 8403; Alice Web session/descriptor 8404/8405 (subject 8), Bob Web
8406/8407 (subject 9), Alice's independent human API 8410/8411. Their intended
post-install tickets are respectively 8500, 8501, 8510. Each session must be
enrolled and issued separately at the installed package version. Browser and
API tokens are transport credentials, never substitutes for Mini admission.
Two later Hermes controllers require separate agent sessions, tickets, task
accounts, custody and fixed resident routes. No agent identity is allocated or
asserted by these preparation scripts.

## Finite operator sequence

1. `prepare.sh NEW_ROOT SIGNED_GITWEB_SPK SOURCE_DESCRIPTOR MINI_CLIENT` verifies
   source and package bytes, creates the protected input copy and completion key,
   and stages a source overlay. It produces no Store.
2. After the source Host and physical SPK Host binaries are independently
   qualified, set `QUALIFIED_HOST_SHA256` and `QUALIFIED_SPK_HOST_SHA256` to
   their reviewed hashes and call
   `run-base.sh PREPARED_ROOT QUALIFIED_HOST MINI_CLIENT SQLITE_HELPER SIGNATURE_HELPER QUALIFIED_SPK_HOST`.
   All executable paths must be absolute and outside `/tmp` and `/var/tmp` for
   the later `PrivateTmp` physical unit. Before any Store is created, the
   physical `qualify-launch` command must parse this signed SPK once, use the
   source Host's pure v2 launch-descriptor author/inspect codec, and return
   exact package/launch roots, ordered create-command and continue-command
   digests, canonical bytes and retained inspection. The script compares
   those fields and refuses a missing CLI, unsupported version or mismatch.
   The reviewed workroom source then regenerates its operator Settings JSON;
   a full canonical JSON comparison with the pre-Store offline Host config
   must pass **before bootstrap**. This catches any drift in the duplicate
   preflight settings producer, rather than comparing just the custody fields.
   Only then does it run the reviewed birth scripts in a **new** Store. The
   integrated source overlay adds eight independently enrolled agent
   signers/accounts, eight grains, six source-admitted parent witness
   delegations, and distinct Bob Web, Alice API, and two agent API sessions
   alongside the original app/package/snapshot and Alice Web session. It
   retains exact birth/delegation receipts and participant-signed resource
   readbacks. It checks the pinned completion key and management config.
3. With a protected live Mini operator socket under `/run`, call
   `prepare-install-config.sh PREPARED_ROOT QUALIFIED_HOST OPERATOR_SOCKET APP_UID IMAGE_DIR NEW_INSTALL_JOURNAL`.
   The image path is exactly
   `/var/lib/minidregg/spk/packages/sha256-2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa`;
   the fresh journal is under `/var/lib/minidregg/spk/install-ops/`. This writes
   private BEGIN, CLAIM and INSTALL-completion signer profiles and
   `mini-spk-resident-install-v1` config. It submits no lifecycle event.

   This existing helper describes the earlier INSTALL contract and is **not
   yet qualified for the v3 launch-root lifecycle**. Do not submit its output
   to the fresh integrated Store. The eventual INSTALL/START recipe must use
   the qualified v2 `launchRoot` and retained canonical descriptor, while the
   embedded v1 `packageRoot` identifies the signed package inside that
   descriptor.

The three signer files pin subject 8/key 8008/epoch 2 to the existing
management seed and exact ordered Mini plan roles. BEGIN pins invocation
`(4,0),(1,0)` and package observation `(9,0)`; CLAIM pins `(4,0),(1,0)`
plus app/package observations `(9,0),(10,0)`; INSTALL completion pins
`(4,0),(4,1),(8,0),(8,1),(1,0),(9,0)`. The Rust signer compares each actual
Mini source plan's role, index, key, epoch and canonical header before signing;
these static shapes are not a substitute for the source plan. START needs its
own one-target completion signer file and resident config, after the final
physical `agents: Vec` route schema freezes. The shared app process must offer
independent Alice/Bob Web entrances, Alice's separate API entrance, and two
distinct Hermes agent routes; no singular agent or shared token is sufficient.
The integrated parent birth pins each tool, dispatch payer and provider as a
generation-1 no-op witness worker, with distinct child capabilities delegated
by its controller after birth. `grain-runtime` already renews managed worker
policies before a later hard attach, but its current worker list omits the
dispatch payer. That controller renewal must be extended and qualified before
a restarted agent route can claim a fresh parent witness; a static
generation-1 capability is not lifetime authority.

## Bounded checks in this cut

`sh -n` and `shellcheck` pass on all three scripts. In an isolated test copy of
`prepare.sh` only, the root restriction was redirected to
`/tmp/spk-platform-prep-test/r1` and `REPO` to the local Mini checkout. The
production script was not modified by that test. It processed the actual SPK,
descriptor and Mini client, generated a 32-byte completion seed/public key,
and `sha256sum -c` passed for every staged input. The sample input manifest
SHA-256 was `f2c0ca0d8ca79e38d7ffe504b79c74a4b4c4ee50675946baa39483fbb8cfb750`;
the generated provision source SHA-256 was
`7188590c45bcce07cc8775d3894eead510a62f618e5b4908ac5fe4cae8606cc2`.
A dry composition of the
positive-fee and member overlays passed `sh -n` and retained the completion
key, three management settings, grain tariff and grain-backed factory mode.
That final dry source SHA-256 was
`0dee92a2fd36bcf45a2fd40848196579146f034554c88d0979db6d12bb237421`.
The scratch location is test-only: `PrivateTmp` would hide it from the physical
installer. The scratch key is not used as platform authority.

After the path-hardening edit, a fresh isolated positive preparation with the
same real SPK and descriptor passed its staged `sha256sum -c`. The scratch
copy changed only its allowed root prefix and repository path. Six focused
`prepare.sh` calls refused trailing `/..`, trailing `/.`, embedded `//`, a
dangling output symlink, a group-writable parent and a symlinked parent. A
`run-base.sh` scratch copy refused a dangling `base` symlink and trailing
`/..`. A `prepare-install-config.sh` scratch copy, with a test-only Unix socket
and no Store, refused trailing `/..`, a dangling INSTALL journal symlink and
a group-writable journal parent. None created a Store or submitted an event.

The fresh Store, these new agent/session births, INSTALL custody JSON, actual lifecycle plans, signed
source inspections, post-CAS receipts, physical image comparison, two human
sessions, direct API and two agent routes have **not** been run in this cut.
Those are the next acceptance steps after the qualified Host and final
resident route schema are available.
At this evidence date the v2 source author and offline physical
`qualify-launch` route are still being qualified, so this new positive gate
has no accepted native execution result. The script's post-gate birth path
has not run under this version. A focused scratch run with an unsupported
physical qualifier refused before `base` or `base.source-stage` was created.
The checked provision overlay passed `sh -n`; a heredoc-only evaluation of its
post-overlay operator JSON and the offline config had identical full
`jq -S` SHA-256
`4b95ae70f122e097a8598014b99ee7bbd8f4810613e711d97ed434ec229b32e4`.
This scratch comparison did not invoke Host, Mini bootstrap or a Store helper.

At the first review of this preparation cut, the then-current resident source
selected signed `manifest.continue_command` for every launch. That dated
finding explained why a virgin GitWeb volume could not start: its signed
create action runs `start.sh` to initialize `/var/repo.git`, the hook and
receive-pack. The resident source has since changed to refuse a virgin launch
before writing a journal; the v3 source-bound create/wake claim and volume
custody path are still being qualified. This preparation has not exercised
that path. The isolated `gitweb-smoke` volume is not an input to the fresh
fixture.
