# Mini candidate: interfaces an operator depends on

This directory builds a source-pinned Mini family, packages it in one format, and
supplies a standalone Store bootstrap (`run.sh`). The bootstrap starts the public
Store socket only. A hosted service also provisions the private operator socket,
public relay, member entrance, controllers, app broker and their configuration;
the manifest records which executables a candidate ships, and their presence does
not establish that those services are configured or that a combined deployment has
passed its receiving journeys (section 8).

Two routes produce a candidate directory and both end in `package.py --roles`
(section 1): `build.sh` (from scratch, below) and `lane-build.sh` (an incremental
build from a warm base; `scripts/pipeline/publish-artifacts` drives it). Protocol
allocations and socket exposure are owned by
[`protocol/host-operations.json`](../../protocol/host-operations.json), checked
against the actual receivers; read the copy inside the selected source archive
when examining a deployed image.

Procedure, from a clean Linux x86-64 account:

```sh
git clone https://github.com/emberian/minidregg && cd minidregg && git checkout <commit>
deploy/candidate/build.sh --out /srv/mini/candidate-<commit>          # binaries + manifest
C=/srv/mini/candidate-<commit>
cp $C/genesis-params.example.json /srv/mini/genesis-params.json      # edit: operator decisions
$C/params.sh fill-genesis /srv/mini/genesis-params.json              # the genesis clock, chosen now
$C/run.sh init  --manifest $C/manifest.json --params /srv/mini/genesis-params.json --state /srv/mini/store-a [--pay-observer /srv/mini/pay-observer.json]
$C/run.sh start --state /srv/mini/store-a                             # or: run.sh unit ... | systemd
$C/run.sh sponsor --state /srv/mini/store-a
$C/run.sh stop  --state /srv/mini/store-a
# The journey (definition of done) stands up its own fresh Store from the same manifest:
M7_REFERENCE=/srv/mini/other-build/provenance.json \
  native/resource-client/journey.sh $C/manifest.json /srv/mini/journey-1
```

`/srv/mini/...` stands for any directory the operator chooses. No script writes
outside `--out`, `--state` or the journey's run root, except the toolchain
managers' own caches and the shared compiler-seat root (section 1).

## 1. Build and package

### `build.sh`

**Inputs.** One source archive: `--source-archive FILE.tar` made by `git archive
<commit>`, or the clean checkout the script runs in (it runs `git archive HEAD`
itself and refuses uncommitted tracked changes). The commit id is read back from
the archive (`git get-tar-commit-id`), never from a `.git` directory. All
building happens in `OUT/work/src`, extracted from that archive
(`build.sh:94-116`). `--client-only` builds only `bin/mini` and the friend clients,
writes `provenance.json` of type `minidregg-client-provenance-v1` and `SHA256SUMS`,
and no manifest (`build.sh:275-293`).

**Host requirements.** Linux x86-64 only (`build.sh:67-70`). Commands
required: `git jq tar sha256sum file curl lake rustup cargo cc python3 readelf
flock`, plus `zig` for each default friend-client target (`build.sh:72-82`);
`elan`'s `lake`/`lean` must be first on `PATH` and match `lean-toolchain`
(`build.sh:132-135`). The Store helper links the system SQLite shared library
(`libsqlite3.so`, or the versioned `libsqlite3.so.0` found by
`native/hyperdocument-link-sqlite-store/build.rs:29-39`).

**Network, all pinned by the source:**

| what | pinned by | fetched from |
| --- | --- | --- |
| Lean toolchain | `lean-toolchain` | elan's release server (first use) |
| Lean packages | `lake-manifest.json` revisions | their git URLs |
| mathlib `.olean` + generated C | the mathlib revision | the mathlib artifact cache (`lake exe cache get`), stored in `OUT/work/mathlib-cache` |
| Rust toolchain | `rust-toolchain.toml` | rustup's dist server (`--no-self-update`) |
| Rust crates | root workspace `Cargo.lock` (`--locked`) | crates.io, cached in `$CARGO_HOME` |

**Steps** (`build.sh`): Lean packages and mathlib cache; the native Host through
`scripts/build-native-host.sh` (bounded Lean compiler); the signing-consent
provider as a companion of that build (`--root Host.ClientConsentSession
--companion-of OUT/work/host-build`: modules the Host build compiled are
byte-checked and reused); every Rust role; friend clients; usage smoke and
`scripts/check-host-cold-start.sh`; then `package.py`. Evidence lives in
`OUT/work/host-build/` and `OUT/work/consent-build/`.

All concurrent native builds on a host must select the same compiler-seat root,
`MINIDREGG_LEAN_SEAT_ROOT` (default `/tmp/minidregg-lean-seats`,
`scripts/build-native-host.sh:347`); operators coordinating several accounts
configure its custody explicitly. `MINIDREGG_CYCLE_DIR` selects evidence, not
extra compiler capacity.

**Rust determinism.** Each Rust build runs in its own absolute source directory
with `--locked`, `CARGO_INCREMENTAL=0` and `--remap-path-prefix` for the source
(`/minidregg`), `$CARGO_HOME` (`/cargo`) and the target directory (`/target`)
(`build.sh:182-188`; `lane-build.sh` rust step for the lane path). No binary
postprocessing is used. `lib.sh`'s `candidate_build_root` (a fixed-symlink build
root) is used only by `scripts/pipeline/check-reproducible`; neither `build.sh`
nor `lane-build.sh` calls it.

### `package.py`: the one packager

`deploy/candidate/package.py --roles ROLES.json --source-archive SOURCE.tar --out
NEW_DIR [--toolchains T.json] [--host-build-manifest M.txt] [--into-existing]`
writes every candidate directory. `build.sh` calls it with `--into-existing`
(binaries already in `OUT/bin`); `lane-build.sh pack` calls it with its own roles
manifest. `lane-build.sh host|consent|rust|pack` is an incremental native build
from a warm base, the consent companion, the Rust roles, and a `pack` that refuses
unless no compiled input changed between the build commits and HEAD
(`lane-build.sh:37-50`).

**The role list is `package.py`'s, not this document's.** `ROLES`
(`package.py:47-74`) maps each role to its file under `bin/`; `RUST_ROLES`
(`package.py:78-86`) is the one list both builders read (`package.py --rust-roles`
prints `ROLE CRATE BINARY`); `host` and `consent` are the Lean roles. A roles
manifest that lacks any Lean role or any `--rust-roles` role is refused
(`package.py:424-428`), and so is one whose archive commit differs from its
`sourceCommit` (`package.py:21-24`, `286-287`). `REQUIRED` (`package.py:96`: `host
consent mini store verifier keys`) are the roles every Store needs; `run.sh`
requires only those and verifies every other role a candidate carries.

**Shipped files** (`package.py:285-395`):

- `bin/<ROLES[role]>` for each role, mode `0555`.
- `bin/clients/x86_64-unknown-linux-gnu/`: hard links of `mini`, `minidregg-host`,
  `minidregg-client-consent`, the verifier and the Store helper (`BUNDLE`,
  `package.py:101-102`); `provenance.json` `.clients["x86_64-unknown-linux-gnu"]
  .consent` pins them (section 7). `bin/clients/TARGET/mini` friend clients for each
  target in `MINI_CLIENT_TARGETS` (`build.sh` default `aarch64-apple-darwin`,
  cross-linked with `zig cc -target aarch64-macos`; `MINI_CLIENT_TARGETS=` builds
  none) are added to `.clients` and `outputs` when present.
- The operator scripts, extracted from the same archive (`SCRIPTS`,
  `package.py:104-109`): `run.sh lib.sh params.sh check-tamper.sh genesis.sh
  genesis-params.example.json INTERFACES.md`; `genesis.sh` and the example params
  come from `native/resource-client/`, the one genesis template the acceptance
  fixture also uses.
- `source.tar`, `logs/source-files.sha256` (every archived file), `provenance.json`,
  `SHA256SUMS` (relative to `OUT`) and `manifest.json`.

At `45f45d15` this was 26 output paths (21 roles plus the five-file Linux friend
bundle; `docs/evidence/2026-10-27-m7-round2-dregg-ref/README.md`); a `build.sh`
run with the default client target adds the macOS client.

**Journey fixtures are not candidate outputs.** `package.py --fixture-roles` lists
the binaries the journeys need that no operator runs (`FIXTURES`,
`package.py:87-91`). `lane-build.sh rust` builds them into `LANE_DIR/fixtures`,
`pack` copies them to `OUT/fixtures/` with their own `SHA256SUMS`, outside `bin/`,
`manifest.json` and the shipped `SHA256SUMS`; `scripts/pipeline/journey-runner`
reads them there and `scripts/check-journey.sh` builds them from the checkout.
`build.sh` builds none.

**`manifest.json`** has type `minidregg-candidate-manifest-v2`: the journey's
absolute role paths and SHA-256 pins (`.sha256`), aliases (`shell` = `mini`,
`hermes` = `grainRuntime`, `browserProxy` = `spkBrowserProxy`, `consentHost` =
`consent`; `package.py:97`), `candidate` (absolute path of `provenance.json`),
`sourceCommit`, `clients`, and `outputs`, keyed by every relative file below
`bin/` (`package.py:370-391`). Every output records:

```json
{"sha256": "<64 hex>",
 "build": {"sourceTree": "<git tree of the archive's files>",
           "rustcVerbose": "<builder rustc -vV>",
           "leanToolchain": "<lean-toolchain file contents>",
           "cargoLockSha256": {"Cargo.lock": "<64 hex>"},
           "flags": {"rust": {}, "native": {}}}}
```

The packager refuses a build without the builder's `rustc -vV` and nonempty
`buildFlags.rust` and `buildFlags.native` (`package.py:255-263`). The tree id is
computed from the archive's own files in a throw-away repository, so packaging
needs no checkout; where a repository holds the commit, its `COMMIT^{tree}` must
equal it or the archive is refused as not `git archive COMMIT`
(`package.py:144-170`, `264-271`).

**`provenance.json`** (`minidregg-candidate-provenance-v1`, written at
`package.py:330-373`): `source` (`commit`, `tree`, `archive`, `archiveSha256`,
`origin`, `fileList`, `fileListSha256`), `target`, `toolchains`, `binaries`
(role to relative path and hash), `abi`, `packaging`, optional `hostBuildManifest`,
`clients`, `outputs` and `builtUtc`. Binary paths are relative to `OUT`. `.abi`
records each ELF's non-weak `GLIBC_*` version needs (`readelf -V`):
`edge/mini/ship.sh` (dregg-infra) refuses a box whose glibc is older than
`.abi.glibcRequired`.

**Verification at run time.** `run.sh` requires manifest v2, checks that the
manifest's `outputs` equal the provenance's and that every output's build identity
is complete (`lib.sh:35-70`), and hashes every output before any `init`, `serve`,
`start`, `stop`, `status`, `upgrade`, `platform` or `sponsor` (`run.sh:59`,
`126-130`, `155`). A mismatch refuses with `binary NAME sha256 mismatch: manifest
X, file Y` (`lib.sh:97`). There is no bypass flag or variable. This protects
against binary changes relative to an operator-selected manifest; the manifest is
the trust input, not a cryptographic signature on the publisher. Old manifests
refuse: re-emit them with `package.py` and complete builder evidence, and
initialize a fresh Store for a rebuilt executable family. Relative output paths
stay valid when a candidate directory is copied; the absolute role, client and
provenance references in its manifest must be relocated together
(`check-tamper.sh` does this for its copy).

**Hot-swap overlays.** `lane-build.sh overlay BASE PARENT LABEL ROLE...` (over `package.py
--overlay`) makes `PARENT/<id>` from a candidate BASE with ROLE's binaries rebuilt at the lane's
commit, for testing between cuts; it is never a READY cut. `<id>` is 12 hex, the candidate id
`ship.sh` takes: the first 12 hex of the SHA-256 of its `provenance.json` as canonical JSON
(sorted keys, no spaces) without `.overlay.id`, `.builtUtc` and each role's `.overlaidUtc`.
Provenance names files relative to the candidate, so the id does not depend on where it lives,
and the same overlay with the same LABEL twice is one id (the second is refused). LABEL is
`.overlay.name`. An overlay is told from a cut by `provenance.json .overlay`, never by its name. A role's whole build family is swapped or the overlay is
refused (every role of one crate, or `host` with `consent`), since one crate's binaries from two
commits fail at run time. Untouched files are hard links of BASE, which is never written. Every
pin is re-emitted by the packager: `manifest.json` (paths relocated to OUT), `SHA256SUMS` (BASE's
list plus `overlay/COMMIT.source.tar`) and `provenance.json`, whose `.overlay` records `base`
(provenance path, sha256, commit), `sources` (each overlay commit's tree, archive and toolchains)
and `roles` (each swapped role's commit and sha256). A swapped output's build identity names its
overlay commit's tree; `lib.sh` accepts an output tree only when it is the base's
`.source.tree` or one of `.overlay.sources`. The operator scripts, `source.tar` and `world/` stay
BASE's. A Hermes runtime root bound to BASE follows with `build-runtime-root --rebind ROOT OUT`
when `grainRuntime` or `grainProviderBridge` is swapped.

### Reproducibility (M7)

`native/resource-client/journey.d/m7.sh` compares every output against an
independently built candidate (`M7_REFERENCE`, or `.m7Reference` in the manifest),
checks both sets' bytes and compiled inputs, exercises tampered `init` and `serve`,
then initializes, serves, reads through and stops its own Store. Measured:
`docs/evidence/2026-10-27-m7-round2-dregg-ref/README.md` records a cold build of
`45f45d15` on a second Debian 13 box reproducing all 26 output SHA-256s of the
first box's candidate (Hetzner ccx33 pair, toolchains matched); the earlier
`docs/evidence/2026-09-30-candidate/` baseline covers four binaries on one machine.
Both are for the commits and toolchains they name; a different commit, toolchain or
glibc has no measurement until M7 runs on it.

The tamper plants are `scripts/kn2/plant-m7-tamper.sh CANDIDATE NEW_EVIDENCE_DIR`
and `scripts/kn2/plant-m7-no-verification.sh CANDIDATE NEW_EVIDENCE_DIR`; the
latter removes the verification calls only in a temporary `run.sh` and requires
M7's tamper check to fail with its pinned refusal-test message. `check-tamper.sh`
is the shipped tamper exerciser.

## 2. Processes

```
supervisor ─ run.sh serve ─exec→ mini serve --host H --config PINNED --socket STATE/public/mini.sock
                                   └─ H PINNED stdio            (one long-lived Host child, stdin/stdout)
                                        ├─ STORE serve            (one long-lived coprocess; each call answered in-process)
                                        └─ VERIFIER serve         (one long-lived coprocess; each check answered in-process)
clients: mini ... --socket STATE/public/mini.sock   (connect, one request, one reply, close)
```

* `mini serve` owns the socket and one Host child. Connections are concurrent,
  one thread each; the Host exchange is serial, one request at a time
  (`native/resource-client/src/transport.rs:1744-1758`, `1824-1865`). Bounds
  (`SERVE_BOUNDS`, `transport.rs:1607-1612`): 64 live connections (the next is
  refused `busy: connection limit`), a Host queue of 32 (`busy: host queue full`),
  60 s queue residence, 10 s to read an envelope. The queue is fair between peer
  uids: when full, a peer holding more than its share gives up its newest queued
  job (`native/resource-client/src/serve_queue.rs`). Every such refusal is a `254`
  reply for a request that never reached the Host.
* If the Host exits between requests it is restarted; if a request errors or
  exceeds its bound the Host is killed and restarted and that request's status is
  uncertain (the client retains the exact call and `mini retry` recovers the
  original outcome). Only a Host that cannot be started ends the service
  (`transport.rs:1832-1862`).
* The Store helper and verifier are `serve` coprocesses of the same executables
  the CLI forms run: each request frame is one argv answered by the one-shot
  function in-process (`native/hyperdocument-link-sqlite-store/src/main.rs:227-236`,
  `native/credential-signature-verifier/src/main.rs:134-144`; Host side
  `Compiler/NativeCoprocess.lean`).
* SIGTERM to `mini serve` ends it; the Host sees EOF on stdin and exits. A systemd
  unit should use `KillMode=control-group` (the `run.sh unit` template does).
* `run.sh` sets `TMPDIR=STATE/tmp` for everything it starts.
* The standalone Store process opens no TCP port. The browser proxy, provider and
  entrance services have their own network configuration. Remote access (SSH to
  the Store's account, a forwarded Unix socket, a gateway) is an operator
  decision; the socket protocol below is local and authenticates by file-system
  ownership and the config/Host pins, not by a network handshake.

## 3. The client socket

`STATE/public/mini.sock`, a Unix stream socket.

* Its directory must be owned by the serving account with mode `0700`; the socket
  is `0600`. Only that account can connect.
* Sidecars in the same directory, owner-private: `mini.lock` (flock; one server per
  socket), `mini.config` (byte copy of the served config; a later `serve` with
  different config bytes is refused), `mini.mode` (`public-v1` or `operator-v1`; a
  public socket is never upgraded to operator mode).
* A stale socket file whose listener is gone is removed at start; a live one is
  refused.
* The socket path must be shorter than 108 bytes (`sockaddr_un`), so `STATE` must
  be at most 90 bytes. `run.sh init` refuses a longer one (`run.sh:64-67`).

**Framing.** Every message in both directions is `u32 little-endian length` then
that many bytes (`transport.rs:703-713`). The length bound is `MAX_FRAME`
(`transport.rs:25`): the lookup frame bound 12,103,788 (`bounds.rs:9`) + 5 + the
config bound 65,536 + 32, that is 12,169,361. The Host request frame bound is
12,102,760 (`bounds.rs:7`).

**Request envelope** (client to socket, `split_envelope`, `transport.rs:198-230`):

| bytes | field |
| --- | --- |
| 1 | envelope version: `1`, or `2` (adds the Host pin; `mini` sends 2) |
| 4 | u32 LE config length (at most 65,536) |
| n | the pinned config file's exact bytes; must equal what the server serves |
| 32 | (version 2) SHA-256 of the Host executable the client expects |
| 1 | operation byte |
| rest | operation payload |

**Reply** (socket to client): the first byte is the echoed operation byte and the
rest is its result; or an outcome marker, `253` (`RESPONSE_NO_RECORD`: the Host decided
before any append) or `255` (`RESPONSE_HOST_OUTCOME`), followed by an `OUTCOME` frame
(section 4); or `254` followed by a UTF-8 reason for a refusal the Host never saw
(`config pin mismatch`, `host image pin mismatch`, `invalid socket envelope`,
`operation unavailable on selected socket`, `host frame exceeds bound`, the
`busy: ...` refusals above). The markers are generated constants
(`mini_sdk::host_operations`, from `protocol/host-operations.json`). The server
allows 10 s to receive a request and 10 s to write a reply; the client waits up to
600 s for a reply (`transport.rs:1219`, `1239`).

**Operation allocation and exposure.** `protocol/host-operations.json` owns
request bytes, status, purpose and public/operator routes; the registry checker
compares it with Host dispatch and client selectors. A reserved byte is not a
callable endpoint. Consult the named receiver and codec for payload shape; a
second manual table here would drift from those consumers.

`mini serve-operator` serves a separate owner-private socket with the lifecycle,
dispatch and other operator routes (`--peer-uid` admits further uids; the owner is
always admitted). `mini serve-public-proxy --socket PUBLIC --upstream PRIVATE
--config CONFIG.json` supplies public access through that private Host using the
registry's allowed public routes (usage text, `native/resource-client/src/main.rs:839-842`).
The standalone `run.sh` recipe does not provision this composed topology; a hosted
installation selects it explicitly and binds controllers, payment observers and app
custodians to the correct socket.

**Host stdio.** `mini serve` speaks the same frames to the Host child without the
envelope: `u32 LE length` then `operation byte + payload`; the Host replies `u32 LE
length` then `operation byte (or a marker) + payload`. Direct CLI use
(`minidregg-host CONFIG COMMAND ARGS`) is how `genesis.sh` runs `profile` and how
`mini bootstrap` runs genesis; the full command list is the Host's usage text
(`minidregg-host` with no arguments).

## 4. Wire codecs

All binary messages are Lean `StreamCodec` values (`Theory/StreamCodec.lean`),
decoded strictly: a message is accepted only if re-encoding the decoded value gives
back exactly the input bytes. A nat is little-endian base-255 digits (each 0..254)
followed by byte `0xFF` (`encodeNat`, `Theory/StreamCodec.lean`); bytes,
lists, products, sums and bool are defined beside it, and a framed message is an
ASCII magic then the stream encoding.

The frame names and versions are owned by `Compiler/NativeProtocolFrames.lean`
(signed call, draft, signing plan, outcome, observe intent, challenge and signed
frames); the message shapes by `Compiler/NativeHostCodec.lean` and
`Compiler/NativeObservationCodec.lean`; the genesis source frame by
`Kernel/NativeHostGenesis.lean:257` (`configFrame`). A retired version is refused,
never reinterpreted: each codec keeps its retired frames next to the proof that
they refuse. This document does not copy version numbers.

An outcome is confirmed (with receipt and confirmation kind installed /
recoveredAfterUncertainResponse / replayed), refused (one byte of the closed
`RefusalReason`, `Compiler/RefusalReason.lean`; a law refusal may also name the
failing clause), contention, absent, unavailable or uncertain. On a Host refusal
`mini` prints `refused: <reason>: <text>` and exits 3 (`main.rs:188-208`); other
statuses are in the same function. A refusal's `phase` is a short source-selected
word. Before a signature verifies, only `unknown-key` and `stale-root` are named
(anything else is `undisclosed`); a blind submission's refusal is always
`undisclosed`.

## 5. Host and helper protocols

The Host reaches each helper through its `serve` coprocess (section 2); the
argument vectors and results below are those of the one-shot CLI, which the
coprocess answers identically.

**Store helper** (`storageBinary`, root `storageRoot`); verbs are the `USAGE` string
at `native/hyperdocument-link-sqlite-store/src/main.rs:28`:

| call | success | other outcomes |
| --- | --- | --- |
| `STORE read-to ROOT OUT` | exit 0, empty stdout/stderr, image bytes in `OUT` | exit 3 = no image yet; anything else = read failed |
| `STORE cas ROOT EXPECTED\|- POST` | exit 0, stdout `Installed` or `AlreadyPresent`, empty stderr | exit 4 with empty stdout = conflict; anything else = **uncertain** |

`-` means "expect no image" (the legacy one-slot record). The durable log, its
checkpoints, the history nodes and the fn archive journal use the `durable-*` and
`journal-*` verbs; their files, exit codes and the sibling anchor are specified in
`docs/DURABLE-STORE.md` (exit codes in `main.rs:200-209`). The binary has no
test-only verbs: the crash and hold fixtures live in the crate's `fixtures`
feature binary.

**Signature verifier** (`signatureBinary`): `VERIFIER verify PUBLIC FRAME SIG` with
a 32-byte raw public key file, the frame file and a 64-byte raw signature file;
exit 0 with stdout exactly `verified\n` or `invalid\n` and empty stderr; anything
else is an error, never an acceptance. Ed25519 `verify_strict`; the frame is
opaque to the helper. `verify-sshsig PUBLIC NAMESPACE MESSAGE SIG` verifies an
OpenSSH SSHSIG signature over the same key shape (`USAGE`,
`native/credential-signature-verifier/src/main.rs:92`).

## 6. State directory (`run.sh init --state STATE`)

Everything is created owner-only (`umask 077`, directories `0700`).

| path | written by | content |
| --- | --- | --- |
| `state.json` | init | `minidregg-candidate-state-v1`: absolute manifest path, Host SHA-256, pinned-config SHA-256, creation time. Every later command re-checks the manifest pins, this Host pin, and the helper paths in the pinned config |
| `genesis-params.json` | init | copy of the operator's params (completion custodian key filled in) |
| `keys/sponsor.key`, `.pub`, `.pub.hex` | `mini keygen` | the genesis sponsor's key (format in section 7) |
| `keys/clock.key`, `.pub`, `.pub.hex` | `mini keygen` | the clock subject's key: its only authority is `C_tick`; its workspace is made with `mini clock --action init` (deploy: `/var/lib/mini/clock`, `deploy/clock/mini-clock-tick.service`) |
| `keys/completion.seed`, `.pub`, `.pub.hex` | `mini keygen`, only when `.grainPlatform.completionCustodianKey` is `null` | the grain platform's completion custodian; its public key is pinned into the genesis config and its seed signs lifecycle completions; never copied out of `keys/` |
| `operator.json`, `profile.json`, `genesis.json`, `sponsor-birth-context.json`, `clock-birth-context.json` | `genesis.sh` | see below |
| `deployment/` | `mini bootstrap` | `checkpoint.key` (the Store's checkpoint and log MAC key, random, mode 0600, one per Store), `genesis-source.json`, `operator-config.json` (copies), `genesis-source.bin`, `genesis.bin`, `pinned-config.json`, `profile.json`, `description.json`, `pay-ledger-genesis.json` (`main.rs:1449-1495`) |
| `store/forward-link.sqlite3` | Store helper | the durable image |
| `sponsor/` | `run.sh sponsor` | the sponsor's participant workspace (`workspace.json`, `refs/`, `proposals/`, `attempts/`, `sources/`) |
| `namespace/` | sponsor workspace | durable identity reservations for names the sponsor allocates |
| `public/` | serve | `mini.sock`, `mini.lock`, `mini.config`, `mini.mode`, `server.pid` (`start` only) |
| `tmp/` | Host, helpers | scratch (`TMPDIR`) |
| `logs/` | run.sh | bootstrap and sponsor output, `serve.log` (`start` only) |

**Genesis params** (`minidregg-candidate-genesis-params-v1`). The schema is the
`check_params` function in `native/resource-client/genesis.sh:46-74`, which
`run.sh init` runs first (`run.sh:53`, `61`); `native/resource-client/genesis-params.example.json`
holds the values the recorded qualification runs used. In outline: the genesis
coordinates and tariffs as JSON integers (0 <= n < 2^53), `sponsor {...}`
(`nextKeyDigest` must be present; `run.sh init` generates the sponsor key and so
accepts only `null`, `run.sh:82-83`), the dedicated `clock {...}` subject (distinct
from the sponsor; `tickCapabilityId` is its `C_tick`), `meterAllowance` with exactly
ten integer keys, `issuanceCap`, `tailBound`, `payControlCapability`, optional
`disabledEvaluators`, and, for a world that hosts SPK grains (`deploy/market/INSTALL.md`
section 0), `grainPlatform {lifecycleManagement {managementSubject managementKeyId}
grainBirthTariff {base perBirth} completionCustodianKey}` (`genesis.sh:82-97`).
The management subject is a Host setting (`run.sh platform` rewrites it, restarting a
Store that `run.sh start` launched; a unit-managed Store is stopped by its unit first); without `grainPlatform` the world refuses every grain install by name.
`params.sh require-platform PARAMS.json` refuses a genesis lacking the block,
naming the field.

**The genesis clock.** `genesis-params.example.json` carries `clock.genesisNow:
null` and `clock.maxStepSeconds: null`. `run.sh init` and `genesis.sh` refuse an
unfilled or non-positive value (`clockStepBoundInvalid`, `clockGenesisNowInvalid`;
`genesis.sh:47-50`). `params.sh fill-genesis PARAMS.json` fills them in place at
genesis time: `genesisNow` = now or `$GENESIS_NOW`, `maxStepSeconds` =
`$MAX_STEP_SECONDS` or 300 (`params.sh:47-48`). It never repairs an explicit bad
value (0 refuses) and never re-dates a filled file: a present value other than the
one it would write refuses (`params.sh:60-66`). A driver that hand-writes a `mini
bootstrap --source` file calls `params.sh fill-source SOURCE.json`
(`clockGenesisNow`, `clockMaxStepSeconds`, decimal strings) instead. The
`deploy/clock/mini-clock-tick.service` header states the same rule.

The sponsor and the clock subject are the identities genesis names; every later
participant is enrolled through the client and receives Host-allocated identifiers.
`genesis.sh PARAMS SPONSOR_PUBLIC_HEX CLOCK_PUBLIC_HEX HOST STORE VERIFIER DIR`
takes both public keys. Its optional environment inputs are documented in its
header: `EXTRA_CLOCK_TICKERS`, `EXTRA_GENESIS_ENROLLMENTS`, `GENESIS_PAY_OBSERVER`
(set by `run.sh init --pay-observer`, `run.sh:105-110`).

**`operator.json`** (Host `Settings`, `Host/Main.lean:694`): written by `genesis.sh`
from the params (`genesis.sh:132-145`): the 15 coordinate numbers (`domain`
through `genesisHeight`), `expectedSeed: 0`, the absolute paths `storageBinary`,
`storageRoot` and `signatureBinary`, and, when present in the params,
`disabledEvaluators`, `objectiveInvocation`, and from `grainPlatform` the
`lifecycleManagement`, `grainBirthTariff` and `completionCustodianKey` sections.
The other optional `Settings` sections (fn gateway and polls, provider services,
agent dispatch) stay absent; `checkpointKey` is set at bootstrap.

**`genesis.json`** (genesis source, `genesis.sh:151-192`): the same coordinates as
decimal strings, `expectedSemantics` (from `profile.json`), `issuerEpoch`,
`factoryPredicate`, two `enrollments` (the sponsor with its initial balance; the
clock subject with balance 0), `factoryControllerSubject`,
`factoryControllerCapability`, `payControlCapability`, `meterAllowance`,
`tailBound`, `issuanceCap` (the tariff asset's issuance cap, installed as its
issuer well's floor; the sponsor's initial balance counts against it),
`clockGenesisNow`, `clockMaxStepSeconds` and `clockTickers`
(`[{subject, capability}]`, the clock subject first). Genesis installs the clock
cell's law admitting exactly the tickers' `tickClock` requests, one `C_tick` per
ticker, and confines the factory law against every ticker. The Host refuses a
genesis whose coordinates differ from `operator.json`.

**`pinned-config.json`** is `operator.json` plus the genesis `expectedSeed` the
Host derived. It is the config every client presents: the socket compares its bytes
exactly, and the Host checks the image it opens against its `expectedSeed`. It
names the helpers by absolute path, so the candidate directory must stay where it
was when `init` ran (or `run.sh upgrade` rebinds a stopped Store to a new
manifest's helpers, section 7).

## 7. Supervision (`run.sh`) and key files

* `serve` validates every output hash, the state's Host pin and the helper paths in
  the pinned config, sets `TMPDIR`, then `exec`s `mini serve` (`run.sh:208-213`).
  Use it under systemd (`run.sh unit --state STATE` prints a unit: `Type=simple`,
  `Restart=on-failure`, `KillMode=control-group`, `UMask=0077`,
  `NoNewPrivileges=yes`, `PrivateTmp=yes`, `ProtectSystem=strict` with
  `ReadWritePaths=STATE` alone, `RestrictAddressFamilies=AF_UNIX`, `MemoryMax=8G`;
  `run.sh:305-328`) or any other supervisor.
* `start`/`stop`/`status` are a minimal supervisor for hosts without one. `start`
  backgrounds `serve`, records `public/server.pid`, and waits (at most 120 s) for the
  socket and a line matching `^mini: host process [0-9]+$` in this launch's part of
  `logs/serve.log` (`run.sh:227-249`; the line is printed at `transport.rs:1535`).
  `stop` only signals a pid whose command line is `... serve ... --socket
  STATE/public/mini.sock`, and waits (at most 60 s) for it and its Host child to
  exit (`run.sh:215-272`).
* `sponsor` creates the genesis sponsor's workspace and imports the factory
  reference (needs the Store serving); it is idempotent. It selects the signing
  consent trio from the verified manifest roles (`run.sh:279-284`).
* `upgrade --manifest N1_MANIFEST` rebinds a stopped Store's `storageBinary` and
  `signatureBinary` and its recorded Host pin to a new candidate; the Store and its
  semantic configuration are unchanged (`run.sh:133-174`). `platform
  --management-subject S --management-key K` sets the Store's lifecycle management in
  the pinned config (a Store `start` launched is stopped through its PID file and
  started again; a unit-managed one is refused until its unit stops it; `run.sh:182-215`); clients re-pin the config.

**Key and workspace files.**

* **Secret key**: exactly 32 raw bytes (Ed25519 seed), a regular file owned by the
  invoking user with no group/other permission bits. The client refuses any other
  shape (symlink, wrong owner, `0644`, wrong length).
* **Public key**: exactly 32 raw bytes. `mini keygen` also prints it as hex.
* Keys never enter the Host: the Host authors headers and plans, the client signs
  them locally, the Host assembles detached signatures.
* **Workspace** (`mini workspace --action init`): `workspace.json`
  (`minidregg-participant-workspace-v1`: absolute Host, config, socket and key
  paths, subject, optional enrollment, birth context and namespace root). A
  workspace is bound to one Store and one key.
* **Attempts**: every write keeps `intent.json`, `challenge.json`, the exact
  `call.bin` before submission, and `outcome.json`. `mini retry --attempt DIR --mode
  submit|lookup` resends the exact call or looks it up; an admitted call comes back
  `replayed` with its original receipt, never as a second effect.
* **References** (`refs/NAME.json`, `minidregg-participant-reference-v1`; delegation
  hand-off `recipient-reference.json`, `minidregg-delegated-reference-v1`):
  `authority: "hint-only"`. Names are local hints; the Host decides use from signed
  observations and current law.
* **Signing consent**: the client signs only after a locally selected consent
  provider reconstructs the bytes; `MINI_LOCAL_HOST`, `MINI_CONSENT_HOST` and
  `MINI_CONSENT_CONFIG` select it (absolute paths, all three together). Without them
  the client refuses to sign. Details: `deploy/shell/README.md`, "Signing consent:
  the three variables".

## 8. What the operator decides

- **fn image.** Mini at or after `fn frames!` requires an fn with `--frame` and
  refuses one without it by name. The production and dev fn pins are recorded in
  `protocol/fn/images.json` (production `d420a2b5` has no `--frame`; the `--frame`
  build is the journeys' and pipeline's dev pin). Production deploy waits for fn's
  converged image.
1. **Placement and paths**: which machine and Unix account hold the candidate, each
   Store's state directory (at most 90 bytes, for the socket), and the sponsor key.
   All scripts take them as arguments; nothing defaults to a shared or temporary
   location.
2. **Genesis coordinates** (`genesis-params.json`): identifiers, tariffs, budgets,
   lifetimes, meter allowances, the sponsor's validity window and the genesis clock.
   They are fixed for the life of the Store; changing them is a new Store.
3. **Custody of the sponsor key**: it authorizes every enrollment and owns the
   factory control capability. The candidate generates it inside the state
   directory; moving it elsewhere means editing the sponsor workspace's
   `workspace.json` key path.
4. **Supervision**: systemd (`run.sh unit`) or another supervisor running `run.sh
   serve`; restart policy; log retention.
5. **Access**: public and operator Unix sockets retain owner-only custody. Remote
   members enter through the forced Mini-shell/proxy protocol; they do not need Unix
   shell accounts. See [shell deployment](../shell/README.md) and its
   [operator guide](../shell/OPERATOR.md). Member credentials and signing authority
   remain distinct from the service account running the transport. The standalone
   bootstrap does not install SSH or browser ingress policy.
6. **Backups**: the state directory holds several owners' records (the durable image
   in `store/`, the sponsor's workspace and attempts, namespace reservations, keys).
   Participants' own workspaces and keys live wherever they keep them. Restoring one
   of these does not restore the others consistently. Back up with the service
   stopped.
7. **Capacity**: measure the selected family with its real workload, population,
   admission limits and resource settings. The September 29 measurements in
   `docs/evidence/2026-09-30-candidate/` describe that earlier source and are not
   current capacity limits. Distinguish cold history audit, cached reopen,
   interactive writes, app work and provider contention.
8. **Upgrades**: current service deployment uses full teardown and rebuild from the
   selected family, with repeatable provisioning. Legacy migration or rolling
   transition is not a release prerequisite. Preserve old state deliberately before
   teardown when its data is wanted.

## 9. Hosted service composition

A candidate ships the controller/provider bridge, scheduler, SPK hosting, browser
proxy, broker and volume helper, payment watcher, key broker, launch gate, the
self-serve door and its root processor, the web gateway and its root session
helper, and the Discord entrance and room mirror (`ROLES`, `package.py:47-74`).
Which of these are configured on a box is not recorded here. Their operator
contracts are in [Hermes](../hermes/README.md), [SPK hosting](../spk-host/README.md),
[payments](../pay/README.md), [member access](../shell/README.md),
`deploy/door/README.md`, `deploy/web-frontend/INSTALL.md` and
`deploy/discord/README.md`, together with the matching source's command and config
parsers. Deployment unit templates and root-owned service provisioning are in those
directories.

Qualification belongs to the actual configuration and executable family: one
Store/world shared by enrolled members, residents and apps; current authority and
independent budgets; concurrent admission; ordinary crash and retry; and a usable
checkpoint and resume path. Component or fixture success alone does not establish
that combined service. Cross-node operation and participant hosting similarly
require their own configured topology and receiving evidence.
