# Mini candidate: interfaces an operator depends on

This directory builds a source-pinned Mini family and supplies a standalone Store
bootstrap. The bootstrap below starts the public Store socket; a complete hosted
service also provisions the private operator socket, public relay, member entrance,
controllers, app broker and their configuration. The manifest records shipped
executables; their presence does not establish that those services are configured
or that a combined deployment has passed its receiving journeys.

Updated October 8, 2026. Three routes produce a candidate directory, and all of them
go through one packager, `package.py` (section "One packaging format, one packager"
below): `build.sh` (the procedure here), `lane-build.sh` (an incremental build on a
build box) and a sealed hbox capsule (`package.py --capsule`). Every candidate carries
the signing-consent pair. Protocol allocations and socket exposure are owned by
[`protocol/host-operations.json`](../../protocol/host-operations.json), checked
against the actual receivers. Use that registry from the selected source archive
when examining a deployed image.

Procedure, from a clean Linux x86-64 account:

```sh
git clone https://github.com/emberian/minidregg && cd minidregg && git checkout <commit>
deploy/candidate/build.sh --out /srv/mini/candidate-<commit>          # binaries + manifest
C=/srv/mini/candidate-<commit>
cp $C/genesis-params.example.json /srv/mini/genesis-params.json      # edit: operator decisions
$C/params.sh fill-genesis /srv/mini/genesis-params.json              # the genesis clock, chosen now
$C/run.sh init  --manifest $C/manifest.json --params /srv/mini/genesis-params.json --state /srv/mini/store-a
$C/run.sh start --state /srv/mini/store-a                             # or: run.sh unit ... | systemd
$C/run.sh sponsor --state /srv/mini/store-a
$C/run.sh stop  --state /srv/mini/store-a
# The journey (definition of done) stands up its own fresh Store from the same manifest:
M7_REFERENCE=/srv/mini/other-build/provenance.json \
  native/resource-client/journey.sh $C/manifest.json /srv/mini/journey-1
```

`/srv/mini/...` stands for any directory the operator chooses. No script
writes outside `--out`, `--state` or the journey's run root, except the
toolchain managers' own caches (below) and the shared compiler-seat root.

## 1. Build (`build.sh`)

**Inputs.** One source archive: either `--source-archive FILE.tar` made by
`git archive <commit>`, or the clean checkout the script runs in (it then runs
`git archive HEAD` itself and refuses a checkout with uncommitted tracked
changes). The commit id is read back from the archive (`git get-tar-commit-id`),
not from any `.git` directory. All building happens in `OUT/work/src`, extracted
from that archive.

**Host requirements.** Linux x86-64; `git jq tar sha256sum file curl cc`;
`elan` (its `lake`/`lean` first on `PATH`); `rustup` with `cargo`; the system
SQLite shared library (`libsqlite3.so.0`, and `libsqlite3.so` or a C compiler
that can find the versioned one) for the Store helper.

**Network, all pinned by the source:**

| what | pinned by | fetched from |
| --- | --- | --- |
| Lean toolchain | `lean-toolchain` | elan's release server (first use) |
| Lean packages (mathlib and its dependencies) | `lake-manifest.json` revisions | their git URLs in `lake-manifest.json` |
| mathlib `.olean` + generated C for that revision | the mathlib revision | the mathlib artifact cache (`lake exe cache get`), stored in `OUT/work/mathlib-cache` |
| Rust toolchain | `rust-toolchain.toml` | rustup's dist server (`--no-self-update`) |
| Rust crates | root workspace `Cargo.lock` (`--locked`) | crates.io, cached in `$CARGO_HOME` |

**Outputs.**

| path | what |
| --- | --- |
| `OUT/bin/minidregg-host` | Lean-authored native Host, built by `scripts/build-native-host.sh` (bounded Lean compiler; shared seats in `MINIDREGG_LEAN_SEAT_ROOT`, independent of per-build evidence) |
| `OUT/bin/minidregg-client-consent` | local signing consent provider (`Host.ClientConsentSession`), built by the same builder as a companion of the Host build (`--root Host.ClientConsentSession --companion-of OUT/work/host-build`): every module the Host build compiled is byte-checked and reused, only consent-only modules compile; evidence `OUT/work/consent-build/`. Pinned as `provenance.json` `.binaries.consent` and `manifest.json` `.consentHost`. `package.py` REQUIRES it (a roles manifest or sealed family without it is refused: a candidate whose friends cannot sign is not shippable), and `build.sh` re-checks the pins and the bundle after packaging. `deploy/candidate/test-package.py` runs the packager on stub roles (no Lean) |
| `OUT/bin/mini` | client (`native/resource-client`); also the Linux x86-64 friend client (`provenance.json` `.clients["x86_64-unknown-linux-gnu"]`) |
| `OUT/bin/clients/x86_64-unknown-linux-gnu/` | the Linux friend bundle, hard links of `bin/mini`, `bin/minidregg-host` (`MINI_LOCAL_HOST`), `bin/minidregg-client-consent` (`MINI_CONSENT_HOST`), the verifier and the Store helper; `.clients["x86_64-unknown-linux-gnu"].consent` pins them (see section 8, signing consent) |
| `OUT/bin/clients/TARGET/mini` | friend clients for each target in `MINI_CLIENT_TARGETS` (default `aarch64-apple-darwin`, cross-linked with `zig cc -target aarch64-macos`, ad-hoc signed by the linker; `zig` is then required). Hashed in `provenance.json` `.clients`, `SHA256SUMS`, and `manifest.json` `.clients` (absolute paths). `MINI_CLIENT_TARGETS=` builds none. `--client-only` builds only `bin/mini` and these, writes `provenance.json` of type `minidregg-client-provenance-v1` and `SHA256SUMS`, and no manifest |
| `OUT/bin/minidregg-link-sqlite-store` | Store helper (`native/hyperdocument-link-sqlite-store`) |
| `OUT/bin/minidregg-credential-signature-verifier` | Ed25519 verifier helper (`native/credential-signature-verifier`) |
| `OUT/bin/grain-runtime`, `OUT/bin/grain-provider-bridge` | Durable agent controller and sandbox provider bridge (`native/grain-runtime`) |
| `OUT/bin/mini-inference-scheduler` | Shared inference admission, placement and fairness (`native/inference-scheduler`) |
| `OUT/bin/spk-host`, `OUT/bin/spk-browser-proxy` | Application custody/broker and browser entrance (`native/spk-host`) |
| `OUT/bin/pay-watcher` | Solana payment observer (`native/pay-watcher`) |
| `OUT/bin/mini-discord` | Optional Discord entrance (`native/discord-entrance`) |
| `OUT/run.sh`, `OUT/lib.sh`, `OUT/params.sh`, `OUT/genesis.sh`, `OUT/INTERFACES.md`, `OUT/genesis-params.example.json` | operator scripts and documents, copied from the same archive; `genesis.sh` and the example params come from `native/resource-client/`, the one genesis template the acceptance fixture also uses |
| `OUT/source.tar` | the exact source archive |
| `OUT/provenance.json` | source, toolchains, relative binary paths and hashes, timings (below) |
| `OUT/SHA256SUMS` | `sha256sum` lines for everything above and `logs/source-files.sha256`, relative to `OUT` |
| `OUT/manifest.json` | the journey-format manifest (below) |
| `OUT/logs/` | build log, per-step logs, `source-files.sha256` (every archived file) |
| `OUT/work/` | extracted source, Lean/cargo build trees, mathlib cache. Not needed at run time; the Host build evidence is `OUT/work/host-build/`. |

All concurrent native builds on a host must select the same compiler-seat root.
Its default is `/tmp/minidregg-lean-seats`; operators coordinating multiple
accounts must configure its custody explicitly.
`MINIDREGG_CYCLE_DIR` selects evidence, not additional compiler capacity. The
candidate builder compiles the Host import closure; separately qualify the
required umbrella/assurance targets when those interfaces change.

Rust candidate crates and their path dependencies share the root Cargo workspace
and `Cargo.lock`. Each builder runs Cargo in its own absolute source directory,
with `--locked`, `CARGO_INCREMENTAL=0`, and `--remap-path-prefix` for that source
(`/minidregg`), `$CARGO_HOME` (`/cargo`) and the Cargo target directory
(`/target`). Generated `OUT_DIR` sources also participate in LLVM symbol identity;
remapping their target directory fixes the separately measured SPK difference. Workspace membership makes dependency
identity relative to the workspace root. Source remapping alone does not fix
external path dependency identity: the measured direct grain-runtime builds had
different Cargo path fingerprints and Rust symbol disambiguators. Two cold
workspace builds from different lexical roots produced identical bytes. The
old fixed-symlink helper remains for the read-only pipeline diagnostic; candidate
builders no longer use it. No binary postprocessing is used to obtain identity.

**`manifest.json`** has type `minidregg-candidate-manifest-v2`. It retains the
journey's absolute role paths and SHA-256 pins, and adds `outputs`, keyed by every
relative executable path below `bin/`, including consent, services, the Linux
friend bundle and any cross-compiled clients. Every output records:

```json
{"sha256": "<64 hex>",
 "build": {"sourceTree": "<git rev-parse COMMIT^{tree}>",
           "rustcVerbose": "<builder rustc -vV>",
           "leanToolchain": "<exact lean-toolchain file contents>",
           "cargoLockSha256": {"Cargo.lock": "<64 hex>"},
           "flags": {"rust": {}, "native": {}}}}
```

The actual flags objects are nonempty: Rust records its remaps, release profile,
locked resolution and incremental setting; native records its builder and entry
modules. Native build manifests separately bind the compiled closure. The tree
id comes from the archive commit in the packaging repository, never the current
checkout's HEAD. The packager requires builder toolchain/flag evidence, reads
pins from the source archive, and writes the same output identities into
`provenance.json`. Packaging must run in a repository containing that commit.
Sealed capsules without this evidence refuse and must be rebuilt/repackaged.

`run.sh` requires v2, verifies the pinned provenance and its complete output map,
and hashes **every** output before any `init`, `serve`, `start`, or `sponsor`
launch. A mismatch refuses with `binary NAME sha256 mismatch: manifest X, file Y`.
There is no bypass flag or environment variable. This protects against binary
changes relative to an operator-selected manifest; the manifest is the trust
input, not a cryptographic signature on the publisher. Old manifests refuse.
Re-emit them with `package.py` and complete builder evidence; initialize a fresh
Store for a rebuilt executable family. Existing v1 state descriptors can refer
to a newly emitted v2 manifest only when their Host and helper bindings still
match. Relative output paths stay valid when copying a candidate; absolute role,
client and provenance references in its manifest must be relocated together.

M7 compares every output against an independently built candidate, checks both
sets' actual bytes and compiled inputs, exercises tampered `init` and `serve`,
then initializes, serves, reads through and stops its own Store. Run the plants
`scripts/kn2/plant-m7-tamper.sh CANDIDATE NEW_EVIDENCE_DIR` and
`scripts/kn2/plant-m7-no-verification.sh CANDIDATE NEW_EVIDENCE_DIR`: the latter
removes verification calls only in a temporary `run.sh` and requires M7's tamper
check to fail with its pinned refusal-test message.

**`provenance.json`** (`minidregg-candidate-provenance-v1`):

```json
{"type": "minidregg-candidate-provenance-v1",
 "source": {"commit": "<40 hex>", "archive": "source.tar", "archiveSha256": "<64 hex>",
            "origin": "build.sh | sealed-capsule | <roles manifest origin>",
            "fileList": "logs/source-files.sha256", "fileListSha256": "<64 hex>"},
 "target": "x86_64-linux",
 "toolchains": {"recorded": "build.sh", "leanToolchain": "...", "lean": "...", "lake": "...",
                "mathlibRev": "...", "rustToolchain": "...", "rustc": "...", "cargo": "...",
                "cc": "...", "rustflags": "...", "seconds": {}},
 "binaries": {"host": {"path": "bin/minidregg-host", "sha256": "..."}, "mini": {},
              "store": {}, "verifier": {}, "grainRuntime": {}},
 "abi": {"glibcRequired": "2.39", "binaries": {"mini": {"glibcRequired": "2.39",
         "glibcStrong": [], "glibcWeakOnly": [], "needed": ["libc.so.6"]}}},
 "packaging": {"type": "build.sh | sealed-capsule | <roles manifest origin>"},
 "hostBuildManifest": {"path": "/abs/.../manifest.txt", "sha256": "..."},
 "clients": {"x86_64-unknown-linux-gnu": {"path": "bin/mini", "sha256": "..."}},
 "builtUtc": "..."}
```

Binary paths here are relative to `OUT`.

**One packaging format, one packager.** `deploy/candidate/package.py` writes
every candidate directory: `build.sh` calls it after building (`--roles`, the
binaries already in `OUT/bin`), a lane build on a build box calls it with its own
role manifest (`--roles ROLES.json --source-archive SOURCE.tar`; `deploy/candidate/lane-build.sh
host|consent|rust|pack` is that path: an incremental native build from a warm base, the consent
companion, the Rust roles, and a `pack` that refuses unless no compiled input changed since the
build commits), and a sealed
hbox family is packaged with `--capsule FAMILY_DIR`. Every binary is claimed to
be built from the archive's one commit: `--roles` requires the manifest's
`sourceCommit` to be the archive's commit, and `--capsule` refuses a family any
of whose shipped roles was built at another commit (an "unchanged-role-reuse"
row is a claim, not a build) or whose seal does not cover its manifest.
`.abi` records each ELF's non-weak `GLIBC_*` version needs (`readelf -V`):
`edge/mini/ship.sh` (dregg-infra) refuses a box whose glibc is older than
`.abi.glibcRequired`, and the box's own loader resolves every shipped binary
before publication.

**Reproducing.** Two builds from archives with the same compiled inputs, in
different directories, yielded the same four core SHA-256s in the dated baseline
(measured: see
`docs/evidence/2026-09-30-candidate/`). The journey's M7 step
(`native/resource-client/journey.d/m7.sh`) checks exactly that against a
reference build named by `M7_REFERENCE` (or `.m7Reference` in the manifest).

## 2. Processes

```
supervisor ─ run.sh serve ─exec→ mini serve --host H --config PINNED --socket STATE/public/mini.sock
                                   └─ H PINNED stdio            (one long-lived Host child, stdin/stdout)
                                        ├─ STORE read-to|cas ...  (one short process per durable read/CAS)
                                        └─ VERIFIER verify ...    (one short process per signature check)
clients: mini ... --socket STATE/public/mini.sock   (connect, one request, one reply, close)
```

* `mini serve` owns the socket and one Host child. It handles one request at a
  time. If the Host exits or a reply exceeds its bound the service stops
  (status of that request: uncertain; the client retains the exact call and
  `mini retry` recovers the original outcome).
* SIGTERM to `mini serve` ends it; the Host sees EOF on stdin and exits. A
  systemd unit should use `KillMode=control-group` (the template does).
* The Host and helpers write scratch files through the process temp directory.
  `run.sh` sets `TMPDIR=STATE/tmp` for everything it starts.
* The standalone Store process opens no TCP port. The optional browser proxy,
  provider and entrance services have their own network configuration. Remote access
  (SSH to the Store's account, a forwarded Unix socket, a gateway) is an
  operator decision; the socket protocol below is local and authenticates by
  file-system ownership and the config/Host pins, not by a network handshake.

## 3. The client socket

`STATE/public/mini.sock`, a Unix stream socket.

* Its directory must be owned by the serving account with mode `0700`; the
  socket is `0600`. Only that account can connect.
* Sidecars in the same directory, all owner-private: `mini.lock` (flock; one
  server per socket), `mini.config` (byte copy of the served config; a later
  `serve` with different config bytes is refused), `mini.mode` (`public-v1` or
  `operator-v1`; a public socket is never upgraded to operator mode).
* A stale socket file whose listener is gone is removed at start; a live one
  is refused.
* The socket path must be shorter than 108 bytes (`sockaddr_un`), so
  `STATE` itself must be at most 90 bytes. `run.sh init` refuses a longer one.

**Framing.** Every message in both directions is `u32 little-endian length`
then that many bytes; length is 1 ..= 12,168,333 (Host frame 12,102,760 + 5 +
config bound 65,536 + 32).

**Request envelope** (client → socket):

| bytes | field |
| --- | --- |
| 1 | envelope version: `1`, or `2` (adds the Host pin; `mini` always sends 2) |
| 4 | u32 LE config length (≤ 65,536) |
| n | the pinned config file's exact bytes; must equal what the server serves |
| 32 | (version 2) SHA-256 of the Host executable the client expects |
| 1 | operation byte |
| rest | operation payload (< 12,102,760 bytes) |

**Reply** (socket → client): first byte is the echoed operation byte and the
rest is its result; or `255` followed by a strict `OUTCOME/v4` refusal (below);
or `254` followed by a UTF-8 reason for a socket-level refusal (`config pin
mismatch`, `host image pin mismatch`, `invalid socket envelope`, `operation
unavailable on selected socket`, `host frame exceeds bound`). Deadlines: the
server allows 10 s to receive a request and 10 s to write a reply; the client
waits up to 600 s for a reply.

**Operation allocation and exposure.** The selected source's
[`host-operations.json`](../../protocol/host-operations.json) owns request bytes,
status, purpose and public/operator routes. The registry checker compares it with
Host dispatch and client selectors. A reserved byte is not a callable endpoint.
Consult the named receiver and codec for payload shape; keeping a second manual
wire-version table here would drift from those consumers.

`mini serve-operator` serves a separate owner-private socket with the lifecycle,
dispatch and other operator routes. `mini serve-public-proxy` supplies public
access through that private Host using the registry's allowed public routes. The
standalone `run.sh` recipe above does not provision this composed topology. A
hosted installation must select it explicitly and bind controllers, payment
observers and app custodians to the correct socket.

**Host stdio.** `mini serve` speaks the same frames to the Host child without
the envelope: `u32 LE length` then `operation byte + payload`; the Host
replies `u32 LE length` then `operation byte (or 255) + payload`. EOF at a frame
boundary ends the Host normally; a truncated, oversized or unknown frame ends
it. Direct CLI use (`minidregg-host CONFIG COMMAND ARGS`) is how `init` runs
`profile`, `author genesis`, `genesis` and `bootstrap`; the full command list is
the Host's usage text (`minidregg-host` with no arguments).

## 4. Wire codecs

All binary messages are Lean `StreamCodec` values (`Compiler/Tower256ConcreteBackend.lean`),
decoded strictly: a message is accepted only if re-encoding the decoded value
gives back exactly the input bytes.

| primitive | encoding |
| --- | --- |
| nat | little-endian base-255 digits (each 0..254), then byte `0xFF`; zero is just `0xFF` |
| digest | a nat |
| bytes | nat length, then the raw bytes |
| list | nat count, then the items |
| product (a, b) | a's encoding then b's; no separator |
| sum | tag byte `0` (left) or `1` (right), then the payload; wider sums nest to the right |
| bool | one byte, `1` true, `0` false |
| framed message | ASCII magic, then the stream encoding |

Messages (`Compiler/NativeHostCodec.lean`, `Compiler/NativeObservationCodec.lean`):

* `DREGG/NATIVE-HOST/SIGNED-CALL/v3` — sum of: birth(bytes) | invoke(command
  bytes, list target envelopes, list observe envelopes, authority envelope) |
  install(bytes) | delegate(bytes) | revoke(bytes).
* `DREGG/NATIVE-HOST/DRAFT/v3` — sum of: birth(descriptor bytes, list capability) |
  invoke(command) | install(subject, control capability, declaration) |
  delegate(command) | revoke(command).
* `DREGG/NATIVE-HOST/SIGNING-PLAN/v4` — domain digest, semantics digest, world
  root digest, height nat, finalized draft, list of slots (role nat, index
  nat, canonical header bytes). The client signs each header with Ed25519. A
  signed header (v2) carries the plan's authority footprint and `validUntil`
  height. v3 refuses.
* `DREGG/NATIVE-HOST/OUTCOME/v4` — sum of: confirmed(confirmation, receipt) |
  refused(reason byte, phase bytes, detail bytes, optional law clause) |
  contention | absent | unavailable(detail) | uncertain(detail). Confirmation is
  installed / recoveredAfterUncertainResponse / replayed. Receipt is
  transaction id, event id, accepted count, world root (all digests/nats). The
  accepted count counts entries through that transaction, not the current tip.
  The reason is one byte of the closed `RefusalReason`
  (`Compiler/RefusalReason.lean`); a law refusal may also name the failing
  clause (`LawLeaf`: path, the committed clause as policy-record tokens, the
  slot's before/after values). v1, v2 and v3 frames are refused, never
  reinterpreted. On a Host refusal `mini` prints `refused: <reason>: <text>`
  and exits 3.
* `DREGG/NATIVE-HOST/OBSERVE-INTENT/v3` — subject, nonce, purpose (query(kind,
  target, view: resource | policy | capability) or prepare(draft)), list of
  grants (kind, target, capability).
* `DREGG/NATIVE-HOST/OBSERVE-CHALLENGE/v6` — intent, domain, semantics,
  federation, world root, authority root, height, the deployment clock at that
  height (`now`, `slot`: the clock the read's law is judged at), list of
  canonical signing headers. v5 refuses.
* `DREGG/NATIVE-HOST/OBSERVE-SIGNED/v6` — challenge, list of 64-byte signatures
  (one per header). v5 refuses.

A refusal's `phase` is a short source-selected word (`observation`, `prepare`,
`wire`, `replay`, ...). The client prints it as
`host refused COMMAND; encoded refusal: <hex of OUTCOME/v4>`. Before a
signature verifies, only `unknown-key` and `stale-root` are named (anything
else is `undisclosed`); a blind submission's refusal is always `undisclosed`.

## 5. Host ↔ helper protocols

The Host runs each helper as a child process with arguments only; it reads
stdout, stderr and the exit status.

**Store helper** (`storageBinary`, root `storageRoot`):

| call | success | other outcomes |
| --- | --- | --- |
| `STORE read-to ROOT OUT` | exit 0, empty stdout/stderr, image bytes in `OUT` | exit 3 = no image yet; anything else = read failed |
| `STORE cas ROOT EXPECTED\|- POST` | exit 0, stdout `Installed` or `AlreadyPresent`, empty stderr | exit 4 with empty stdout = conflict; anything else = **uncertain** |

`-` means "expect no image". The whole durable image (genesis plus every
accepted entry) is **one** record in `ROOT/forward-link.sqlite3`, replaced by
compare-and-swap; a record is at most 64 MiB. The helper also has test-only
commands (`cas-crash`, `publish-crash`, `publish-hold`) that the Host never
calls in production.

**Signature verifier** (`signatureBinary`): `VERIFIER verify PUBLIC FRAME SIG`
with a 32-byte raw public key file, the frame file and a 64-byte raw signature
file. Exit 0 with stdout exactly `verified\n` or `invalid\n` and empty stderr;
anything else is an error, never an acceptance. Ed25519 `verify_strict`; the
frame is opaque to the helper.

## 6. State directory (`run.sh init --state STATE`)

Everything is created owner-only (`umask 077`, directories `0700`).

| path | written by | content |
| --- | --- | --- |
| `state.json` | init | `minidregg-candidate-state-v1`: absolute manifest path, Host SHA-256, pinned-config SHA-256, creation time. Every later command re-checks the manifest pins, this Host pin, and the helper paths in the pinned config. |
| `genesis-params.json` | init | copy of the operator's params (schema below) |
| `keys/sponsor.key`, `keys/sponsor.pub`, `keys/sponsor.pub.hex` | `mini keygen` | the genesis sponsor's key (format in §8) |
| `keys/clock.key`, `keys/clock.pub`, `keys/clock.pub.hex` | `mini keygen` | the clock subject's key: its only authority is `C_tick`; its workspace is made with `mini clock --action init` (deploy: `/var/lib/mini/clock`) |
| `clock-birth-context.json` | init | the clock subject's birth context (the factory law refuses it every birth) |
| `operator.json` | init | Host operator config (schema below) |
| `profile.json` | `minidregg-host operator.json profile` | semantics digest and metering profile |
| `genesis.json` | init | genesis source (schema below) |
| `deployment/` | `mini bootstrap` | `genesis-source.json`, `operator-config.json` (copies), `genesis-source.bin`, `genesis.bin`, `pinned-config.json`, `profile.json`, `description.json` |
| `store/forward-link.sqlite3` | Store helper | the durable image |
| `sponsor-birth-context.json` | init | sponsor's birth context (factory observe grant + spend account) |
| `sponsor/` | `run.sh sponsor` | the sponsor's participant workspace (`workspace.json`, `refs/`, `proposals/`, `attempts/`, `sources/`) |
| `namespace/` | sponsor workspace | durable identity reservations for names the sponsor allocates |
| `public/` | serve | `mini.sock`, `mini.lock`, `mini.config`, `mini.mode`, `server.pid` (`start` only) |
| `tmp/` | Host, helpers | scratch (`TMPDIR`) |
| `logs/` | run.sh | bootstrap/sponsor output, `serve.log` (`start` only) |

**Genesis params** (`minidregg-candidate-genesis-params-v1`; every value a JSON
integer, 0 ≤ n < 2^53): `domain federation factoryId resourceBookId
authorityCellId issuer ownerBudget lifetime tariffBase tariffPerBirth
tariffPerGrant tariffPerInitialPayloadByte collector asset genesisHeight
issuerEpoch factoryControllerCapability`, `sponsor {subject keyId keyEpoch
activeFrom activeUntil accountId spendCapabilityId controlCapabilityId
factoryObserveCapabilityId initialBalance}`, `clock {subject keyId keyEpoch
activeFrom activeUntil accountId spendCapabilityId controlCapabilityId
factoryObserveCapabilityId tickCapabilityId genesisNow maxStepSeconds}` (the dedicated clock subject,
distinct from the sponsor; `tickCapabilityId` is its `C_tick`; `genesisNow` the genesis's Unix
second and `maxStepSeconds` the most one clock tick may advance, both positive), and
`meterAllowance` with the ten keys `incidences turnBytes memoryTouches witnessBytes proofWork
storageBytes networkBytes sideEffectCount feeDebit leaseByteBlocks`.
`genesis-params.example.json` holds the values the recorded qualification runs
used, except the genesis clock: its `clock.genesisNow` and `clock.maxStepSeconds` are `null`
(unfilled), and `run.sh init` and `genesis.sh` refuse an unfilled or non-positive value
(`clockStepBoundInvalid`, `clockGenesisNowInvalid`). They are filled AT GENESIS TIME by the one
helper, `params.sh fill-genesis PARAMS.json` (in place: `genesisNow` = now or `$GENESIS_NOW`,
`maxStepSeconds` = `$MAX_STEP_SECONDS` or 300). It never repairs an explicit bad value (0
refuses) and never re-dates a filled file (a present value other than the one it would write
refuses). A driver that hand-writes a `mini bootstrap --source` file calls
`params.sh fill-source SOURCE.json` (`clockGenesisNow`, `clockMaxStepSeconds`, decimal strings)
instead; no driver writes a clock value itself. The sponsor and the clock subject are the identities genesis names; every
later participant is enrolled through the client and receives Host-allocated
identifiers. `genesis.sh PARAMS SPONSOR_PUBLIC_HEX CLOCK_PUBLIC_HEX HOST STORE
VERIFIER DIR` takes both public keys.

**`operator.json`** (Host `Settings`, `Host/Main.lean`): the 16 genesis numbers
above that the Host needs (`domain federation factoryId resourceBookId
authorityCellId issuer ownerBudget lifetime tariffBase tariffPerBirth
tariffPerGrant tariffPerInitialPayloadByte collector asset genesisHeight`),
`expectedSeed: 0`, and three absolute paths: `storageBinary`, `storageRoot`,
`signatureBinary`. Optional sections (`fnGateway fnPoll fnReplyPoll
fnReplyCatalog continuityProviderResourceId providerMetering providerServices
grainBirthTariff completionCustodianKey completionManagement
residentBeginManagement residentClaimManagement agentDispatchFixed
agentLifetimeDispatchFixed agentLifetimeDispatchServices`) stay absent/null in
this candidate.

**`genesis.json`** (genesis source): the same coordinates as decimal strings,
`expectedSemantics` (from `profile.json`), `issuerEpoch`, `factoryPredicate`
(`{"type":"all","predicates":[]}`), one `enrollments` entry for the sponsor
(`key {keyId keyEpoch algorithm:"1" subject publicKey(hex) activeFrom activeUntil
revoked:false}`, `accountId spendCapabilityId controlCapabilityId
factoryObserveCapabilityId initialBalance accountPredicate`),
`factoryControllerSubject`, `factoryControllerCapability`, `meterAllowance`,
and `clockTickers` (`[{subject, capability}]`: the clock subject first; genesis
installs the clock cell's law `all [request/verb = 7 (tickClock), request/subject
∈ tickers]`, one `C_tick` per ticker on the clock cell, and confines the factory
law against every ticker). The clock subject has a second enrollment (balance
0). Genesis source frame `GENESIS-SOURCE/v3`; v2 refuses.
The Host refuses a genesis whose coordinates differ from `operator.json`.

**`pinned-config.json`** is `operator.json` plus the genesis `expectedSeed`
the Host derived. It is the config every client presents: the socket compares
its bytes exactly, and the Host checks the image it opens against its
`expectedSeed`. It names the helpers by absolute path, so the candidate directory
must stay where it was when `init` ran (or re-run `init` on a new Store).

## 7. Supervision (`run.sh`)

* `serve` validates every output hash, the state's Host pin and the helper
  paths in the pinned config, sets `TMPDIR`, then `exec`s `mini serve`. Use it
  under systemd (`run.sh unit --state STATE` prints a unit: `Type=simple`,
  `Restart=on-failure`, `KillMode=control-group`, `UMask=0077`,
  `NoNewPrivileges=yes`, `PrivateTmp=yes`) or any other supervisor.
* `start`/`stop`/`status` are a minimal supervisor for hosts without one:
  `start` backgrounds `serve`, records `public/server.pid`, and waits (≤ 120 s)
  for the socket and the `mini: serving` line in `logs/serve.log`; `stop` only
  signals a pid whose command line is `mini serve ... --socket STATE/public/mini.sock`,
  and waits (≤ 60 s) for it and its Host child to exit.
* `sponsor` creates the genesis sponsor's workspace and imports the factory
  reference (needs the Store serving); it is idempotent.

## 8. Key and workspace files

* **Secret key**: exactly 32 raw bytes (Ed25519 seed), a regular file owned by
  the invoking user with no group/other permission bits. The client refuses
  any other shape (symlink, wrong owner, `0644`, wrong length).
* **Public key**: exactly 32 raw bytes. `mini keygen` also prints it as hex.
* Keys never enter the Host: the Host authors headers and plans, the client
  signs them locally, the Host assembles detached signatures.
* **Workspace** (`mini workspace --action init`): `workspace.json`
  (`minidregg-participant-workspace-v1`: absolute Host, config, socket and key
  paths, subject, optional enrollment/birth context/namespace root). A
  workspace is bound to one Store and one key; moving the Store or the key
  breaks it.
* **Attempts**: every write keeps `intent.json`, `challenge.json`, the exact
  `call.bin` before submission, and `outcome.json`. `mini retry --attempt DIR
  --mode submit|lookup` resends the exact call or looks it up; an admitted call
  comes back `replayed` with its original receipt, never as a second effect.
* **References** (`refs/NAME.json`, `minidregg-participant-reference-v1`;
  delegation hand-off `recipient-reference.json`,
  `minidregg-delegated-reference-v1`): `authority: "hint-only"`. Names are
  local hints; the Host decides use from signed observations and current law.

* **Signing consent**: the client signs only after a locally selected consent
  provider reconstructs the bytes; `MINI_LOCAL_HOST`, `MINI_CONSENT_HOST` and
  `MINI_CONSENT_CONFIG` select it (absolute paths, all three together). Without
  them the client refuses to sign. Details: `deploy/shell/README.md`,
  "Signing consent: the three variables".

## 9. What the operator decides

- **fn image.** Mini at or after `fn frames!` (lane/plat-fn-frames) requires an fn with `--frame` on identity, status, position, ack and poll, and refuses an fn without it by name ("this fn has no --frame"). Production deploy waits for fn's converged image; until then the production fn pin is d420a2b5 and the `--frame` build (fn 6679dae0e) is the journeys' and pipeline's DEV pin. Both are recorded in `protocol/fn/images.json`.

1. **Placement and paths**: which machine and Unix account hold the candidate,
   each Store's state directory (at most 90 bytes, for the socket), and the
   sponsor key. All scripts take them as
   arguments; nothing defaults to a shared or temporary location.
2. **Genesis coordinates** (`genesis-params.json`): identifiers, tariffs,
   budgets, lifetimes, meter allowances and the sponsor's validity window. They
   are fixed for the life of the Store; changing them is a new Store.
3. **Custody of the sponsor key**: it authorizes every enrollment and owns the
   factory control capability. The candidate generates it inside the state
   directory; moving it elsewhere means editing the sponsor workspace's
   `workspace.json` key path.
4. **Supervision**: systemd (`run.sh unit`) or another supervisor running
   `run.sh serve`; restart policy; log retention.
5. **Access**: public and operator Unix sockets retain owner-only custody.
   Remote members enter through the forced Mini-shell/proxy protocol; they do
   not need Unix shell accounts. See [shell deployment](../shell/README.md) and
   its [operator guide](../shell/OPERATOR.md). Member credentials and signing
   authority remain distinct from the service account running the transport.
   The standalone bootstrap does not install SSH or browser ingress policy.
6. **Backups**: the state directory holds several owners' records — the durable
   image (`store/`), the sponsor's workspace and attempts, namespace
   reservations, keys. Participants' own workspaces and keys live wherever they
   keep them. Restoring one of these does not restore the others consistently.
   Back up with the service stopped.
7. **Capacity**: measure the selected family with its real workload, population,
   admission limits and resource settings. The September 29 measurements in
   `docs/evidence/2026-09-30-candidate/` describe that earlier source and are not
   current capacity limits. Distinguish cold history audit, cached reopen,
   interactive writes, app work and provider contention. Fixture populations do
   not define the number of platform users; configured limits must produce
   explicit admission/refusal and allow normal continued operation.
8. **Upgrades**: current service deployment uses full teardown/rebuild from the
   selected family, with repeatable provisioning. Legacy migration or rolling
   transition is not a release prerequisite. Ordinary restart, exact retry,
   payment conservation and backup/restore still require their own evidence.
   Preserve old state deliberately before teardown when its data is wanted.

## 10. Hosted service composition

This build ships the controller/provider bridge, scheduler, SPK hosting/browser
proxy, payment watcher and optional Discord entrance. Their operator contracts
are in [Hermes](../hermes/README.md), [SPK hosting](../spk-host/README.md),
[payments](../pay/README.md) and [member access](../shell/README.md), together with
the matching source's command/config parsers. Deployment unit templates and
root-owned service provisioning must be pinned separately when supplied by the
infrastructure repository.

Qualification belongs to the actual configuration and executable family: one
Store/world shared by enrolled members, residents and apps; current authority and
independent budgets; concurrent admission; ordinary crash/retry; and a usable
checkpoint/resume path. Component or fixture success alone does not establish
that combined service. Cross-node operation and participant hosting similarly
require their own configured topology and receiving evidence.
