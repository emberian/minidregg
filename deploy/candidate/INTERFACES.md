# Mini candidate: interfaces an operator depends on

This directory builds and runs one Mini Store from source. Everything below is
what the procedure reads, writes, executes or listens on. Anything not listed
here is not part of the candidate contract.

Procedure, from a clean Linux x86-64 account:

```sh
git clone https://github.com/emberian/minidregg && cd minidregg && git checkout <commit>
deploy/candidate/build.sh --out /srv/mini/candidate-<commit>          # binaries + manifest
C=/srv/mini/candidate-<commit>
cp $C/genesis-params.example.json /srv/mini/genesis-params.json      # edit: operator decisions
$C/run.sh init  --manifest $C/manifest.json --params /srv/mini/genesis-params.json --state /srv/mini/store-a
$C/run.sh start --state /srv/mini/store-a                             # or: run.sh unit ... | systemd
$C/run.sh sponsor --state /srv/mini/store-a
$C/journey.sh --state /srv/mini/store-a --out /srv/mini/journey-1     # only on a Store made for it
$C/run.sh stop  --state /srv/mini/store-a
```

`/srv/mini/...` stands for any directory the operator chooses. No script
writes outside `--out`, `--state` or the journey `--out`, except the toolchain
managers' own caches (below).

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
| Lean packages (mathlib and its dependencies, `uwueave`) | `lake-manifest.json` revisions | their git URLs in `lake-manifest.json` |
| mathlib `.olean` + generated C for that revision | the mathlib revision | the mathlib artifact cache (`lake exe cache get`), stored in `OUT/work/mathlib-cache` |
| Rust toolchain | `rust-toolchain.toml` | rustup's dist server (`--no-self-update`) |
| Rust crates | each crate's `Cargo.lock` (`--locked`) | crates.io, cached in `$CARGO_HOME` |

**Outputs.**

| path | what |
| --- | --- |
| `OUT/bin/minidregg-host` | Lean-authored native Host, built by `scripts/build-native-host.sh` (bounded, serialized Lean compiler; seat directory `OUT/work/host-cycle`) |
| `OUT/bin/mini` | client (`native/resource-client`) |
| `OUT/bin/minidregg-link-sqlite-store` | Store helper (`native/hyperdocument-link-sqlite-store`) |
| `OUT/bin/minidregg-credential-signature-verifier` | Ed25519 verifier helper (`native/credential-signature-verifier`) |
| `OUT/run.sh`, `OUT/journey.sh`, `OUT/lib.sh`, `OUT/INTERFACES.md`, `OUT/genesis-params.example.json` | operator scripts and documents, copied from the same archive |
| `OUT/source.tar` | the exact source archive |
| `OUT/SHA256SUMS` | `sha256sum` lines for everything above, relative to `OUT` |
| `OUT/manifest.json` | see below |
| `OUT/logs/` | build log, per-step logs, `source-files.sha256` (every archived file) |
| `OUT/work/` | extracted source, Lean/cargo build trees, mathlib cache. Not needed at run time; the Host build evidence is `OUT/work/host-build/`. |

Rust binaries are built with `--remap-path-prefix` for the source tree
(`/minidregg`) and `$CARGO_HOME` (`/cargo`), so their bytes do not depend on
where the operator unpacked the source or keeps the registry. The Host's bytes
do not contain build paths.

**`manifest.json`** (`minidregg-candidate-manifest-v1`):

```json
{"type": "minidregg-candidate-manifest-v1",
 "source": {"commit": "<40 hex>", "archive": "source.tar", "archiveSha256": "<64 hex>",
            "origin": "git-archive-HEAD | supplied-archive", "fileListSha256": "<sha of logs/source-files.sha256>"},
 "target": "x86_64-linux",
 "toolchains": {"leanToolchain": "...", "lean": "...", "lake": "...", "mathlibRev": "...",
                "rustToolchain": "...", "rustc": "...", "cargo": "...", "cc": "...", "rustflags": "..."},
 "binaries": {"host":     {"path": "bin/minidregg-host", "sha256": "..."},
              "mini":     {"path": "bin/mini", "sha256": "..."},
              "store":    {"path": "bin/minidregg-link-sqlite-store", "sha256": "..."},
              "verifier": {"path": "bin/minidregg-credential-signature-verifier", "sha256": "..."}},
 "hostBuildManifest": {"path": "work/host-build/manifest.txt", "sha256": "..."},
 "seconds": {"leanPackagesAndMathlibCache": 0, "nativeHost": 0, "rust": 0, "total": 0},
 "builtUtc": "..."}
```

Paths are relative to the manifest's directory. Every consumer (`run.sh`,
`journey.sh`, `native/resource-client/newparticipant-acceptance.sh`) resolves
the four binaries through the manifest and refuses one whose SHA-256 differs.

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
* No process opens a network socket. There is **no TCP port**. Remote access
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
rest is its result; or `255` followed by a strict `OUTCOME/v1` refusal (below);
or `254` followed by a UTF-8 reason for a socket-level refusal (`config pin
mismatch`, `host image pin mismatch`, `invalid socket envelope`, `operation
unavailable on selected socket`, `host frame exceeds bound`). Deadlines: the
server allows 10 s to receive a request and 10 s to write a reply; the client
waits up to 600 s for a reply.

**Operations on the public socket** (`mini serve`). The server forwards only
these; everything else is `254 operation unavailable`:

| op | name | payload | reply payload |
| --- | --- | --- | --- |
| 0 | describe | empty | JSON description of the served image |
| 1 | prepare (authorized) | `OBSERVE-SIGNED/v3` whose intent purpose is a draft | `SIGNING-PLAN/v3` |
| 2 | submit | `SIGNED-CALL/v3` | `OUTCOME/v1` |
| 3 | lookup | `SIGNED-CALL/v3` | `OUTCOME/v1` (`absent` if never admitted) |
| 4 | challenge | `OBSERVE-INTENT/v3` | `OBSERVE-CHALLENGE/v3` |
| 5 | query (authorized) | `OBSERVE-SIGNED/v3` whose purpose is a query | the view bytes |
| 6 | profile | empty | JSON metering/semantics profile |
| 7 | author | kind frame: u16 LE kind length, UTF-8 kind, UTF-8 JSON source | canonical bytes |
| 8 | inspect | kind frame with binary input | JSON |
| 9 | signatures | UTF-8 JSON list of hex signatures | canonical signature list |
| 10 | observe-assemble | pair: u32 LE length, challenge bytes, signature list | `OBSERVE-SIGNED/v3` |
| 11 | assemble | pair: signing plan, signature list | `SIGNED-CALL/v3` |
| 12–19 | fn consumer/reply/catalog/outbox, provider continuity and metering | per service | only when the matching optional config section is set; otherwise a refusal |
| 20, 21 | selected-release submit / lookup | ingress | `OUTCOME/v1` |
| 28, 29 | application share-issue submit / lookup | ingress | `OUTCOME/v1` |
| 30, 31 | current application / session birth intent | JSON object ≤ 256 KiB | intent bytes |
| 86 | participant key enrollment plan | pair: signed factory observation, command | plan |
| 87 | participant key enrollment assembly | pair: plan, pair(sponsor sig 64 B, possession sig 64 B) | ingress |
| 88, 89 | participant key enrollment submit / lookup | ingress | `OUTCOME/v1` |
| 91 | current resource birth intent | pair: signed observation, JSON source ≤ 256 KiB | intent bytes |

`mini serve-operator` serves a separate owner-private socket (same framing,
peer UID must equal the server's) with the lifecycle, dispatch, share-issue,
fn-namespace/frontier and agent-reserve routes. The candidate does not start
one; the bake-off journey needs none.

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
* `DREGG/NATIVE-HOST/SIGNING-PLAN/v3` — domain digest, semantics digest, image
  boundary digest, height nat, finalized draft, list of slots (role nat, index
  nat, canonical header bytes). The client signs each header with Ed25519.
* `DREGG/NATIVE-HOST/OUTCOME/v1` — sum of: confirmed(confirmation, receipt) |
  refused(phase bytes, detail bytes) | contention | absent | unavailable(detail) |
  uncertain(detail). Confirmation is installed / recoveredAfterUncertainResponse /
  replayed. Receipt is transaction id, event id, accepted count, image boundary
  (all digests/nats). The accepted count counts entries through that
  transaction, not the current tip.
* `DREGG/NATIVE-HOST/OBSERVE-INTENT/v3` — subject, nonce, purpose (query(kind,
  target, view: resource | policy | capability) or prepare(draft)), list of
  grants (kind, target, capability).
* `DREGG/NATIVE-HOST/OBSERVE-CHALLENGE/v3` — intent, domain, semantics,
  federation, image boundary, height, list of canonical signing headers.
* `DREGG/NATIVE-HOST/OBSERVE-SIGNED/v3` — challenge, list of 64-byte signatures
  (one per header).

A refusal's `phase` is a short source-selected word (`observation`, `prepare`,
`wire`, `replay`, ...). The client prints it as
`host refused COMMAND; encoded refusal: <hex of OUTCOME/v1>`. Every
authorization failure at observation or preparation currently has the same
detail, `observation refused`.

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
| `state.json` | init | `minidregg-candidate-state-v1`: absolute manifest path, Host SHA-256, pinned-config SHA-256, creation time. Every later command re-checks the Host and helper hashes against it. |
| `genesis-params.json` | init | copy of the operator's params (schema below) |
| `keys/sponsor.key`, `keys/sponsor.pub`, `keys/sponsor.pub.hex` | `mini keygen` | the genesis sponsor's key (format in §8) |
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
authorityCatalogueId issuer ownerBudget lifetime tariffBase tariffPerBirth
tariffPerGrant tariffPerInitialPayloadByte collector asset genesisHeight
issuerEpoch factoryControllerCapability`, `sponsor {subject keyId keyEpoch
activeFrom activeUntil accountId spendCapabilityId controlCapabilityId
factoryObserveCapabilityId initialBalance}`, and `meterAllowance` with the ten
keys `incidences turnBytes memoryTouches witnessBytes proofWork storageBytes
networkBytes sideEffectCount feeDebit leaseByteBlocks`.
`genesis-params.example.json` holds the values the recorded qualification runs
used. The sponsor is the only identity genesis names; every later participant
is enrolled through the client and receives Host-allocated identifiers.

**`operator.json`** (Host `Settings`, `Host/Main.lean`): the 16 genesis numbers
above that the Host needs (`domain federation factoryId resourceBookId
authorityCatalogueId issuer ownerBudget lifetime tariffBase tariffPerBirth
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
`factoryControllerSubject`, `factoryControllerCapability`, `meterAllowance`.
The Host refuses a genesis whose coordinates differ from `operator.json`.

**`pinned-config.json`** is `operator.json` plus the genesis `expectedSeed`
the Host derived. It is the config every client presents: the socket compares
its bytes exactly, and the Host checks the image it opens against its
`expectedSeed`. It names the helpers by absolute path, so the candidate directory
must stay where it was when `init` ran (or re-run `init` on a new Store).

## 7. Supervision (`run.sh`)

* `serve` validates the manifest hashes, the state's Host pin and the helper
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

## 9. What the operator decides

1. **Placement and paths**: which machine and Unix account hold the candidate,
   each Store's state directory, and the sponsor key. All scripts take them as
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
5. **Access**: who can reach the socket. The socket and its directory are
   owner-only, so every client (sponsor, participants, agents) currently runs as
   the Store's Unix account on the Store's machine; group or other-user access
   is refused by design. There is no network listener. Letting participants on
   other machines or under other accounts in needs an operator-chosen entrance
   (for example an SSH forced command or a gateway that speaks this protocol),
   and that entrance is not part of this candidate.
6. **Backups**: the state directory holds several owners' records — the durable
   image (`store/`), the sponsor's workspace and attempts, namespace
   reservations, keys. Participants' own workspaces and keys live wherever they
   keep them. Restoring one of these does not restore the others consistently.
   Back up with the service stopped.
7. **Capacity**: measured on one development machine (bake-off 2026-09-29):
   signed write ~2.6 s at 10 records, ~13 s at 100, ~25 s at 150; cold reopen
   ~5 s at 10, ~121 s at 100, ~243 s at 150; Host RSS ~750 MB at ~100 records;
   the Host is CPU-bound and single-threaded per request. A declared resource
   page holds at most 4 scalar entries. The whole image is one ≤ 64 MiB SQLite
   record. Size a Store for tens to low hundreds of accepted records, not
   thousands.
8. **Upgrades**: a state directory is pinned to one Host image; a new Host
   build means a new candidate directory and, with this candidate, a new Store.
   There is no migration path.

## 10. Not in this candidate

fn transport and selected release across nodes, the operator socket, Hermes /
grain runtime agents, `spk-host` application hosting, inference, and any
network entrance. Each has its own interfaces and qualification record.
