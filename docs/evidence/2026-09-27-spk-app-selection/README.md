# Signed SPK selection for browser and agent acceptance

2026-09-27. This is an **artifact inspection**, not a grain launch. No package executable ran. Public SPKs were downloaded to `/tmp`, checked against the [Sandstorm catalog index](https://app-index.sandstorm.io/apps/index.json), and decoded with an isolated Rust harness using Bread's actual SPK, Cap'n Proto wire and manifest parsers. The harness compiled with `CARGO_BUILD_JOBS=2`; it did not build either full repository. The four small files in [`signed-gitweb/`](signed-gitweb/) were copied byte-for-byte from the verified GitWeb archive, not from GitHub. Root owns the eventual private Linux run and its separate evidence.

## Selection

**GitWeb 0.0.10** is the best first package for an ordinary browser view plus an agent-callable API. A Git commit pushed by an agent through Git smart HTTP should become visible as a file and commit in the GitWeb browser UI. This is a source-grounded acceptance recipe; no push, browser session, token or Mini bridge has yet been exercised. GitWeb's browser interface is a repository viewer, so it does not demonstrate human editing inside the browser. Davros below is the alternative if browser-side mutation is required.

### Catalog and signed package identity

| Field | Recorded value |
|---|---|
| Catalog app | `GitWeb`, version `0.0.10`, version number `10` |
| Catalog App ID | `6va4cjamc21j0znf5h5rrgnv0rpyvh1vaxurkrgknefvj0x63ash` |
| Catalog package ID | `2bbfe6d3c705dfb0696905ecd9c1d00d` |
| Public [package URL](https://app-index.sandstorm.io/packages/2bbfe6d3c705dfb0696905ecd9c1d00d) | 14,045,864 bytes |
| Full package SHA-256 | `2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa` |
| xz uncompressed size | 73.8 MiB; within Bread's default 256 MiB decompression cap |
| Signed App ID | `6va4cjamc21j0znf5h5rrgnv0rpyvh1vaxurkrgknefvj0x63ash`, exactly the catalog ID |

Bread's copied `Spk::parse` verified the package's Ed25519 signature and archive hash with its **default** limit. The parsed manifest and 576-byte `sandstorm-http-bridge-config` are signed archive members. Their SHA-256 hashes are `3ef23992c6ee79e5b684cec632d4552c5b34889348ae63acaaedb42b9616024f` and `49d196f64ca2ce672a378581a8376ada53b27614bba522bbaec042237f0e70a2`, respectively. The manifest says `appVersion=10`, `appMarketingVersion=0.0.10`, with:

| Grain phase | Signed command | Signed environment |
|---|---|---|
| New | `/sandstorm-http-bridge 10000 -- /bin/sh start.sh` | `PATH=/usr/local/bin:/usr/bin:/bin` |
| Continue | `/sandstorm-http-bridge 10000 -- /bin/sh continue.sh` | `PATH=/usr/local/bin:/usr/bin:/bin` |

The signed bridge config declares `apiPath="/repo.git/"`, no Powerbox APIs, permissions named `read` and `write`, and roles named `guest` and `developer`. The [publisher package definition](https://github.com/dwrensha/gitweb-sandstorm/blob/master/.sandstorm/sandstorm-pkgdef.capnp) assigns `guest=[read]` and `developer=[read,write]`; these role bit assignments were read from that source, while the signed binary config independently established its permission/role names and API path. Package App ID, package hash, manifest and bridge configuration do **not** by themselves prove successful execution.

### What the signed application image contains

The signed [`start.sh`](signed-gitweb/start.sh) creates `/var/repo.git` as a bare repository, enables Git HTTP receive-pack, installs a post-receive hook and then calls `continue.sh`. The signed [`continue.sh`](signed-gitweb/continue.sh) starts `fcgiwrap` and `nginx`. The signed [`nginx.conf`](signed-gitweb/nginx.conf) routes `/repo.git/*` to `/usr/lib/git-core/git-http-backend`. It uses the bridge-provided `X-Sandstorm-Permissions` header to allow fetch with `read` and receive-pack/push with `write`, returning 403 when those checks fail. GitWeb's browser pages are served at `/` / `/gitweb.cgi`. Its signed [`sandstorm.js`](signed-gitweb/sandstorm.js) asks Sandstorm's offer-template API for a Git clone URL and credential instructions. These four signed files each matched the corresponding files in the [publisher's repository](https://github.com/dwrensha/gitweb-sandstorm) byte-for-byte when fetched on 2026-09-27; no release tag was published, so the signed files remain the authority.

| Signed excerpt | SHA-256 |
|---|---|
| [`nginx.conf`](signed-gitweb/nginx.conf) | `cc755b1f8f03fc910c45d96678921397be7d132a389e0aceae4bda8338b2cd23` |
| [`start.sh`](signed-gitweb/start.sh) | `725b22268bb4fa7c2c8ef5348ba2c6cdcd123171dea9afd0d4fa0568f84452c9` |
| [`continue.sh`](signed-gitweb/continue.sh) | `6d571a2e3a503b822da8df3a29524548fae3f84ba87996ae6841bb1d793a3370` |
| [`sandstorm.js`](signed-gitweb/sandstorm.js) | `b37eae1cdab610d2df4ab5cc491c125d2fb8a722d6a51171137f61447f99d635` |

Archive path audit found 25 symlinks, zero duplicate names and zero dot/slash name components. Three symlink targets are absolute **within the package chroot**: `etc/localtime → /usr/share/zoneinfo/GMT+0`, `lib64/ld-linux-x86-64.so.2 → /lib/x86_64-linux-gnu/ld-2.24.so`, and `usr/lib/ssl/openssl.cnf → /etc/ssl/openssl.cnf`. Top-level `/dev`, `/proc`, `/tmp` and `/var` are directory entries. A materializer that rejects all absolute symlinks would reject this real package; resolving them against the package root is necessary. This path audit does not establish that the runtime mounts and Linux loader work.

### Exact browser/API handoff to qualify

The [Sandstorm HTTP API contract](https://docs.sandstorm.io/en/latest/developing/http-apis/) validates the external token at the platform gateway, strips it, adds Sandstorm permission headers, and prefixes inbound API paths with `apiPath`. For this package, an external API request `GET /info/refs?service=git-upload-pack` must reach the application as `GET /repo.git/info/refs?service=git-upload-pack`. Git smart HTTP also needs `POST /git-upload-pack`; push needs `GET /info/refs?service=git-receive-pack` and `POST /git-receive-pack`. The query string, HTTP method, request body, response status and Git content types must survive the Mini ingress and bridge. Browser session paths remain unprefixed `/` and `/gitweb.cgi`. Mini must derive `X-Sandstorm-Permissions` from the authenticated session or API grant and must not trust a caller-provided copy. The package's own nginx config then applies its `read`/`write` gate.

The shortest proposed two-participant check is: create a private GitWeb grain and open it in the browser; grant the agent `developer` (`read,write`) API access; have the agent push a small commit over smart HTTP; refresh GitWeb in the browser and inspect the commit/file; attempt a push with a `guest` (`read`) token and require refusal. The signed UI offers Basic-auth Git credentials, while Sandstorm's API also documents Bearer tokens. This is a proposed test, not an observed result. The exact Mini token/role issuance path, API prefixing, permission injection, Git bridge behavior and writable `/var` mount remain runtime obligations.

## Compared packages

| Package | Signed identity and size | Declared interface / observed obstacle |
|---|---|
| [sntfy v2.28.0-sandstorm-18](https://app-index.sandstorm.io/packages/bc424d5fd3cf60977cacdac328adfbee) | SHA-256 `bc424d5fd3cf60977cacdac328adfbee4de94f88d57383ad38b3d472c0c24f2d`; 17,379,772 B, 71.7 MiB unpacked; App ID `c6rk81r4qk6dm3k04x1kxmyccqewhh4npuxeyg1xrpfypn2ddy0h` matches catalog | Signed `apiPath="/"`, `admin`/`fullapi` permissions and API role. [Release source](https://github.com/orblivion/ntfy/tree/v2.28.0-sandstorm-18) requires `fullapi` for all requests and `admin` additionally for web UI; JSON POST `/` and polling GET `/<topic>/json?poll=1`. Go server, SQLite cache at `/var/lib/ntfy/cache.db`. Its [release README](https://github.com/orblivion/ntfy/blob/v2.28.0-sandstorm-18/.sandstorm/README.md) says browser subscriptions were deliberately removed; browser UI is mostly onboarding/API URL management. Strong JSON API fallback, thinner shared GUI. |
| [Davros 0.31.1](https://app-index.sandstorm.io/packages/c4c975c3adbeeb77fd928bb90202c049) | SHA-256 `c4c975c3adbeeb77fd928bb90202c04961d2caac52fc4c45f702d5c17011f6d8`; 127,209,100 B, 476.9 MiB unpacked; App ID `8aspz4sfjnp8u89000mh2v1xrdyx97ytn8hq71mdzv4p4d8n0n3h` matches catalog | Signed `apiPath="/"`, `view`/`edit` and viewer/admin roles; [release source](https://github.com/mnutt/davros/tree/v0.31.1) has a normal file UI, WebDAV `/dav/*`, header-based permission middleware and offer-template credentials. Node server, writable `/var/davros/data`; optional LibreOffice/Python preview stack. Default Bread parser rejects `TooLarge`; inspection alone used an explicit 600 MiB cap. Best candidate if browser-side mutation is essential, with a larger compatibility burden. |
| [Wekan 6.15.0](https://app-index.sandstorm.io/packages/bf4d676cf1f6ad39d528ae0c65ca12e1) | SHA-256 `bf4d676cf1f6ad39d528ae0c65ca12e184ee7978f5dd16cc70e08686a327fa2d`; 84,633,020 B, 524.8 MiB unpacked; catalog App ID differs from signed replacement ID `6jz1aawur7kga7tdsj9kgpxx1yzh6xz1qmrpnqukcp1rekprd9f0` under [Sandstorm's key-replacement map](https://github.com/sandstorm-io/sandstorm/blob/master/src/sandstorm/appid-replacements.capnp) | Signed `apiPath="/"`, `WITH_API=true`, Node/Mongo. Browser GUI is suitable, but bundled REST middleware appears to require a Meteor resume token that Sandstorm's API bearer does not supply. Authentication is unresolved. Default parser rejects `TooLarge`. |
| Simple Todos v5 | Local fixture SHA-256 `5830d70137cdae158118884da8790870fb095a07996cfe7708fb0155df45232e`; 23,632,200 B | Browser DDP, Node/Mongo, signed `apiPath=""`; no declared external HTTP API. |
| Hledger Web 1.31 | SHA-256 `23321185cf7dd1ae7a74e5b7deb6caba45ceefba309acbbfe350aff9b5a1c3ca`; 19,366,328 B | Signed bridge `apiPath=""` despite browser ledger UI. |
| EtherCalc | SHA-256 `93bd2c296692368252ea7b5610a7930db60e5b283340a60b6be8a812c7e309ee`; 11,983,992 B | Signed bridge `apiPath=""` despite shared spreadsheet UI. |

## Reproduction boundary

The isolated harness copied Bread parser files with SHA-256 `spk.rs=f4fc171119049297f034f4d4afe0a83356d32a388f37c34a7ab4f33166738f19`, `capnp_wire.rs=843d2b958a62f0afc138699b225bc7c481de342cd9b401efcbce469e9ca417ff`, and `manifest.rs=542862e850e6da3e1398258f971c5b2ed754c2da0cd90f8e218f505e8a4ade61` (the edited manifest parser that preserves command environment). A tiny local `grain` type stub and output-only inspection code completed the Rust harness; they were not Bread production code. `/tmp/spk-mini-probe-fixed/gitweb-findings.txt` records bounded decoded output; `/tmp/spk-mini-probe-fixed/gitweb-extract.log` records the path audit; `/tmp/spk-mini-probe/APP-SELECTION.md` is the working report. Those `/tmp` files are convenience references, not durable evidence and are not required to interpret the hashes and signed excerpts above. No parser success has been counted as an application run.
