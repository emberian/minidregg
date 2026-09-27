# GitWeb SPK to Mini identity projection

This is a source-authored prospective identity for the signed GitWeb package, not an accepted Mini installation or a running grain. `scripts/application-share-issue/author-gitweb-identity.lean` uses the Mini permission-schema, interface, manifest, and SPK-identity codecs. Its selected profile maps the signed ViewInfo to web interface 1/v1 and API interface 2/v1 with the same schema. Mini's first install advances package version 0 to 1; signed upstream AppVersion 10 is a separate descriptor field.

Inputs checked on 2026-09-27:

| Input | SHA-256 | Check |
| --- | --- | --- |
| `/tmp/spk-mini-probe/gitweb.spk` | `2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa` | 14,045,864 bytes; retained signature-verified Bread parse in [SPK selection](../2026-09-27-spk-app-selection/README.md) |
| `/tmp/spk-mini-probe/gitweb-signed-manifest.capnp` | `3ef23992c6ee79e5b684cec632d4552c5b34889348ae63acaaedb42b9616024f` | retained signed archive member, 103,736 bytes |
| `/tmp/spk-mini-probe/gitweb-signed-bridge-config.capnp` | `49d196f64ca2ce672a378581a8376ada53b27614bba522bbaec042237f0e70a2` | retained signed archive member, 576 bytes; byte-identical to `native/spk-rpc/tests/fixtures/gitweb-signed-bridge-config.capnp` |
| `scripts/application-share-issue/gitweb-signed-schema-source.json` | `dff4ec778b6b53b8eb3aae4c470101611915c7d3a5f1d4f03187ff8b8d6e6305` | exact `decode_bridge_config` of that fixture projected to ordered permission-schema source JSON, with controller-selected schema version 10; byte-identical to retained `/tmp/spk-bridge-projection-20260927/source.json` |
| `scripts/application-share-issue/gitweb-verified-package.json` | `07ec966e1f1917d310462a7847e3644bfbca43da865a8df623b482be0eb5e8b3` | pinned verified package fields: length, signer-derived App ID, signed AppVersion, member hashes and `/repo.git/` API path |

The source projection has permissions `read, write`; guest role `[true,false]`, developer `[true,true]` and default; no denied names. The bridge decoder verifies those roles in the signed member, rather than relying on the publisher's separate package definition. The Lean author reads the exact schema source with `Host.ApplicationPermissionSchemaAuthoring.author`, checks the decoded typed schema against this signed projection, requires a valid SPK descriptor, and checks that descriptor against the prospective manifest.

The bounded authoring command used a private source-qualified OLean directory,
`/tmp/mini-share-issue-private/.lake/build/lib/lean`, ahead of Lake's normal
dependencies. Its `Kernel/ApplicationSpkPackageIdentity.olean` SHA-256 was
`69ecf606601d1d9d91c59f44c0186009f355b292adf2cc68cc95a85c4fd1e32c`
from source SHA-256 `50e85fab622f8acc0515bca49e81751206e088d8c7efee5c39069a82fd8eb8e8`;
`Host/ApplicationPermissionSchemaAuthoring.olean` was
`f1edbb9cb2d339ecb7014bdc9207319dafb8ccc8e0c0301d0eb4fbfce9b44d6b`
from source `32bc18ba7ea15fb9384761edba7d067216ee9d9761fdd286ef5998deace204f8`.
The imported schema and interface source files were respectively
`a497f562f4b5c4ca28fc50f4f4c195745085451c29cf3e44e0f4035badf64d0c`
and `ac6756a1dcabfd82cae55de4f078a40ee3f96850e88e8452b26565d5b6a675fe`.
After verifying these hashes and claiming one local Lean seat, the bounded
typecheck and run from the repository root were:

```sh
LEAN_NUM_THREADS=2 lake env sh -c 'LEAN_PATH="/tmp/mini-share-issue-private/.lake/build/lib/lean:$LEAN_PATH" lean -o /tmp/mini-share-issue-private/GitWebAuthor.olean scripts/application-share-issue/author-gitweb-identity.lean'
LEAN_NUM_THREADS=2 lake env sh -c 'LEAN_PATH="/tmp/mini-share-issue-private/.lake/build/lib/lean:$LEAN_PATH" lean --run scripts/application-share-issue/author-gitweb-identity.lean scripts/application-share-issue/gitweb-verified-package.json scripts/application-share-issue/gitweb-signed-schema-source.json /tmp/mini-gitweb-identity-author-v1-20260927'
```

The output directory must be new. The author refuses unknown package fields,
package values differing from the retained verified selection, an invalid
descriptor, a mismatched schema, or a manifest not matching the descriptor.

The source author and package input above produced `/tmp/mini-gitweb-identity-author-v1-20260927` in a private bounded Lean run. The Lean source SHA-256 was `3bca5b502d98fb0c9b299e43f5a8c81cfa8fca99afa0e5757bcdd7990ec5bf2e`; direct Lean typecheck and execution passed. A version-11 schema variant was refused with `schema differs from exact decoded signed BridgeConfig projection` before output creation.

| Source-owned value | Decimal root or output SHA-256 |
| --- | --- |
| `Schema.root` | `27586312506136906444761485190217684760117883013262689471085630892456074924140` |
| web interface 1/v1 root | `53299483962106769258833733671603118086868705766326359006795883486181739552740` |
| API interface 2/v1 root | `16445804020461737684443349038626961901395635045771526464786662868335098993478` |
| `Descriptor.root` / prospective `packageRoot` | `87005803221096792113550003106028498326059648433438765766069915491574610318393` |
| `package-identity.bin` | `a853b57cb79ce72f965d97b682a17c83e1396ef8e8f2f65d130e3207dbec7e7f` |
| `schema.bin` | `534278a3930b12049cbbb69eeecea91b72ced7245edf4898356091e15e8ef21d` |
| `web-interface.bin` / `api-interface.bin` | `3156abd5815eb8b243b22b89ecc96a03d3a3eb61bca5481785b4dbdc3ec0e98b` / `716c4c22fe44eee7de335a4a2ab314cfe80fae4bf27a8ef3bb3876ccc97284cf` |
| `prospective-manifest.bin` for app 8401, Mini packageVersion 1 | `ca431a7f5972bd2ce675026c71ae4af921531530c8c22d68c349069d79d252f7` |
| `roots.json` | `0d848da24169771e02fcb32b88465cbe9dec87649432e76a87309cf6f89f272f` |

The historical package and bridge evidence is the physical signature-check boundary. This author does not itself parse or verify an SPK. The positive-fee issue fixture deliberately uses current package version 0 to prove ticket fee and recovery without pretending an install happened. The actual Mini install must still admit the exact descriptor/manifest binding through the lifecycle receiver and current physical host; a final share ticket scoped to package version 1 cannot be used against an uninstalled version-0 app. No dispatch or GitWeb app execution is established by these root calculations.
