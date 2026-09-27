# Generic source-owned signed-SPK descriptor authoring

`Host.Json.author "application-spk-package-identity"` accepts exactly the
host's one verified signed-SPK parse: lowercase hex `rawSha256`,
`manifestSha256`, and `bridgeConfigSha256`; canonical decimal strings
`rawLength` and `signedAppVersion`; Sandstorm `signedAppId`; `bridgeApiPath`;
and nested `signedSchema` in the existing
`minidregg-application-permission-schema-source-v1` JSON format. Mini's schema
author validates the ordered permission/role projection. Mini then derives
the interface IDs, kinds and versions: web 1/v1, and only for the exact signed
path `/repo.git/`, API 2/v1 with the same schema. The source-owned descriptor
codec and `Descriptor.valid` reject any other mapping, length, SHA shape,
AppID alphabet, or invalid schema. The request has no caller-chosen Mini
interface coordinates or package root.

`Host.Json.inspect "application-spk-package-identity"` strictly decodes the
canonical descriptor and returns its full byte echo, root, physical image
identity, raw and signed-member hashes, signed AppID/version, bridge path,
and each ordered interface's canonical bytes, root, schema bytes and root.
The physical host must still compare all fields to one verified Bread parse
and its signed BridgeConfig/ViewInfo; this authoring is not an SPK signature
verifier or an installed Mini manifest.

The generic route authored the retained GitWeb signed-SPK fields plus the
signed schema JSON to byte-identical `package-identity.bin` SHA-256
`a853b57cb79ce72f965d97b682a17c83e1396ef8e8f2f65d130e3207dbec7e7f`.
An alternate API path and a one-byte-length SHA each refused before output.
The route was directly Lean-compiled and exercised in a private Persvati
overlay. No linked Host or INSTALL acceptance is claimed here.

| Artifact | SHA-256 |
| --- | --- |
| `Host/Json.lean` | `579e4f365502012bc98fdc2b54b65538c0b0c3ed307a7f95df4dab272cf873c6` |
| private `Host/Json.olean` | `a20c78b8d4440d9542e517f2e2fede64ec067df4cc22d514dfb071e9c5874dbf` |
| private direct Lean compile log | `1903389907f5a5a2f1da59eb1b8f881e1520b9c9b5fb14ef89266bb34306e770` |
| private GitWeb generic-author input JSON | `d3a20215559dbef43ac09b4225f7ea6097291343ac730079bdb8a8c20f84f259` |
| private Lean author/inspect probe source | `9b519a47eb8017856fedf177eef865d79925ae8a798bf252076ea57a22250c9f` |
| private authored descriptor bytes | `a853b57cb79ce72f965d97b682a17c83e1396ef8e8f2f65d130e3207dbec7e7f` |
| private bad-path and bad-SHA refusal logs (each) | `aea2da709c8e64688d5594f1f9d5da4e7d080722c25a164c4b4c420687d9d60e` |

The private overlay paths are `/tmp/minidregg-completion-src/Host/Json.lean`,
`/tmp/minidregg-completion-olean/Host/Json.olean`, and
`/tmp/minidregg-spk-descriptor-Json.log` on Persvati. The executable probe
and its input/output/refusal logs are under `/tmp/mini-spk-descriptor-*` there.
The private source copy and shared source matched by SHA-256.
