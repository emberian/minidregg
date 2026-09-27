# Grain-backed share JSON custody

The event22 operator request is authored by `Host.Json.author` kind
`application-share-issue-grain-request`. Its JSON has exactly `spec`, `payer`,
`funding`, `sourceCapabilities`, `tool`, and `parent`; each grain selector has
exactly `task`, `capability`, and `observeCapability`. The existing strict share
spec parser supplies the ticket, issuer, payer, funding, and capability fields.
No current root, state, or signing header is accepted from this JSON.

`Host.Json.inspect` kinds `application-share-issue-grain-request` and
`application-share-issue-grain-plan` decode their respective canonical source
frames. Both expose the exact `canonicalRequest` hex. The plan also exposes
`canonicalPlanHex`, finalized grain birth source/command/descriptor, current
tool and parent selectors and roots, and `birthSlots`, `appSlot`, and ordered
`slots` (birth slots followed by the app slot). Each slot includes its exact
header hex and decoded algorithm, key ID/epoch, authority root, registry
commitment, domain, message, and nullifier. The inspector refuses noncanonical
frames and a finalized grain birth whose capabilities differ from the request.
These projections are for private signer custody; native admission remains
authoritative.

The direct Lean check of the new inspector and Host.Json passed in a private
Persvati overlay against the committed event22 Authoring OLean. A focused
executable check authored a complete request and inspected its frame, checking
the echoed canonical request length; it printed
`grain-backed share request author/inspect: ok`. No native event22 acceptance or
linked Host claim follows from this source-only check.

| Artifact | SHA-256 |
| --- | --- |
| `Kernel/ApplicationShareIssueGrainAuthoring.lean` | `a25be2da5f70a9f81f2128c406b4caa39262bc679fe66a1023423bf20b14ca63` |
| `Host/ApplicationShareIssueGrainInspection.lean` | `28e7435b69e6b09a322a14986df487397f72311575d44bcb56e535b9ea26bf18` |
| `Host/Json.lean` | `e9bea5b5c942e467ee0be53273df092de9a8079a9c40f5703a83c0e25c816a30` |
| private event22 Authoring OLean | `78e871e363d53e0ed4c9a835e0093ab759c96797166865b4894e5c60a039633a` |
| private GrainInspection OLean | `13c4504212e0cd4602913306c982f85659a1b56f3bc65a2f62b4362020c87c28` |
| private Host.Json OLean | `b0ec7942a2fec938ec71cd77e66955ef6225d47200df060313295be34d2f61ef` |
| private Host.Json check log | `2b77a9fa08220647a5e7c61fafec77ca4b495f1fb7a8066db0f6bca0fff910ab` |
| focused request check source / log | `1a74ecb1e09dd4b1cfcdd7f8d8949b7f00ff35d3326be20ed32e7c1f3f8a7620` / `db8b9eac13a3d249d28f08eb3854534a16c1d54557bd423dec94205406553160` |

The private source/check files are `/tmp/mini-grain-inspection-src/Host/ApplicationShareIssueGrainInspection.lean`,
`/tmp/minidregg-completion-src/Host/Json.lean`,
`/tmp/minidregg-grain-share-Json-rebuilt.log`, and
`/tmp/mini-grain-share-json-check.{lean,log}` on Persvati. The checked OLean
overlay is `/tmp/minidregg-grain-share-union`, based on the independent
`/home/ember/build/minidregg-overnight-20260927-selected-prefix-codec` tree.
