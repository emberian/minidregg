# Grain-backed share-ticket source checkpoint

This additive event-22 path addresses the factory-law mismatch in the retained
[r4 native attempt](../2026-09-27-application-share-issue-native-attempts/r4-diagnosis.md):
worker 8's factory authority permits a grain-backed birth, while the older
event-15 share issue requests a bare birth. Event 15 and its accepted history
remain unchanged. The new path uses the existing joint grain birth admission
for factory authority, Book fee, tool settlement and parent witness, then
checks the app's current delegation and initializes the ticket atom in the
same durable intent.

The following source files were compiled serially against the certified
ebddd8e Lean/OLean closure in the private Persvati overlay
`/tmp/mini-share-grain-source-20260927`. The frozen baseline Host binary has
SHA-256 `65b9877366acf2cb55c575cbd9cdde72c9476370434c8e328c851129799619ef`;
the event-22 modules were **not** linked into that binary. Each direct Lean
invocation exited successfully and produced a nonempty OLean. The respective
logs are empty (SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`).

| Module | Source SHA-256 | Persvati log | OLean SHA-256 |
| --- | --- | --- | --- |
| `Kernel/ApplicationShareIssueGrainSource.lean` | `e543bf372368ed5294bd60e9ffaf44fa4befbf6cadd090da41b83c3e9bdc597b` | `/tmp/mini-share-grain-source-20260927/Source.log` | `8e81db529d28c15ddcf8a3dc3c7ca3049d3d903c048dffdd0edae4f7b118385d` |
| `Kernel/ApplicationShareIssueGrainAdmission.lean` | `ace43f6779db83c4f2549c4e3958c4b0a4a65067f139df2bac5f3c5ed63427cc` | `/tmp/mini-share-grain-source-20260927/Admission.log` | `6890bb4f9fa81f9782661acdccf04f3dde01e802036bccd75bd71e70f0de832e` |
| `Kernel/ApplicationShareIssueGrainReceiver.lean` | `0eb50dcd644ff150ccfe5be682f9b246f65d2fc570ffbd3f47b59b84d7207ec1` | `/tmp/mini-share-grain-source-20260927/Receiver.log` | `02d54c25e8d8ad7c2f9215f3150f0b27648e122b3c0322f147f0ff6074c81edb` |
| `Kernel/ApplicationShareIssueGrainAuthoring.lean` | `a25be2da5f70a9f81f2128c406b4caa39262bc679fe66a1023423bf20b14ca63` | `/tmp/mini-share-grain-source-20260927/Authoring.log` | `78e871e363d53e0ed4c9a835e0093ab759c96797166865b4894e5c60a039633a` |

The source check used direct `lean -R /tmp/mini-share-grain-source-20260927`
with `-o /tmp/mini-share-grain-source-20260927/Kernel/<module>.olean`, one
compiler process at a time, after installing source-matched baseline OLean
links in that private overlay. This qualifies the four new modules only; it
is not a whole-host build or native admission result.

Remaining integration: the verifier must re-admit event 22 at its original
prefix, compare the **full** recorded intent and retain a distinct typed
issued-ticket witness for current dispatch. Event-15 evidence cannot stand in
for it. Host routes 54/55 (receive/exact lookup) and operator-private 56/57
(current plan/detached assembly), their source-owned JSON inspection, Rust
custody, a source-qualified native link and a fresh same-factory-law acceptance
fixture are not yet present. The existing r4 Store is unchanged after its
definitive event-15 refusal. Its tool grain is active with remaining budget but
reserved amount zero, so event 22 requires a new signed reserve and fresh
same-image tool/parent observations before authoring.
