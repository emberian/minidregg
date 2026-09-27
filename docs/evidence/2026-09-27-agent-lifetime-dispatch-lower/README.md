# Event26 lower admission checkpoint

This is an additive, source-only lower path for the explicitly issued lifetime grant. Old event21 ingress, ticket and session codecs remain unchanged. The new event26 carrier retains the complete paid dispatch and original reserve bytes, plus event27 issue and current grant-read selectors. Its source matcher keeps the ticket/session origin at the original event22 parent generation, while binding the reserve context and signed current DRC parent target to the present execution generation. A different HTTP request, grant issue, or physical grant cell cannot reuse these coordinates.

| New source | SHA-256 |
| --- | --- |
| `Kernel/ApplicationAgentLifetimeDispatchIngress.lean` | `bc3e9c93d3f8cc5e55ea9ab5594af8f8ee1ad19120c46c0051b73e643ff18f9e` |
| `Kernel/ApplicationAgentLifetimeDispatchCurrent.lean` | `c4c1b046d549dcb8145e068d7aec77f74dcbc8d8d6d0b563229624f66d17b888` |
| `Kernel/ApplicationAgentLifetimeDispatchCore.lean` | `66b7558c562d35e2fbdaf0bf80deb0446974d364c97a6ea71252f78f0b5951b5` |

The current-image checker receives historical event22 spec/index/full receipt/ingress bytes and historical event27 grant/index/final physical grant cell root **as inputs**. It checks the original ticket's installed content, current observe capability and role ceiling; current app, manifest, session enrollment, issuer capability lineage and source law; the grant's current signed read, exact decoded record, and complete cell root; the fresh reserved parent DRC command; and the independently signed current purse hold. The candidate intent carries one physical read guard for each of app, manifest, enrollment, ticket, grant and purse, plus the original reserve claim and the same one-use HTTP operation marker used by event21. The signed observation's inner payload root is distinct from the historical complete-cell root and is not substituted for it.

This lower component **does not authenticate the supplied history by itself**. A future NativeHostReplay event26 branch must supply verifier-minted original event22 and event27 membership at their exact admitted indices and receipts, the certified event27 post-cell root, and the original reserve certificate, then route the derived intent through one durable CAS and exact readback. There is no event26 receiver, Host operation, runtime consumer, native fixture or live HTTP permit in this checkpoint. The reused current app policy check supports the existing source-owned standard app/session/ticket law family; current grant policy may change but its signed read and capability must still admit under the law then installed.

The grant physical-root comparison freezes **content**, not the authority rule: `ResourceBirthCodec.physicalRoot(.live cell)` hashes only that cell's lifecycle marker and `PackedCell.bytes` (`Compiler/ResourceBirthCodec.lean:294–306,424`; `Theory/CellSlot.lean:114–126`). A policy revision creates a separate `.policySource` cell and updates CredentialAuthorityDomain policy-head fields (`Compiler/CanonicalCellRegistry.lean:489–595`; `Compiler/CredentialAuthorityDomain.lean:329`; `Kernel/PolicyInstallReceiver.lean:203–245`). Capability revocation likewise changes authority state. Neither changes the grant content cell bytes. The current signed grant observation must pass the newly installed law and revocation state independently; an edited/tombstoned grant atom changes the content cell root and is refused.

In the isolated hbox overlay `/tank/dregg-build/mini-lifetime-grant-review-20260927`, against exact 55d3868 source and the source-qualified prefix-292 manifest SHA-256 `0c0b8fd0aedf4f97650d3ad4d369629e955943fd472c0ec089eb4de0f017d1cd`, the three modules passed in dependency order:

```sh
LEAN_NUM_THREADS=2 lake env lean -o .lake/build/lib/lean/Kernel/<module>.olean Kernel/<module>.lean
```

All three exits were 0 and each compiler log was empty (SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). The resulting OLean SHA-256 values in table order were `f4819007f49173ca27957dfab3efbc490b8bf1cff4b5615f9057a114923527f0`, `a5b3cb9d94a4947de914f660a9ff70c22581998b6bb0d7fb9abb7570f2eca655`, and `b1a483a598b1dc6438067170a5ba02171d7ea86bc99c82ea8d55c4e7398ad7d9`. No certified build or shared baseline artifact was changed.
