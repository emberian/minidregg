# Atomic ticket creation and full payload fee

The native share plan previously requested a populated content birth, while
the ordinary birth rule requires an empty page. This repair retains ordinary
empty birth admission, then substitutes only that exact fresh allocation's
source-derived initialized ticket post in the special issue's single intent.
It checks the final physical cell law and preserves allocation identity,
pre-root, unique write IDs, other writes, read guards and bound post roots.

The configured byte tariff prices the initialized payload. A source-derived
effective tariff adds only the final-minus-empty payload supplement to the
base; collector and asset remain unchanged. The descriptor signs the full
fee, and ordinary birth admission and its actual Book batch use that same
effective tariff. Authoring uses the same derived pins without modifying the
global Host configuration or semantics. Named theorems prove the byte-price
arithmetic and exact signed fee/receiver charge correspondence. There is no
zero-byte-tariff restriction or caller-provided tariff override.

Frozen source SHA-256 values:

```
5333b59b246a94fda17f8131194ae958d04ae71d017484b927991b80a4881700  Kernel/ApplicationShareIssueSource.lean
81cba411a330ce72e44f6419b0efe2dbbc5f8f5470f204796a75943bcfa4d5d2  Kernel/ApplicationShareIssueAtomicBirth.lean
042db83d39207dd388ee274d0d6ca45ce1b4f382024315b7e556307c4d072392  Kernel/ApplicationShareIssueAdmission.lean
216c886561df1cb7d93a4d500ade62ee1270ba6f8f83ea4c620d5caf546f4163  Kernel/ApplicationShareIssueReceiver.lean
92fcf65acd7753ba20002fac8d5661b023d638007d4a35de59eb259f9c95ec68  Kernel/ApplicationShareIssueAuthoring.lean
```

The five modules compiled serially in an independent OLean copy at
`/tmp/mini-share-issue-private`, in 27.3 seconds. Root inspected their hashes,
diffs and individual `ApplicationShareIssue*.log` files. Four unused-variable
warnings remain in Source; the other logs are empty. This is a narrow source
check, not a native-link or dependent historical/replay closure claim.

The next native gate must demonstrate positive-byte-tariff issuance with the
actual signed Book debit, insufficient-funds refusal without state changes,
and exact receipt lookup/restart without a second debit. Historical special
event15 admission must rederive and match the complete atomic intent. Sharing
is not declared operational from this source check.
