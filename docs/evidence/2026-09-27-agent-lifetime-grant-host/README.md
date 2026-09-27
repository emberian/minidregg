# Event27 lifetime-grant Host route — source gate

The operator Host now accepts an exact typed grant request through
`author application-agent-lifetime-grant-request`. Its JSON contains the full
grant source, original event22 four-field receipt, participant, approval,
owner/control capabilities, payer, funding, and birth source capabilities.
Numeric values are canonical decimal strings. Mini constructs the strict
`requestCodec` bytes; the client does not encode the grant or issue wire.
`inspect application-agent-lifetime-grant-request` and
`...-plan` are source-owned, read-only custody projections with the exact
canonical request/spec and ordered signing headers.

Native stdio operations are reserved and routed as follows:

| Opcode | Boundary |
| --- | --- |
| 72 | Strict event27 ingress → verifier-selected event22 issue, fresh current admission, one durable CAS/readback → ordinary Outcome receipt |
| 73 | Exact event27 ingress → Verified historical original → receipt-only Outcome |
| 74 | Strict request → current Verified image → framed signing plan |
| 75 | LE32 pair of strict plan and detached signatures → current Verified plan recheck → framed event27 ingress |

All four broker operations are owner-private and bounded. The public service
socket refuses them at this checkpoint. The submit route cannot produce an
agent dispatch permit; the lookup route does not replay installation.

Changed source pins:

| File | SHA-256 |
| --- | --- |
| `Host/Json.lean` | `50adfe1403e167c81f73cefee47fa5740bdc63950eb777d476f176feda32c7d8` |
| `Host/Main.lean` | `988c7dd531df69b6e49a303fc16023af369fbec0b728414a633c055298a75a54` |
| `native/resource-client/src/transport.rs` | `f5339141800cbdd63e209c24df9e1e50818c88412df7c65315d3103979cf4aa5` |

Imported event27 module pins: Receiver `a5aa2975357669ae0ce1c0b27709df28acd7ed6f068a51543a983ed6a02e023c`,
Lookup `b4b43029b4fcefb199203880404721bd4f352767d81f935f97bab486d2367878`,
Authoring `3e7235bde67e926ad6ead21d56392d2640c6d71d8a3623e87a05ba11a61db972`,
Inspection `e5dd5cd55b5a3f673732e540527ffe652f2efa7305b6684350d4c198840c0a6a`.

An independent writable hbox overlay imported those source-matched OLeans
and compiled Host.Json then Host.Main serially with `LEAN_NUM_THREADS=2`.
Both direct Lean commands exited 0; Json reported existing linter/axiom
notes, Main log is empty. Resulting OLean SHA-256 values are
`a717d95b6dc066220c552793dccb47c14931fcd9098aea86395394a388a0368e`
and `3833a84b50a307f30265237b0f924175e393b58fbf84b78f8ec8bfd156e9f9d6`.
Focused `cargo nextest` broker test passed 1/1; `cargo fmt --check` passed.
This is a source and broker gate only; no linked Host or native event27 Store
acceptance is claimed.
