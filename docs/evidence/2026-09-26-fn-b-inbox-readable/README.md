# Real B fn inbox: signed read and bounded typed presentation

This keyless subset comes from a **read-only** signed Mini query of target 600
in the quiet, completed run-5 B Store at
`/tmp/mini-fn-grain-r5-ab-large/run-5/mini-b`. The B Store had already
accepted the real r5 R carrier from A and completed the distinct A/B exchange.
The query used B's gateway observation grant; it did not submit another B
resource mutation. `intent.bin`, `signed-observation.bin`, and `view.bin`
retain the exact query evidence. The full raw JSON presentation was 4.2 MiB
and is intentionally not duplicated here.

`view.bin` is 716 KiB (SHA-256
`c10142579f2900256da1b30e8ebb819323c0bb3e99e3bec2d83474f142a6acbd`).
The selected-bbf native Host's pure `inspect fn-inbox-resource` path decoded
that **same** signed view to `fn-inbox-summary.json`: four entries, 10,066
bytes, SHA-256
`f47663e462833929809d8ae67f37706c5c973de09a812824e4e45d3d89bd0035`.
The binding's carried origin is an `invoke` whose signed targets include
tool grain 7102, parent grain 7101, and the scalar publication 7003 with
field-0 create value 1. The summary labels this as decoded B resource content
and carried A evidence. It does not claim that B locally applied the remote
publication. The signed `view.bin` remains the authoritative bytes; the
summary is bounded human/agent presentation, not another admission decision.

Binary/source scope: selected-bbf Mac Host SHA-256
`d94f7eb91ff9c54d1e6c4b46a650e491c0e54ca9b3a1114c5b0dd4ee717269fb`,
Mini client SHA-256
`a038f57ea39bc375e42ac1be0c3807cc9f215222f9ec947e05507355562f1585`,
`Host/FnInboxView.lean` SHA-256
`d28b193dfbadb2623b30afd0cc643f2d94f248d88c7753d474cfc8e2762f7eb4`.
The typed payload is well below the runtime's 256 KiB final result bound;
this artifact proves native typed presentation, while an actual MCP wrapping
probe is a separate gate. No custody key, B config, or full Store is included.
