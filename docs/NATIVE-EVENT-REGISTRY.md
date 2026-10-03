# Native event registry

Durable event tags identify replayed source transitions. Host opcodes identify
requests to a local adapter; they use a separate namespace. Reserved source
interfaces are not evidence of a deployed endpoint.

| Durable tag | Source transition |
| --- | --- |
| 60 | Joint reservation |
| 61 | Joint bootstrap bundle |
| 62 | Activity initialization and advance |
| 63 | Private backend party |
| 64 | Activity pending commitment |
| 65 | Governed portable home transfer |
| 66 | Failed START reconciliation |

The allocation is named in `Compiler/NativeDurableEventRegistry.lean`. The
portable prototype initially used 63 before registration; it moved to 65 to
preserve the private party allocation. No admitted portable event used 63.

Host requests 201–202 serve joint reserve preparation and dispatch. Requests
203–205 are allocated to the private backend party endpoint. Failed START
reconciliation uses 206 prepare, 207 assemble, 208 submit, and 209 exact ingress
lookup. An uncertain submission retains its exact ingress and uses lookup;
lookup does not authorize another physical launch.
