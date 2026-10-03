# Authored shared station consequences

`EngineeringStation.bend` supplies an author-owned airlock/engineering/infirmary
graph and movement costs. `SharedConsequences.bend` supplies reusable take, drop
and movement methods over one global property owner and shared oxygen supply.
An action emits ordered writes to the player and the shared resource together.
Every candidate retains source revision and rules/player/resource roots.

`NativeMethods.bend` exposes public take/drop/move methods returning the common
`WorldPlanScalar.PlanResult`. `NativePlans.bend` is structural lowering only:
resource identity, root, field and exact old/new value survive unchanged.
A refusal stays `Refused(reason)`, never a successful empty Plan.
`Receiving.bend` and `NativeReceiving.bend` use synthetic inputs to accompany the
general laws and test actual source evaluation/constructor decoding.

A source check does not grant mutation authority. Native receiving must pin the
exact package/public export, source input binding, current roots and preimages,
schema, observe/mutate capabilities and current acceptance law. Changing the
rule source requires authorized adoption; adoption approval is not an install
grant. The property receiver must reject unrelated raw owner writes.

Run the source checker with Bun and explicit read-only sealed runtime/output:

```sh
BEND_SEALED_RUNTIME=/path/to/pinned/seeded/tooling \
STATION_EVIDENCE_ROOT=/path/to/owned/evidence \
bun scripts/objective-bend/check-station.ts
```

`STATION_SOURCE_ROOT` and `WORLD_PLAN_SCALAR_SOURCE` may select isolated sources.
The source package manifest binds the logical `./WorldPlanScalar.bend` import
to the one shared source under `examples/objective-bend-world`, rather than
copying another constructor implementation. `Base` is similarly an explicit
manifest binding to the local sealed Prelude. These are package imports.

The runtime provides pinned `bend.ts`, `safe.ts`, and `sealed.ts`; this example
never copies or changes the language kernel. Keep generated Books/transcripts
outside tracked source. Actual Book.check and the source-machine receiving test
are separate checks, using the designated build host and captain's bounded seat.

The separate scripted resident provider consumes the existing ACP's actual
native document read, returning cited narration and an opaque source-call
suggestion. Ordinary protected-document append/readback and resident custody
remain the existing common path. A suggestion is not a Plan or proof of an
installed world effect. See `STATUS.txt` for the current evidence boundary.
