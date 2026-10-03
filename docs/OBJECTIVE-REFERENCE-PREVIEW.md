# Objective Bend reference preview

The `objective-bend-1` edition has its own lazy reference semantics and demand machine. It does not inherit upstream BendTT termination or consistency claims. The historical BendTT execution profile remains separate.

`native/bend-source/objective-elaborate.ts` consumes a locked captured package, verifies source and AST hashes, reparses the exact source with the captured parser snapshot, checks import coordinates, and emits the actual term executed by `Theory.ObjectiveBendDemandMachine`. It also retains authored declarations, requirements and law bodies. Retained laws are not discharged proofs.

```
bun native/bend-source/objective-elaborate.ts CAPTURE_JSON OUTPUT_LEAN ARGUMENTS_JSON PROJECTIONS_JSON LIMITS_JSON
```

Arguments are canonical decimal natural strings, booleans or records. A projection is `{ "field": "name", "argument": "3" }`, with an optional argument. Limits specify positive canonical decimal strings `ticks`, `heap` and `stack`; the lowerer refuses limits above 1000000. Callers may impose smaller public limits.

The producer writes `OUTPUT_LEAN`, `.core.json` and `.typed.json`. The typing packet must contain exactly the core term. A caller must obtain the actual proof-bearing typing receipt before calling a typed preview successful. The current annotation producer supports literal ordinary declarations and returns an explicit diagnostic for unsupported annotated bodies; it does not default unknown result types to natural.

The generated runner prints one `dregg.objective-bend.reference-result.v1` JSON record. Status is `finished`, `suspended`, `divergent` or `refused`. A ground result has tag `natural` with a decimal string, or `label`. Closures, records and prototypes are reported without forcing their bodies or fields. Suspension retains machine state internally; this JSON view is not yet a persisted checkpoint codec. Blackhole reports no ground result and is not a catchable source exception.

Actual source consumers exercise even/odd mutual calls, repeated final-self calls and whole inherited computation, heterogeneous extensions, captured extension factories, unused divergent arguments and fields, cached shared fields, reflected metadata of a divergent target, and repeated application of the same extension. The saved Studio source `Notebook.remember` executes to natural 8 and the new checker accepts its exact term as natural. These executable checks are distinct from general elaboration correctness, demand adequacy and sharing theorems, which remain under construction.

Preview grants no native authority. Current signatures, source admission, read laws, capacity/funding, typed effects, atomic receiving and result release must still consume the explicit new edition. The old CBV source profile cannot substitute for that join.
