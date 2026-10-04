# Objective Bend reference preview

The `objective-bend-1` edition has its own lazy reference semantics and demand machine. It does not inherit termination or consistency claims from upstream Bend.

`native/bend-source/objective-elaborate.ts` consumes a locked captured package, verifies source and AST hashes, reparses the exact source with the captured parser snapshot, checks import coordinates, and emits the actual term executed by `Theory.ObjectiveBendDemandMachine`. It also retains authored declarations, requirements and law bodies. Retained laws are not discharged proofs.

```
bun native/bend-source/objective-elaborate.ts CAPTURE_JSON OUTPUT_PREFIX ARGUMENTS_JSON PROJECTIONS_JSON LIMITS_JSON [application|definition]
```

Arguments select either the legacy array of canonical decimal natural strings, booleans and records, or an explicit `dregg.objective-bend.argument-values.v1` envelope with `values`. Tagged values are `{tag:"natural",value:"7"}`, `{tag:"boolean",value:true}`, `{tag:"label",value:"text"}` or `{tag:"record",fields:[{name:"x",value:<tagged value>} ]}`. Exact keys and distinct field names are required. String labels never become numbers or booleans because of their contents. A projection is `{ "field": "name", "argument": "3" }`, with an optional argument. Limits specify positive canonical decimal strings `ticks`, `heap` and `stack`; the lowerer refuses limits above 1000000. Callers may impose smaller public limits.

The producer writes `OUTPUT_PREFIX.core.json` and `OUTPUT_PREFIX.typed.json`; it no longer generates a Lean runner (that runner was an untyped twin of the preview loop and is deleted). The typing packet must contain exactly the core term. A caller must obtain the actual proof-bearing typing receipt before calling a typed preview successful. The annotation producer retains explicit Nat/Bool/record and captured Extension signatures. The repaired checker accepted actual captured factories and heterogeneous source composition under the earlier scalar edition; matching Boolean wire-v2 qualification is recorded separately. Ordinary result holes can infer supported primitive bodies without a default natural type. Unsupported annotated bodies receive a diagnostic; unknown result types never default to natural.

Execution goes through `Host/ObjectiveBendPreview` (check, then `runBounded` on the same decoded term), which reports `finished`, `suspended`, `divergent` or `refused`. See [OBJECTIVE-BEND-FRONTEND.md](OBJECTIVE-BEND-FRONTEND.md) for the source language and the checks.

Actual source consumers exercise even/odd mutual calls, repeated final-self calls and whole inherited computation, heterogeneous extensions, captured extension factories, unused divergent arguments and fields, cached shared fields, reflected metadata of a divergent target, and repeated application of the same extension. The saved Studio source `Notebook.remember` executes to natural 8 and the new checker accepts its exact term as natural. These are checked by `tests/objective-bend-source/preview-cohort.json` and, for GenericExtensionReuse, EvenOddTen, TwiceReview and LazySharedField, by typed drivers in `examples/objective-bend-world/reference/` that pin the result as a `native_decide` theorem (and, for LazySharedField, that the shared field is entered once); `scripts/check-objective-examples.sh` runs both. The executable checks are distinct from general elaboration correctness, demand adequacy and sharing theorems, which remain under construction.

Preview grants no native authority. Current signatures, source admission, read laws, capacity/funding, typed effects, atomic receiving and result release must still consume the explicit new edition. The old CBV source profile cannot substitute for that join.

The scalar repair uses `dregg.objective-bend.core.v2` and `dregg.objective-bend.typed-core.v3` (v2, with fully inlined types, no longer loads). Immutable wire-v1/Core3 preview tooling remains a historical cohort. Tooling pins must select the matching core, checker and lowerer; old Boolean-as-label packets must not be silently reinterpreted.
