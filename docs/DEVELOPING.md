# Developing Mini

Read [the system map](README.md) and [Objective Bend](OBJECTIVE-BEND.md) first.
[AGENTS.md](../AGENTS.md) owns repository work/build rules. This guide follows the
actual source boundary: checking an authored program, preparing a native method
proposal, and qualifying a new runtime are different operations.

## Find the implementation you are changing

| Question | Source to follow |
| --- | --- |
| What does an Objective Bend program mean? | [OpenRecursion](../Theory/ObjectiveBendOpenRecursion.lean): `Term`, `Step`, `Evaluates` (the lazy reference semantics) |
| How does it execute? | [DemandMachine](../Theory/ObjectiveBendDemandMachine.lean): `stepRaw`, `runBounded`; [DemandData](../Theory/ObjectiveBendDemandData.lean) and [DemandCapacity](../Theory/ObjectiveBendDemandCapacity.lean): deep result extraction under a capacity policy |
| How is it typed? | [Types](../Theory/ObjectiveBendTypes.lean), [Typing](../Theory/ObjectiveBendTyping.lean): `check` returns an actual derivation |
| Where is the original Bend calculus? | [Vendor provenance](../vendor/bend/PROVENANCE.json) and [BendTTSource](../Theory/BendTTSource.lean): a reference artifact only, not a language target |
| What does a program identity commit? | [Evaluator](../Compiler/Evaluator.lean), [Program codec](../Compiler/NockProgramCodec.lean); the codec's historical name does not mean the record can identify only Nock |
| How does a real method become checked effects? | [WorldKindMethods](../Kernel/WorldKindMethods.lean) → [ResourceTransaction](../Kernel/ResourceTransaction.lean) → [Run](../Kernel/Run.lean) → [WorldMethodTrace](../Kernel/WorldMethodTrace.lean) |
| Where do native fields and signed views come from? | [WorldKindDescriptor](../Compiler/WorldKindDescriptor.lean), [WorldKindProjection](../Kernel/WorldKindProjection.lean), [Host JSON](../Host/Json.lean) |
| Where is the client method/proposal path? | [world_kind.rs](../native/resource-client/src/world_kind.rs), [workspace.rs](../native/resource-client/src/workspace.rs), [shell.rs](../native/resource-client/src/shell.rs) |
| What owns durability? | [DurableReceiver](../Kernel/DurableReceiver.lean), [DurableReceiverIO](../Compiler/DurableReceiverIO.lean), [store contract](DURABLE-STORE.md) |
| Is there a circuit or FHE specialization? | Not on main for Objective Bend. `Compiler/BendLogic*` specializes the retiring BendTT core and must be re-targeted at the demand machine before it says anything about Objective Bend |

Objective Bend's semantics, machine and typing live in `Theory/ObjectiveBend*.lean`.
The front end is TypeScript: `native/bend-source/objective-parser.ts`,
`objective-frontend.ts` (capture), `objective-elaborate.ts` (surface to core) and
`objective-preview.ts`. `Host/ObjectiveBendPreview.lean` checks and runs a decoded
core term; `Kernel/ObjectiveBendPreparedOutput.lean` and
`Compiler/ObjectiveBendPlanAdapter.lean` turn a result into a scalar Plan. The
[language guide](OBJECTIVE-BEND.md) states what each of these proves and where
the trusted boundary sits. At this revision the `Theory/ObjectiveBend*` proofs are
compiled only by the opt-in `ResearchWip` library, so a green default build says
nothing about them. A native registry/profile must actually consume a module; an
importable theorem alone does not install it.

## Run an Objective Bend example

With the pinned Lean toolchain and the imported `Theory` modules compiled under the
[bounded build policy](#build-and-verify-without-disturbing-another-run), from the
repository root:

```sh
lake env lean --run tests/objective-bend-source/CheckDemandData.lean
lake env lean --run tests/objective-bend-source/CheckDemandCapacity.lean
lake env lean --run examples/objective-bend-world/reference/GenericExtension.lean
```

The first two are unit tests of the demand machine: deep result extraction and its
failures (budget, duplicate field, closure leaked into data, cycle), and a capacity
policy that suspends and later resumes a computation. They report through their exit
status and printed lines. The third runs a pre-elaborated core term for
[GenericExtension.obend](../tests/objective-bend-source/GenericExtension.obend) on
the demand machine and prints its final state. The `reference/` drivers are
generated and untyped (they do not call `check`) and contain no assertions; editing
the `.obend` file does not change them. The source-to-execution route (capture,
elaborate, check, run) is the preview tooling described in the
[language guide](OBJECTIVE-BEND.md#execution-paths).

None of these commands installs a method, creates an instance, spends credits,
emits a world effect or verifies a private backend.

## Use existing native methods

These commands belong to the current native world object interface. They do not
publish arbitrary Objective Bend source. Start with an already enrolled workspace
and a matched Host/configuration. Enrollment and reference import are described
in the [client README](../native/resource-client/README.md); a local reference
never creates a grant.

For example, the real shell help can be inspected with:

```sh
mini shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
  --workspace "$WORKSPACE" --home "$SESSION_HOME" --line 'help instance'
```

The environment variables stand for the selected deployment's absolute paths;
this guide does not supply credentials or invent a running world. Inside that
shell, use the actual names in your authorized workspace:

```text
kind show KIND
instance show INSTANCE
instance call PROPOSAL INSTANCE METHOD
submit PROPOSAL
retry PROPOSAL
```

`instance show` exposes the signed instance and its methods. `instance call`
prepares a retained proposal; `submit` attempts the actual invocation. Repeating
the same method proposal ID retains its intent and consent rather than computing
a new one. `retry` uses the retained attempt for exact-call recovery. If the
outcome is uncertain, preserve that attempt; a new proposal is a new operation.

For explicit compute funding the supported form is:

```text
instance call PROPOSAL INSTANCE METHOD --fund ACCOUNT --max-compute-credits N
```

Both funding options are required together. The compute ceiling is distinct from
command-byte cost. Current account/capability/law and the actual quote still apply;
an unfunded request does not consent to arbitrary payment. The
[world programmer guide](../native/resource-client/WORLD-PROGRAMMER.md) gives
native definition and program authoring details, including a real poll method.

## Trace a proposed feature all the way through

For a new authored method or reusable spec:

1. Define its input/result types and its required and provided methods. Include
   a composition that is incomplete until another author supplies a requirement.
   `requires` is not yet checked at composition; say so in the test.
2. Retain the original source, locked imports and elaborated core. Check the
   actual core term with the Objective Bend checker and run that same term.
3. Specify exact typed Plan outputs, dependencies, ordering, charge and independent
   return schema. Missing samples refuse; placeholder zeroes are not bindings.
4. Follow those bytes into actual native prepared effects and current authority.
   Preserve read guards, accounting, exact retry and durable outcome. Add a new
   shared effect only at its semantic owner, then connect its consumers.
5. Exercise a successful receiving path and a relevant refusal: stale source,
   missing requirement, changed root, wrong audience or insufficient funding.
   Scope the check to the changed contract; a prose edit needs no compiler rebuild.

For a new backend, retain the same semantic statement and bind its real verifier
or execution evidence to exact code, input, output and profile. An enum variant,
backend label or a theorem conditional on an uninhabited adapter is not a joined
execution route. Use the arithmetic and privacy requirements in
[Objective Bend](OBJECTIVE-BEND.md#execution-and-privacy).

## Build and verify without disturbing another run

Read the build script's current options rather than copying a stale command list:

```sh
scripts/build-native-host.sh --help
```

The native route runs in an independent snapshot with independent writable
package/build state. `MINIDREGG_NATIVE_JOBS` and `MINIDREGG_LEAN_THREADS` accept 1
or 2; the script serializes Lean processes. `LEAN_NUM_THREADS` alone does not
limit Lake's process fanout. A full deliberate qualification uses:

```sh
scripts/build-native-host.sh --umbrella \
  --output "$FRESH_BUILD_DIR" --binary "$FRESH_BUILD_DIR/minidregg-host"
```

Use a narrow source check or the script's checked prefix/suffix reuse when that
answers the actual question. Do not rebuild the entire system for documentation
or a disconnected leaf. See [NATIVE-HOST.md](NATIVE-HOST.md) for the build contract.

The native acceptance entrypoint is:

```sh
native/resource-client/journey.sh MANIFEST.json NEW_RUN_ROOT
```

It creates a fresh private Store; it is not a read-only probe of an existing
service. The manifest names absolute `host`, `mini`, `store` and `verifier`
executables with optional exact hashes. The run root must be fresh. Read the
script header for its current steps and inputs: it has no normal `--help` mode.
Read `journey-result.json` and the first non-passing frontier, not just a shell
pipeline's exit code.

The world-method hooks are not registered as `JWORLD-METHOD` in the main journey
step list. Follow the explicit fixture instructions in the world programmer
guide; do not invent `JOURNEY_STEPS=JWORLD-METHOD`. Dedicated fixtures have profile,
activation and funding prerequisites. Existing historical journeys and dated
setup runbooks remain evidence for their exact candidate, not qualification of
whatever executable happens to be on your PATH.

## Record one result, in the right place

A useful evidence entry names source and artifact identity, the exact command,
inputs, outcome, actual receiver and the claim it establishes. Preserve the
failure when it reveals a real boundary. Keep operational keys, local private
URLs and recipient-specific coordination out of the public repository.
Update the owning contract and its one example when behavior changes. New status
prose in several manuals is harder to maintain than one dated evidence record.
