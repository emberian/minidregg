# Developing Mini

Read [the system map](README.md) and [Objective Bend](OBJECTIVE-BEND.md) first.
[AGENTS.md](../AGENTS.md) owns repository work/build rules. This guide follows the
actual source boundary: checking an authored program, preparing a native method
proposal, and qualifying a new runtime are different operations.

## Find the implementation you are changing

| Question | Source to follow |
| --- | --- |
| What is live Bend execution? | [BendTTSource](../Theory/BendTTSource.lean): `Book`, `Eval`, `Walk`; [BendLiveMachine](../Theory/BendLiveMachine.lean): checked bounded execution |
| Where are the exact upstream bytes and adaptation? | [Vendor provenance](../vendor/bend/PROVENANCE.json), [patch](../vendor/bend/lean430.patch), [license](../vendor/bend/LICENSE) |
| What does a program identity commit? | [Evaluator](../Compiler/Evaluator.lean), [Program codec](../Compiler/NockProgramCodec.lean); the codec's historical name does not mean the record can identify only Nock |
| How does a real method become checked effects? | [WorldKindMethods](../Kernel/WorldKindMethods.lean) → [ResourceTransaction](../Kernel/ResourceTransaction.lean) → [Run](../Kernel/Run.lean) → [WorldMethodTrace](../Kernel/WorldMethodTrace.lean) |
| Where do native fields and signed views come from? | [WorldKindDescriptor](../Compiler/WorldKindDescriptor.lean), [WorldKindProjection](../Kernel/WorldKindProjection.lean), [Host JSON](../Host/Json.lean) |
| Where is the client method/proposal path? | [world_kind.rs](../native/resource-client/src/world_kind.rs), [workspace.rs](../native/resource-client/src/workspace.rs), [shell.rs](../native/resource-client/src/shell.rs) |
| What owns durability? | [DurableReceiver](../Kernel/DurableReceiver.lean), [DurableReceiverIO](../Compiler/DurableReceiverIO.lean), [store contract](DURABLE-STORE.md) |
| What is the first circuit specialization? | [BendLogicSpecialization](../Compiler/BendLogicSpecialization.lean) → [BendLogicTrace](../Compiler/BendLogicTrace.lean) → [BendLogicEmit](../Host/BendLogicEmit.lean) |

For Objective Bend, the source cohort adds `Compiler/ObjectiveBendComposition`,
`ObjectiveBendElaboration`, `ObjectiveBendOrder`, `ObjectiveBendPrototype`,
and the separately authored `ObjectiveBendPersistence`,
`ObjectiveBendLinker` and `ObjectiveBendWorkshop`. The world-language cohort adds
`BendWorldSource`, `BendCoreAdmission`, `BendWorldProgramCodec`, `BendWorldPlan`
and their publication/admission consumers. Consult the
[dated index](evidence/2026-10-03-objective-bend.md) before treating an owner-checked
module as part of the selected native Host. A native registry/profile must
actually consume the module; an importable theorem alone does not install it.

## Check the authored example

The readable source package is [world/Workshop](../world/Workshop/MemberExtension.bend).
The committed [core Book](../examples/objective-bend-workshop/MemberExtension.bendtt)
is static emitted source, with the exact original helper closure. The
[driver](../examples/objective-bend-workshop/Run.lean) checks its real composition:

```sh
lake env lean --run examples/objective-bend-workshop/Run.lean \
  examples/objective-bend-workshop/MemberExtension.bendtt
```

Run from the repository root with the repository's pinned Lean toolchain and
already-built matching imports. This narrow driver canonicalizes the supplied
core Book, admits it with the real checker, resolves the actual helper entries
and exercises incomplete, completed and extended compositions. It should refuse
the missing `finalSelf.audit` and accept the two complete cases. The counts and
frozen source qualification belong in the evidence index.

The `.bendtt` input is the emitted Book. Merely editing `.bend` and rerunning a
previous `.bendtt` checks the previous program. Re-elaboration must use the exact
sealed parser/elaborator, pinned pure Prelude and retained dependency transcript.
Do not invoke an unrestricted upstream loader as if it enforced Mini's sealed
imports. The relocated `native/bend-source/check-workshop.ts` wrapper is separately marked
WIP until its public setup/import path is qualified. The checked core recipe above
is available independently; it does not promise an end-to-end source-edit workflow.

What this command does **not** do: install a method, create an instance, spend
credits, emit a world effect, verify a private backend, or prove the optimized
native compiler equivalent. The separate [source exporter](../examples/objective-bend-workshop/Export.lean)
exercises actual whole-Card method outputs.

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

1. Define its input/result types and exact required/provided interfaces. Keep
   persistent Data captures distinct from per-invocation closures. Include a
   composition that is incomplete until another author supplies a requirement.
2. Retain the original source, locked imports and emitted core. Check the actual
   body/type and the complete linked Book; exercise the corresponding live entry.
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
