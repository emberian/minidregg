# Mini

**A programmable shared world for people and agents.**

Mini is growing into the next Dregg: an environment where documents, applications,
communities and ongoing computations share explicit rules for authority, resources,
privacy and history. Members should be able to inspect how their tools work,
compose new behavior, delegate bounded work to agents and evolve their shared
world without handing every application unrestricted access to everything else.

[System guide](docs/README.md) · [Objective Bend](docs/OBJECTIVE-BEND.md) ·
[Developer guide](docs/DEVELOPING.md) · [Current evidence](docs/evidence/2026-10-03-objective-bend.md)

## What you can build

Mini brings several experiences onto one underlying system:

- **A living workdesk:** shared documents, source and history inspection,
  transclusion, annotations, research and review.
- **Programmable communities and worlds:** member-authored objects, tools,
  institutions, collective fiction, allocation rules and service commons.
- **Hosted applications and continuing residents:** SPK application packages,
  browser/API access, Hermes tools and agents with selected context, delegated
  authority and recoverable requests.
- **Persistent computation:** activities that retain their execution context and
  pending obligations, with governed evolution, export and resumption.

These are connected construction goals with working parts. The native shell and
browser expose documents, rooms, signed inspection, member-authored kinds and
instances, and guarded method proposals. Objective Bend source composition and
execution have runnable examples. The full source-authored Studio, new Bend native
effect route, continuing activity lifecycle and cross-provider restoration are
being integrated. The [evidence index](docs/evidence/2026-10-03-objective-bend.md)
identifies the exact source and executable scope behind each result.

## How it fits together

A member reads an authorized view, computes a proposal, and submits it under the
current rules. The same path applies to a human command, an agent tool and an
object method.

```text
authored modules and partial specifications
                   ↓
       checked program + pinned profile
                   ↓
 authorized inputs → computation → typed effects and results
                   ↓
 current grants · laws · read roots · funding
                   ↓
       admitted durable transition
                   ↓
 views · retained outcomes · delivery · authorized private release
```

**Lean owns transition meaning and admission.** The kernel checks current
capabilities, laws, exact state dependencies and resource accounting. Rust supplies
physical clients, signing and custody, storage, transport and hosted-service
adapters. Canonical encodings and generated artifacts connect these boundaries.

**Computation proposes; authority admits.** A correct calculation cannot grant
itself permission. A reference does not confer ownership. A cached program does
not cache authority, and an approved community proposal still needs the actual
installation transition.

**Durability includes uncertainty.** A lost reply retains the original operation
and its recovery path. Delivery, external completion and private-result release
have their own obligations; they do not become complete merely because a local
computation returned.

See the [system map](docs/README.md#find-the-contract-and-its-implementation) for
the contracts and source modules at each boundary.

## Objective Bend

[Objective Bend](docs/OBJECTIVE-BEND.md) is Mini's primary authored language and
live-environment direction. Nock remains supported for existing programs and
history. Bend starts from a pinned dependent affine core; its implementation and
language may evolve with explicit semantics, versioning and refinement.

A partial specification provides methods and declares what it requires. Authors
compose these specifications using final self and prior super, then check the
actual linked program. Immutable source, typed captures and per-invocation closures
connect reusable behavior to persistent objects. Methods return typed proposed
effects and independent results; reflective views use authorized observations.

The [Workshop example](world/Workshop/README.md) demonstrates this directly:
one author supplies catalog and review, another adds an audit requirement, and
a third completes it and changes presentation without editing the original
modules. Its driver rejects the incomplete composition and checks the completed
program. The [language guide](docs/OBJECTIVE-BEND.md) explains the example and
its path toward native admission.

## Try a checked composition

Prerequisites: this repository, the toolchain pinned in
[lean-toolchain](lean-toolchain), and matching compiled imports for
`Compiler.ObjectiveBendWorkshop`. Prepare dependencies through the
[bounded build workflow](docs/DEVELOPING.md#build-and-verify-without-disturbing-another-run);
a fresh clone alone does not contain those artifacts. From the repository root:

```sh
lake env lean --run examples/objective-bend-workshop/Run.lean \
  examples/objective-bend-workshop/MemberExtension.bendtt
```

The driver reports the expected missing `finalSelf.audit`, then accepts the
completed and extended compositions. It checks the committed emitted Book;
regenerating that Book is a separate step when editing the original `.bend`
source. This command needs no running Mini world or credentials.

For an enrolled participant with a matched native client, Host configuration,
workspace and session home, inspect the actual shell interface:

```sh
mini shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
  --workspace "$WORKSPACE" --home "$SESSION_HOME" --line 'help instance'
```

Inside the shell, `instance show NAME` reads an authorized instance;
`instance call ID NAME METHOD` prepares a proposal; `submit ID` attempts admission.
Use the retained attempt for recovery after an uncertain reply. The
[client guide](native/resource-client/README.md) covers enrollment and workspace
setup; [world programming](native/resource-client/WORLD-PROGRAMMER.md) covers
native kinds, programs and methods. These native commands do not yet publish
arbitrary Objective Bend source through a completed Studio workflow.

## Privacy and agreement

Private computation, traffic privacy and distributed agreement are core
requirements. Execution plans can combine native computation, bounded oblivious
execution, reusable circuits, proof verification and homomorphic computation,
provided they preserve the declared result, arithmetic, resource and disclosure
contracts. Private returns have independent custody and current release rules.

Current construction includes a fixed-access Bend controller, executed Bool/BFV
fragments, traffic/custody components and a native Generic Simplex engine.
Their general refinements and joined world receiving paths have distinct
qualification boundaries. Encryption alone does not hide a traffic schedule;
an agreement certificate alone does not authorize or physically install a change.

Read [execution and privacy](docs/OBJECTIVE-BEND.md#execution-and-privacy),
[traffic privacy](native/resource-client/TRAFFIC-PRIVACY.md),
[native agreement](docs/GENERIC-SIMPLEX-NATIVE.md) and
[portable continuation](docs/PORTABLE-CONTINUATION.md) for their actual contracts.

## Selvage

Selvage is Mini's proof-system research and construction layer. It develops
hash-based, small-field machinery for proximity, sumcheck, transcript compilation,
accumulation and verifiable history, with explicit security assumptions and
bounds. Its results support the larger goal of making computations and histories
cheap to verify, including private computation.

A theorem, a compiled controller and a deployed verifier establish different
things. Mini keeps their connections explicit through named obligations,
inhabitation and counterexample checks, axiom accounting, emitted artifacts and
actual receiving tests. The [source](Selvage/) and
[project architecture](PROJECT.md) describe the proof work and its runtime joins.

## Develop and contribute

Start with [AGENTS.md](AGENTS.md) and the [developer guide](docs/DEVELOPING.md).
Use an independent build snapshot and the repository's bounded native builder:

```sh
scripts/build-native-host.sh --help
```

Choose the smallest check that can refute your change. Native acceptance uses a
matched executable manifest and a fresh Store through the
[journey](docs/JOURNEY.md); source checks do not imply that a new executable was
built or deployed. Keep current qualification in the evidence index rather than
copying live counts into introductions.

Contributions can improve authored tools and worlds, close a source-to-runtime
connection, simplify a repeated mechanism, strengthen a proof, or expose a claim
that the current evidence does not support. The aim is one system whose useful
behavior and guarantees grow together.
