# Mini: a programmable shared world

Mini is the construction home for the next Dregg: a shared computing environment
where people and agents author objects, documents, tools and institutions, and
where changes pass through explicit authority, resource and history contracts.
**Objective Bend is its central authored language and live-environment direction.**
Nock compatibility preserves existing executable programs and history.

Start with [Objective Bend](OBJECTIVE-BEND.md) for the language and a worked
composition, then [Developing Mini](DEVELOPING.md) to follow the actual source and
commands. The [dated evidence index](evidence/2026-10-03-objective-bend.md) separates
checked source, executed components and joined native behavior. These guides
explain the system; the older [proof-system introduction](../README.md#selvage),
[project architecture](../PROJECT.md) and [founding atlas](../ATLAS.md) retain their
useful detail and historical context.

## The system in one pass

A member observes an authorized view of current state, computes a proposed
change, and asks Mini to admit it. Lean defines the values, checks and transition
meaning. The native Rust boundary supplies physical transport, signing, custody,
storage and external services. An accepted transition must have a durable outcome;
a lost network reply does not turn an uncertain operation into permission to
perform a second one.

```text
source modules + sealed imports + partial specifications
                         |
            checked core term + exact entry
                         |
  authorized invocation sample -> computation -> typed Plan / result
                         |
       current authority + laws + read roots + funding
                         |
       admitted durable transition / retained outcome
                         |
     authorized views, durable delivery, separate private release
```

This is a map of the shared contract, not a claim that every arrow is already
wired for every language and backend. A source checker establishes properties of
the checked program. An admission check establishes permission for this exact
transition. A runtime or proof backend must separately establish what it computed.

The useful vocabulary is small:

| Term | Meaning |
| --- | --- |
| Participant | A signing identity; a room alias or fictional role is not this identity. |
| Resource | Governed state with an exact current representation and history. |
| Capability and law | The delegated action and the current conditions it must satisfy. Neither is replaced by an object reference. |
| Kind / instance | A definition of fields and behavior, and a particular persistent object with its own state. |
| Spec | A composable, possibly incomplete definition of behavior. |
| Program / source artifact | An immutable executable identity, and retained source, imports and interpretation metadata. |
| Plan | Proposed typed effects, dependencies, messages and results; computation alone does not admit it. |
| Activity | A continuing computation with execution context, continuation and pending obligations. |
| Receipt / retained outcome | Evidence of the particular admitted operation; distinct from physical delivery or decryption. |

## One medium, several experiences

The destination is a shared multiuser agentic world host. Its experiences should
be intelligible in their own terms while sharing the same underlying contracts:

- **Docuverse and workdesk:** documents, source inspection, transclusion, research,
  annotations and review, with exact revision support for derived views.
- **Hosted applications and residents:** SPK applications, browser/API access,
  Hermes tools, private context, delegated actions and recoverable work.
- **Authored worlds:** places, characters, collective fiction and community rules,
  with real shared consequences rather than isolated presentation demos.
- **Allocation and service commons:** contributed capacity, exchange, reservations,
  accounting and recovery, with explicit allocation rules and conservation.

A workshop is a useful demanding example, not the boundary of the product. The
October 13 alpha direction includes traffic privacy and distributed agreement;
component demonstrations do not satisfy those requirements on their own.

## Find the contract and its implementation

The following is a navigation skeleton. Each row points to an existing contract
or implementation; there is no second manual for each subsystem.

| Area | Start here | Semantic / physical owner in source |
| --- | --- | --- |
| Language and object composition | [Objective Bend](OBJECTIVE-BEND.md) | `Theory/ObjectiveBend*.lean` (semantics, demand machine, typing, proofs); `native/bend-source/objective-*.ts` (front end); `Host/ObjectiveBendPreview.lean` |
| Native kinds and methods | [World programmer](../native/resource-client/WORLD-PROGRAMMER.md) | [WorldKindMethods](../Kernel/WorldKindMethods.lean), [WorldPrototypeConstruction](../Kernel/WorldPrototypeConstruction.lean), [WorldMethodTrace](../Kernel/WorldMethodTrace.lean) |
| Authority and transactions | [Client contract](../native/resource-client/README.md) | [ResourceTransaction](../Kernel/ResourceTransaction.lean), [Run](../Kernel/Run.lean) |
| Durability, retry and history | [Durable store](DURABLE-STORE.md), [receipt continuity](RECEIPT-CONTINUITY.md) | [DurableReceiver](../Kernel/DurableReceiver.lean), [DurableReceiverIO](../Compiler/DurableReceiverIO.lean) |
| Documents and authorized views | [Protected authored fragments](contracts/protected-authored-fragments.md), [observation roots](OBSERVATION-AND-PHYSICAL-ROOTS.md) | [HyperdocumentPublication](../Kernel/HyperdocumentPublication.lean), [HyperdocumentCell](../Compiler/HyperdocumentCell.lean) |
| Agreement across domains | [Distributed design history](DISTRIBUTED-DESIGN.md), [current scope](evidence/2026-10-03-objective-bend.md) | [JointReservation](../Kernel/JointReservation.lean), [NativeJointAgreement](../Kernel/NativeJointAgreement.lean), [JointDecisionRecovery](../Kernel/JointDecisionRecovery.lean) |
| Confidential computation and custody | [Private cell](PRIVATE-CELL.md), [language execution contract](OBJECTIVE-BEND.md#execution-and-privacy) | [PrivateWorldIR](../Compiler/PrivateWorldIR.lean), [PrivateSuccessorCustody](../Kernel/PrivateSuccessorCustody.lean) |
| Traffic privacy | [Traffic privacy contract](../native/resource-client/TRAFFIC-PRIVACY.md) | Channel/client/relay paths named by that contract; distinct from computation secrecy |
| Hosted services and SPK | [Provider custody](HOSTED-PROVIDER-CUSTODY.md), [SPK RPC](../native/spk-rpc/README.md) | `native/grain-runtime/`, `native/spk-host/`, `native/resource-client/` |
| Proof systems and compilation | [Selvage introduction](../README.md#selvage), [proof-system survey](PROOF-SYSTEM-SURVEY.md) | `Theory/`, `Selvage/`, `Compiler/`, `Assurance/` |
| Build and native qualification | [Developer guide](DEVELOPING.md), [native host](NATIVE-HOST.md), [journey](JOURNEY.md) | `scripts/build-native-host.sh`, `native/resource-client/journey.sh` |

Dated design documents sometimes describe gaps that subsequent source has closed.
Use them for rationale, then inspect the current declaration and its consumer.
[HANDOFF.md](../HANDOFF.md) links the wider suite's project tracking; it is not a
prerequisite for understanding this guide.

## Keep the guide useful

When a contract changes, update its owning page, the example or source pointer
that exercises it, and the dated evidence entry if qualification changed. Put
counts, source pins and run outcomes in evidence, not introductory paragraphs.
Preserve historical evidence with its scope. Avoid copying task rosters or local
handoffs into the public manual.
