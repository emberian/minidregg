# Mini

**A programmable shared world for people and agents.**

Mini is the construction home of the next Dregg: a world in which documents,
applications, communities and continuing computations share one set of rules for
authority, resources, privacy and history. Members inspect how their tools work,
compose new behaviour, delegate bounded work to agents, and change their shared
world without handing any application unrestricted access to the rest of it.

[System guide](docs/README.md) · [Objective Bend](docs/OBJECTIVE-BEND.md) ·
[Developer guide](docs/DEVELOPING.md) · [Journey](docs/JOURNEY.md) ·
[Evidence, 2026-10-03](docs/evidence/2026-10-03-objective-bend.md)

## The design in one paragraph

**Lean owns semantics and admission; Rust owns the physical boundary.** Every
change is a proposal that the Lean kernel admits or refuses against current
capabilities, laws, exact read roots and funding, and an admitted change has a
durable outcome. The Rust side supplies clients, signing and custody, storage,
transport and hosted-service adapters, and decides nothing semantic. Computation
proposes; authority admits: a correct calculation cannot grant itself permission,
a reference is not ownership, and a lost reply keeps the original operation and
its exact retry rather than licensing a second one.

```text
authored source + partial specifications
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

## What lives here

- **The deos / docuverse world.** Shared documents with transclusion, history,
  marks and protected fragments; rooms with invitations and chat; a shell and a
  browser front end; Studio for editing, importing, forking and previewing source.
- **Objective Bend**, the authored language: lazy open recursion over first-class
  partial specifications, after Faré's account of objects. See
  [below](#objective-bend).
- **Hosted applications (SPK).** Sandstorm-style application packages run as grains
  under Mini authority, with sharing tickets, export, freeze and restore.
- **Hermes and residents.** Agents summoned into a room with selected context,
  delegated tools and recoverable requests; a resident's private notes and
  revision-aware context.
- **The agreement mesh.** A Generic Simplex BFT engine written in Lean and compiled
  native, so that a world can be replicated across replicas that agree on its
  history.
- **Private execution, as research.** Traffic privacy (a post-quantum onion cohort
  with cover traffic), MPC, FHE, oblivious and proof-producing execution. None of
  these executes a member's program privately today.
- **Selvage**, the proof-system research layer (below).

## Honest state

Evidence classes: *authored* (source exists), *compiled* (Lean or Rust checked it),
*executed* (it ran in a test or dev world), *integrated* (a native Host admitted it
in a joined world), *deployed* (running on the public node for real users).

| Component | Evidence | Boundary |
| --- | --- | --- |
| Native Host, shell, documents, journey J0–J8 | deployed | public node runs the 2026-10-01 candidate; no outside member enrolled yet |
| Rooms, invitations, workroom template, chat | integrated | on development worlds only; room-scoped actions take seconds to minutes |
| Studio (edit, import, fork, history, preview) | executed | loopback development servers; no member-reachable route; publication carries no authority |
| Objective Bend Core4 semantics, machine, checker | compiled | soundness, preservation and completeness proved; proofs not in the default gate ([details](docs/OBJECTIVE-BEND.md#formal-status)) |
| Objective Bend native admission | compiled (in lanes) | no native accepted receipt from Objective source on main |
| SPK hosted apps | integrated (install, recovery) | no application has yet served a browser session |
| Hermes in a room | executed | scripted provider on a private Store; off on the public node |
| Discord entrance | executed | against a simulated Discord |
| Agreement mesh | compiled safety theorem; executed | safety over the Lean engine model; four replicas on one host, one failure domain; liveness not established |
| Traffic privacy | executed | one host, honest registrar, endpoint sees the plaintext call; no anonymity proof |
| MPC / FHE | executed (research) | MPC on public fixture inputs; FHE on a public two-input expression with one owner |
| Oblivious and zk execution of Objective Bend | authored, conditional | zk theorems assume an uninhabited refinement; oblivious machinery targets the retiring BendTT core |
| Payments | executed (fixtures) | no live payment address |

Dated, per-artifact evidence lives in [docs/evidence/](docs/evidence/); update it
there rather than copying counts into introductions.

## Objective Bend

[Objective Bend](docs/OBJECTIVE-BEND.md) is Mini's only Bend language. A
specification is a first-class extension of an inherited value under a final self;
specifications compose with `mix`, close with `fix`, and stay usable while partial.
Its core (Core4: `Theory/ObjectiveBend*.lean`) has a lazy reference semantics, a
call-by-need demand machine and a proof-producing checker, with machine-checked
soundness and no-refusal theorems. The front end is TypeScript and is a named
trusted boundary. The language guide lists what Core4 lacks, ranked, and the exact
status of every theorem. Nock remains supported for existing programs and history.

A two-author example: [ReviewBase](tests/objective-bend-source/ReviewBase.obend) and
[ReviewMember](tests/objective-bend-source/ReviewMember.obend). To run the demand
machine's own tests, see
[Run an Objective Bend example](docs/DEVELOPING.md#run-an-objective-bend-example).

## Build and verify

Read [AGENTS.md](AGENTS.md) and the [developer guide](docs/DEVELOPING.md) first. The
rules, in the repository's own terms:

- **Native route:** `scripts/build-native-host.sh`. Read `--help` before using it.
  It builds the native Host (`minidregg-host`) in a snapshot and records a manifest
  of what it built. `--umbrella` runs the literal `lake build Minidregg` integration
  gate; `--incremental-suffix-from SNAPSHOT BUILD_OUTPUT MODULE` reuses a warm build
  and recompiles from the first changed module.
- **Independent snapshots.** Build in a source snapshot with its own writable
  package and build state. The script refuses a tree without the
  `.minidregg-native-snapshot` marker unless `MINIDREGG_NATIVE_ALLOW_SHARED=1`.
- **Two seats.** At most two Lean compiler processes per machine.
  `MINIDREGG_NATIVE_JOBS` and `MINIDREGG_LEAN_THREADS` accept 1 or 2;
  `LEAN_NUM_THREADS` alone does not bound Lake's process fan-out. On a shared
  build machine, run builds under its resource guardian.
- **Acceptance:** `native/resource-client/journey.sh MANIFEST.json NEW_RUN_ROOT`
  starts a fresh private Store from the executables the manifest pins
  (SHA-256-checked) and runs the journey steps. Read `journey-result.json` and the
  first step that did not pass, not the shell's exit status alone. See
  [JOURNEY.md](docs/JOURNEY.md).
- **Scoped checks.** Choose the smallest check that can refute your change: a
  single module (`lake env lean File.lean`) for a Lean edit, a filtered test for a
  Rust edit, no build at all for prose. `lake build Minidregg` is the integration
  gate, not a per-change check. Targets and their limits are in
  [LEAN-QUALIFICATION.md](docs/LEAN-QUALIFICATION.md).
- **Rust:** `cargo build --release --offline --locked` per crate under `native/`;
  run tests filtered to what you changed.

A source check does not establish that a new executable was built, and a built
executable does not establish deployment.

## Layout

| Path | Contents |
| --- | --- |
| `Theory/` | candidate-independent semantics, including Objective Bend Core4; imports only Mathlib and Theory |
| `Kernel/` | admission: resources, capabilities, laws, transactions, durable receiving |
| `Pred/` | the predicate algebra for laws |
| `Effects/` | the effect handler registry |
| `Compiler/` | codecs, arithmetization, IR and source compilers |
| `Host/` | the native receiving process (`Host.Main` is `minidregg-host`) and host tools |
| `Assurance/` | cross-boundary theorems with pinned axiom checks |
| `Verify/` | verification drivers and emitters |
| `Selvage/` | proof-system research |
| `native/` | Rust: the `mini` client (`resource-client`), SPK host and RPC, grain runtime, stores, agreement crypto, private backend, FHE, Discord, pay watcher |
| `prover/` | Rust prover glue |
| `protocol/` | generated protocol and build-surface inventories |
| `scripts/` | build, gate and check scripts |
| `deploy/` | candidate build and service configuration |
| `testing/`, `tests/` | scenario drivers, journeys and focused tests (`tests/objective-bend-source/` holds the `.obend` probes) |
| `examples/`, `world/` | example programs; the `.bend` modules there are upstream-Bend source on the retiring BendTT path, kept as domain designs to port |
| `vendor/bend/` | the pinned original Bend calculus, a reference only |
| `docs/` | contracts, guides and dated evidence |
| `website/` | the static project site |

## Where the design records live

Everything a reader needs is in this repository, under [`docs/`](docs/README.md):
the [system guide](docs/README.md), the [language guide](docs/OBJECTIVE-BEND.md),
the [developer guide](docs/DEVELOPING.md), the dated proof-contract map
([CONSTRUCTION-PROOF-CONTRACTS](docs/CONSTRUCTION-PROOF-CONTRACTS-20261003.txt)),
[persistent computation](docs/BEND-PERSISTENT-COMPUTATION-20261003.txt), the
privacy and agreement contracts it links, and the dated evidence records. Older
top-level documents ([PROJECT.md](PROJECT.md), [ATLAS.md](ATLAS.md),
[HANDOFF.md](HANDOFF.md)) keep rationale and history; where they disagree with
`docs/` or the source, the source wins.

## Selvage

Selvage is Mini's proof-system research and construction layer: hash-based,
small-field machinery for proximity testing, sumcheck, transcript compilation,
accumulation and verifiable history, with explicit security assumptions and
bounds. No world admission uses a proof today; admission is checked by
re-execution. A theorem, a compiled controller and a deployed verifier establish
different things, and Mini keeps those connections explicit through named
obligations, inhabitation and counterexample checks, axiom accounting and receiving
tests. See [Selvage/](Selvage/) and [PROJECT.md](PROJECT.md).

## Contributing

Useful contributions improve an authored tool or world, close a source-to-runtime
connection, delete a duplicated mechanism, strengthen a proof, or expose a claim
the evidence does not support. Say what a change breaks: nothing here has users or
a compatibility obligation, so a format change is a rebuild, and an old shape
should refuse to load rather than be reinterpreted.
