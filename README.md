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
| Native Host, shell, documents, journey J0–J8 | deployed | the public node runs the 2026-10-01 candidate (source `5688775a`): the shell, documents (`new`, `show`, `append`, `edit`, `link`, `backlinks`) and boards; it has no rooms, chat, key rotation or proxy mode, and no outside member is enrolled (what it has and lacks: [FRIENDS.md](deploy/shell/FRIENDS.md)). Evidence: [shell journey, J0–J8 89/89](docs/evidence/2026-09-30-shell-journey/README.md); node state read on 2026-10-03 (swarm Scout G, outside this repository). Main is not the candidate: the continuous journey runner at main `4795b657` (2026-10-04, runner table outside this repository) passes J0–J4, J6, J7 and JROTL and fails J5 and J8 (a stranger's attempt was not refused by the Host in 2 of 6 and 1 of 5 cases) and JROT (3 of 30 checks); the 10-01 pass is the candidate's, not main's, and the fix is open |
| Rooms, invitations, workroom template | integrated | on development worlds only, from lane builds: J15 and J17 pass in [p-story](docs/evidence/2026-10-01-p-story/journey-result.json) and [p-credit](docs/evidence/2026-10-01-p-credit/journey-result.json); not on the public node; room-scoped actions take seconds to minutes (Scout G: workroom template 224–270 s on a development world). ROOM-SCHEMA v2 landed in `6a173263`; the private-rooms end-to-end driver (`3aaa3cfd`, journey row `rooms`) is red on main at `4795b657` (0 of 88 expected rows present) |
| Chat (`say`, `tail`, `topic`, `pin`, `react`) | compiled | Rust code and tests in `native/resource-client/src/chat.rs`, and the `JCHAT` journey hook; no journey result in `docs/evidence/` records `JCHAT` as PASS (the three 10-01 results mark it SKIPPED), so no recorded run has joined chat to a native Host (in-process operations: `336b7c0e`) |
| Studio (edit, import, fork, history, preview) | authored; executed on lane builds only | client routes in `native/resource-client/src/web/studio.rs` and `native/resource-client/src/workspace/studio.rs` (2 focused tests); the loopback development servers that ran were built from lane branches, not from this commit; no member-reachable route; publication carries no authority; the prototype declarations still use the deleted Gen-1 shape and feed nothing ([STUDIO-SOURCE-WORKSPACE.md](docs/STUDIO-SOURCE-WORKSPACE.md)); the preview is the Host's own Lean front end (`31a9072e` preview v2, `a2454432` Lean front end) |
| Objective Bend Core4 semantics, machine, checker | compiled | soundness, preservation and completeness proved; the proofs are the `ObjectiveProofs` library, gated by `scripts/check-objective-proofs.sh proofs` (statement and axiom snapshot), not by the default build ([details](docs/OBJECTIVE-BEND.md#what-is-proved)). Landed: completeness `1456f58e`, `forceWith` and Plan-path soundness `db7c0bc7`, the statement and axiom snapshot gate `3204e85e` |
| Objective Bend native admission | integrated on scratch worlds | `native/resource-client/objective-native-acceptance.py all` (journey row `objective`): publish, a signed invocation with an Accepted receipt, refusal rows r01-r13, reopen and replay; the receiver re-runs the Lean front end on the package and prices the declared envelope by the public tariff; not deployed ([details](docs/OBJECTIVE-BEND.md#native-admission-by-re-execution)). Landed: `31a9072e`, `73223088` (tariff), `6df4602f` (client and acceptance), `796d7d7a`, `a2454432` (Lean front end re-run by the receiver). Journey row `objective` PASS at main `4795b657` (17 rows, 2 readbacks) |
| Objective activities, object records, calls, sends, seats | integrated on scratch worlds (activities, object records, seats); calls and sends executed by lane drivers | every activity turn, `invoke` and `deliverMessage` included, is a signed native command (Host ops 210-214, `mini activity`), and seats have their own (215-219, `mini seat`); journey rows `activity`, `objectrecord` and `seats` run their drivers on scratch worlds; the call (C1-C8) and send (S1-S7) drivers exist and no journey row runs them ([activities](docs/OBJECTIVE-BEND-EVENTS.md#the-kernel), [seats](docs/SEATS.md)). Landed: record, answer slots and resume contract `8194e09d`; resume with view `67362781`; paid exhaustion, disposal and abandonment `d1ce7b0c`; object record `eac4b18c` and `de9c84f7`; one public tariff `bf28dd19`; laws pin `2a7c372b`; seats `6347dcb4` |
| SPK hosted apps | compiled (physical layer and Lean lifecycle); install, start, supervised restart and export integrated on development worlds | [44 of 44 rows](docs/evidence/2026-10-01-spk-apps/jspk1/rows.tsv) of the 10-01 lane run (birth, install, share, start, a SIGKILLed generation replaced by the supervisor's STOP and continue-START, backup, stop, export). Failed-START recovery: `spk-host grain supervise` drives the Lean receiver (`Kernel/ApplicationFailedStartRecoveryReceiver.lean`) through Host ops 206–209 (`native/spk-host/src/grain_export.rs`; lookup and same-bytes resubmission unit-tested against a scripted Host), the code the live r2 world ran on 10-03 now on main; the deterministic journey rows (`scripts/spk-platform/jspk1.sh failstart`, an integration-qualification `spk-host`) are authored and have not run; no application has yet served a browser session (closest: EtherCalc co-editing over TLS with older binaries, [2026-10-02-spk-browser-tls](docs/evidence/2026-10-02-spk-browser-tls/README.md)) |
| Split tenancy (one account per friend, a key broker) | compiled; run on no box | `mini-keys` (`1d4b683f`) holds the seal key, provider keys and Discord secrets; `mini key` (`73e06411`), the Hermes controller (`f991da1d`) and the Discord entrance (`7bb016a3`) go through it; candidates ship it (`b374fee3`, `179f6bee`). dregg-infra `tenancy=split` is built and on no box; the scratch run of its journey is not recorded ([FRIENDS.md](deploy/shell/FRIENDS.md), `1784edf5`) |
| Hermes in a room | executed | scripted provider on a private Store ([J14, 2026-10-01](docs/evidence/2026-10-01-p-hermes-room/journey-result.json)); off on the public node |
| Discord entrance | executed | against a simulated Discord ([2026-10-03-discord-world](docs/evidence/2026-10-03-discord-world/README.md)); under split tenancy it runs each line as the friend's account (`7bb016a3`); no Discord application exists and the entrance is inactive on the public node |
| Agreement mesh | compiled safety theorem; executed | safety over the Lean engine model; four replicas on one host, one failure domain; liveness not established (engine intake `02a4edd7`, quiescent-leader and discovery fixes on main in `205ccbdb`) |
| Traffic privacy | executed | one host, honest registrar, endpoint sees the plaintext call; no anonymity proof (roster enrollment `d7b2f19b`) |
| MPC / FHE | executed (research) | MPC: a width-8 adder over private inputs with per-dealer OS entropy, and a curious-holder transcript check over 8,067 frames, in `native/private-backend` tests (`cf6a4c1d`); FHE: none on main (the BFV consumer ran only upstream-Bend artifacts and was deleted on 2026-10-04) |
| Oblivious and zk execution of Objective Bend | authored, conditional | zk theorems take a refinement premise that is inhabited only for five literal programs, and native proof verification is not connected to the arithmetic relation ([ZK.md](docs/ZK.md), [OBJECTIVE-BEND.md](docs/OBJECTIVE-BEND.md#backends-and-privacy)); the generic oblivious/arithmetic circuit stack has no Objective producer yet (`a006d243`: the tranche covers Core4) |
| Payments | executed (fixtures) | the pay journeys ran on private Stores with recorded Solana answers ([deploy/pay/README.md](deploy/pay/README.md#current-composed-rehearsal-2026-10-02)); the enrolment address and rate (50 DREGG per week) are decided in [enrol-terms.json](deploy/pay/enrol-terms.json) but nothing is deployed: the pay watcher and roster sync are inactive on the public node, and no mainnet transaction has been made. Pay-to-enrol (`mini join --solana`, `--wait`, `--renew`) is documented in FRIENDS.md (`b0bcb7d0`, `243fb343`) and the rate is one terms file (`cb4235b6`); journey steps JPAY1–JPAY4 run it on fixtures, and a known defect is open: the tariff counts hours, so the quoted week is 49.999992 DREGG, not 50 (cv `01a105c0-0292`) |

Evidence rows cite runs of lane builds. Unless a row says otherwise, the run was not
repeated at the commit this README describes. Dated, per-artifact evidence lives in
[docs/evidence/](docs/evidence/); update it there rather than copying counts into
introductions.

## Objective Bend

[Objective Bend](docs/OBJECTIVE-BEND.md) is Mini's only Bend language. A
specification is a first-class extension of an inherited value under a final self;
specifications compose with `mix`, close with `fix`, and stay usable while partial.
Its core (Core4: `Theory/ObjectiveBend*.lean`) has a lazy reference semantics, a
call-by-need demand machine and a proof-producing checker, with machine-checked
soundness and no-refusal theorems. The front end is one program in Lean (parser,
elaborator, C4 linearization), a named trusted boundary: its output is checked by the
proof-producing checker and the receiver re-runs it at admission. The language guide lists what Core4 lacks, ranked, and the exact
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
| `native/` | Rust: the `mini` client (`resource-client`), SPK host and RPC, grain runtime, stores, agreement crypto, private backend, IR2 proof harness, Discord, pay watcher |
| `prover/` | Rust prover glue |
| `protocol/` | generated protocol and build-surface inventories |
| `scripts/` | build, gate and check scripts |
| `deploy/` | candidate build and service configuration |
| `testing/`, `tests/` | scenario drivers, journeys and focused tests (`tests/objective-bend-source/` holds the `.obend` probes) |
| `examples/`, `world/` | Objective Bend reference drivers and `.obend` domain programs |
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
