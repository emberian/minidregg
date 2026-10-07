# One receiver: collapsing the hand-written receiving families

Lane RECEIVER-COLLAPSE, 2026-10-04.  Status of each claim is tagged:
**measured** (a command on this tree, `5216e02f`, re-runnable), **read** (I read
the source), **record** (from the 10-03 reviews or the W1.9 receiver sweep, not
re-verified), **landed** (in commit `c46b49f2` on `lane/receiver-collapse`).

## 1. What is there now

### Census (measured)

`Kernel/` is 493 files and 149,361 lines.  Files that each define their own
copy of a standard piece:

| piece | files |
|---|---|
| `inductive Reject` | 58 |
| `inductive Result` | 56 |
| `structure Accepted` | 53 |
| `structure Prepared` | 52 |
| `def charge` | 46 |
| `def intent` | 41 |
| `def receiveLoaded` | 33 |
| `def replay` | 29 |
| `theorem readGuards_readonly` | 28 |
| `def requireSome` (the same three lines) | 22 |

Twins, measured by diff after renaming the family token:
`ApplicationAgentLifetimeGrantAtomicBirth` and `ApplicationShareIssueAtomicBirth`
are 172 lines each and differ in one docstring line (`grant` / `share`).
`ParticipantKeyEnrollmentReceiver` (178) and
`ParticipantFactoryProvisioningReceiver` (180) differ in 18 diff lines.

`Host/Main.lean` has 167 distinct numeric opcode arms (measured).
`protocol/host-operations.json` holds 176 allocations: 174 active (142 routed
to `fnDispatch`, 25 to `dispatchSession`, 7 to `serveFrame`), 2 reserved; 105
public+operator, 69 operator-only; 20 Rust client-constant bindings and 3
response markers (measured).  `scripts/host-operations.py` checks it against
`Host/Main.lean` and `native/resource-client/src/transport.rs` by parsing a
"small known grammar" of match arms with regular expressions, and generates
`native/host-operations.rs` (read).  Four of the ~74 Host receiver entry
points appear in any theorem (record).

### The 33 `receiveLoaded` families

Standard pieces each file retypes: Rj `Reject`, Ac `Accepted`, Rs `Result`, Pr
`Prepared`, Rp `replay`, RG `readGuards_readonly`, rS `requireSome`, In
`intent`, Ch `charge`, Nf `nullifier` (measured by grep).  "Sig" is the order
of signature verification relative to preparation (re-execution, policy
compile, content runs) per the W1.9 sweep (record), op = Host opcode where the
sweep named it.  Thm = `theorem` declarations in the file (measured).

| family | lines | pieces | sig | op | thm |
|---|---:|---|---|---|---:|
| FnSelectiveReleaseReceiver | 107 | Rj Rs Rp | first | 20 | 1 |
| BendKeyRegistration | 110 | (on DRC) | DRC | – | 2 |
| BendSourcePublication | 113 | (on DRC) | DRC | – | 2 |
| BendOpaqueResultReceiver | 120 | (on DRC) | DRC | – | 1 |
| FnSelectiveReleaseSourceReceiver | 125 | Rj Ac Rs Rp Ch | first | 24 | 0 |
| ObjectiveBendReferenceSource | 161 | (on DRC) | DRC | – | 2 |
| ParticipantKeyEnrollmentReceiver | 178 | Ac Rs Rp RG In Ch Nf | prepare first | 88 | 2 |
| ParticipantFactoryProvisioningReceiver | 180 | Ac Rs Rp RG In Ch Nf | prepare first | 94 | 2 |
| FleetTurnReceiver | 192 | Ac Rs Rp RG In Ch Nf | prepare first | 98 | 2 |
| ApplicationShareIssueGrainReceiver | 195 | Rs Rp RG In Ch Nf | prepare first (DRC B) | 54 | 7 |
| ApplicationShareIssueReceiver | 205 | Rs Rp RG In Ch | prepare first (DRC B) | 28 | 9 |
| GrainResourceBirthReceiver | 238 | Rj Rs Rp RG In Ch | prepare first | – | 2 |
| CapabilityRevocationReceiver | 316 | Ac Rs Rp RG In Ch Nf | prepare first | – | 9 |
| CapabilityDelegationReceiver | 318 | Ac Rs Rp RG In Ch Nf | prepare first | – | 10 |
| BendReturnRelease | 319 | Ac Rs Pr Rp Ch Nf | DRC | – | 2 |
| SubjectKeyCommitmentAdoption | 345 | all ten | prepare first | 189 | 4 |
| **SubjectKeyRotation** | 419 | all ten | prepare first → **first (landed)** | 142 | 4 |
| ApplicationLifecycleBeginReceiver | 430 | Ac Rs Rp In | prepare first (DRC B) | 22 | 9 |
| PayClaimReceiver | 463 | all ten | first | – | 4 |
| CapabilityRenounce | 475 | all ten | first | – | 5 |
| ResourceBirthReceiver | 525 | Rj Rs Rp RG In Ch | prepare first | – | 28 |
| PayEnrolV2Receiver | 568 | Rj Ac Rs Pr RG rS In Ch Nf | prepare first | 119 | 4 |
| PayObservationReceiver | 682 | Ac Rs Pr Rp RG rS In Ch | prepare first | 110 | 14 |
| ClockTickReceiver | 718 | all ten | prepare first | 128 | 12 |
| PolicyInstallReceiver | 730 | Rj Ac Rs Pr Rp RG In Ch | prepare first | – | 27 |
| CertifyReceiver | 745 | all ten | prepare first | 172 | 12 |
| PayAssignmentReceiver | 766 | all ten | prepare first | – | 20 |
| PayBookReceiver | 791 | all ten | prepare first | 105 | 16 |
| PurseRefillReceiver | 812 | Ac Rs Pr Rp RG rS In Ch Nf | prepare first | 115 | 13 |
| JobMoneyReceiver | 956 | Ac Rs Pr Rp RG rS In Ch Nf | prepare first | 162 | 14 |
| RealmWellReceiver | 995 | all ten | prepare first | 125 | 32 |
| PayEnrolReceiver (v1) | 1229 | all ten | prepare first; no-memo bypass | – | 7 |
| DeclaredResourceController | 1912 | Ac RG | first (op 2 path) | 2 | 58 |

"DRC" = rides on `DeclaredResourceController.withAcceptedLoaded`, which loads
the directory before authenticating (record).  Group B of the sweep (share
issue, lifecycle Begin/Claim/Completion, dispatch, session enrollment,
failed-start recovery) calls `DeclaredResourceController.prepare` before
`admit`; `LifecycleClaimV3` re-runs Begin admission (record).  Total: 23 of the
33 files prepare before verifying (record), now 22; the sweep counts ~30 live
entry points.

## 2. The design

### 2.1 `Theory.Receiving.Receiver` (landed, compiled)

One declaration over an abstract journal.  The journal (`Journal`) is what a
receiver sees of durability: a loaded `State`, its journal-bearing `Snap`, a
`lookup` of a transaction id to its `Recorded` id/event/nullifiers, the intent
constructor `intentOf`, the executor's `install`, and one law,
`lookup_install` (an installed intent is found under its own id with its own
event and nullifiers).

```lean
structure Receiver (J : Journal) where
  Env Ingress Command Reject : Type
  Prepared : Env → J.State → Command → Type
  decode   : List UInt8 → Option Ingress
  command  : Ingress → Command
  claims   : Env → J.State → Ingress → Except Reject (List SigQuery)  -- no Prepared argument
  prepare  : (env : Env) → (state : J.State) → (command : Command) →
               Except Reject (Prepared env state command)            -- the gate; may re-execute
  shape    : Prepared env state command → Bool
  txId     : Env → Ingress → J.TxId       -- the marker
  event    : Env → Ingress → J.Event
  nullifiers : Env → Ingress → List J.Nullifier
  payload  : (ingress : Ingress) → Prepared env state (command ingress) → J.Payload
```

`SigQuery` is `(publicKey, message, signature)`.  Defined once from it:
`Refusal` (`malformed | family r | unauthenticated q | verifier d | shape`),
`Accepted` (private constructor; only `admit` makes one), `admit` (claims →
`firstRefused` → `prepare` → `shape`), `verifyAll`/`vouches`, `Admitted`
(oracle + accepted + the equation `admit … ok = .ok accepted`), `admitVia`
(resolve claims, run the verifier, admit), `guardsOff`, `intent`, `receipt`,
`replay`, `Commit`, `Outcome`
(`replayed | conflict | refused | committed ingress admission witness |
durable ingress other`), and `receive` (decode → replay → `admitVia` → append).

**The type carries signature-first.**  `claims` cannot see a `Prepared`, so a
family cannot name a signature over something only preparation computes.  The
four money receivers that sign a host-authored plan (PayObservation,
PurseRefill, JobMoney, PayEnrol) cannot be expressed until they sign the
command and marker first and bind the plan after; the migration forces the
fix the sweep asked for.

Laws proved once (all `#assert_axioms`-pinned; compiled):

| law | statement |
|---|---|
| `admit_signature_first` | `claims = .ok cs → firstRefused ok cs = some q → admit … ok = .error (.unauthenticated q)`, for every receiver, so for every `prepare`/`shape` |
| `admit_ok_iff` | `admit … ok = .ok a ↔ ∃ cs, claims = .ok cs ∧ (∀ q ∈ cs, ok q) ∧ prepare = .ok a.prepared ∧ shape a.prepared` |
| `verifyAll_pure` | at `Id`, the verifier accepts exactly `cs.takeWhile v` |
| `admitVia_vouches_only_verified`, `admitVia_claims_verified` | an admission's oracle vouches only for claims the verifier accepted; so every claim of an admitted ingress verified |
| `admitVia_unauthenticated` | a claim the verifier refuses makes `admitVia` return `unauthenticated`, never an admission or a `prepare` refusal |
| `guardsOff_readonly`, `guardsOff_complete` | no guard on a written cell; no guard on an unwritten cell dropped |
| `replay_only_original` | `replay = some (.ok r)` → `r` is this ingress's receipt and the journal holds exactly its id, event, nullifiers |
| `replay_after_install` | in any state whose snapshot installs an admission's intent, replay confirms that ingress with the same receipt (replay = live admission) |
| `receive_committed` | a `committed` outcome came from a decode, an unjournaled id, `admitVia = .ok admission`, and the append's exact witness |
| `receive_committed_verified` | at the pure verifier, a committed ingress had every claim verified |
| `Fixture.committed_reachable`, `Fixture.unauthenticated_reachable` | premise inhabitants (a two-line journal) |

The `Id` theorems are about the same `receive`/`admitVia` the Host runs in
`IO` (one definition, two monads); the native verifier itself is an IO oracle
and is not modelled.

### 2.2 `Kernel.Receiving.Family` (landed, compiled)

The deployed instance: `journal` with `State := DurableReceiverIO.Loaded
rootBytes`, `Snap := DataSnapshot rootBytes`, `lookup` over
`Snapshot.lookupRecorded`, `install := DataSnapshot.install`,
`intentOf` building a `DataIntent`; `lookup_install` is proved over the real
install.  A family supplies:

```lean
structure Family where
  Env Ingress Command Reject : Type
  rejectRepr : Repr Reject
  Prepared : Env → Durable → Command → Type
  decode : List UInt8 → Option Ingress
  bytes : Ingress → List UInt8
  command : Ingress → Command
  claims : Env → Durable → Ingress → Except Reject (List SigQuery)
  prepare : (env : Env) → (durable : Durable) → (command : Command) → Except Reject (Prepared env durable command)
  writes : Prepared env durable command → List DataWrite          -- the per-cell patch
  writes_bound : ∀ p w, w ∈ writes p → rootBytes w.canonicalPostBytes = w.exactPost
  observed : Prepared env durable command → List ReadGuard
  postLaw : Prepared env durable command → Bool
  txId : Env → Ingress → Digest
  event : Env → Ingress → StableEvent
  nullifiers : Env → Ingress → List StableNullifier
  subject : Ingress → Option SubjectId
  witnessBytes : Ingress → Nat
```

and gets, once: `readGuards` (observed minus written), `shape` (distinct
written cells, every pre-root and guard root current, post law) with
`shape_sound`, `charge` on all ten lanes (`proofWork` = number of claims),
`payload` (both `DataIntent` obligations discharged), `receiver`,
`receiveLoaded` (`receive` in `IO` with the native Ed25519 verifier and
`receiveLoadedDetailed`), `admitNative` (the audit walk's re-admission = the
live `admitVia`), `receipt`, `lookupLoaded`, and `replay_after_execute` (when
the executor accepts an admission's intent, a later state at that snapshot
looks the ingress up as confirmed with the same receipt).  The Host side is
one `NativeHost.receivingOutcome`/`receivingSubmitLoaded`/`receivingLookupLoaded`.

Fields still to add as families need them (not speculative, named by the
census): `fee : Prepared → Nat` (pay families' `feeDebit`), `creates` (birth
families' new cells), and the typed patch of §4.

### 2.3 `HostOp` (design)

One Lean inductive replaces `protocol/host-operations.json`, its regex
scanner, and the three numeric dispatchers:

```lean
namespace Minidregg.Host.Operation
inductive Route | public | operator | stdio
inductive Status | active | reserved
inductive HostOp | describe | authorizedPrepare | submit | … | subjectKeyRotationSubmit | …   -- one per allocation
def HostOp.code   : HostOp → UInt8
def HostOp.symbol : HostOp → String
def HostOp.routes : HostOp → List Route
def HostOp.status : HostOp → Status
def HostOp.all    : List HostOp
theorem all_complete  : ∀ op, op ∈ HostOp.all          := by intro op; cases op <;> decide
theorem code_injective : ∀ a b, a.code = b.code → a = b := by decide
def HostOp.ofCode? (b : UInt8) : Option HostOp := HostOp.all.find? (·.code = b)
theorem ofCode_code (op) : HostOp.ofCode? op.code = some op

inductive Handler
  | submit (family : Kernel.Receiving.Family) (env : NativeHost.Config → family.Env) (label : String)
  | lookup (family : Kernel.Receiving.Family) (env : NativeHost.Config → family.Env) (label : String)
  | session (run : SessionContext → List UInt8 → IO (UInt8 × List UInt8))   -- describe, plan, assemble, queries
def HostOp.handler : HostOp → Handler
def dispatch (ctx) (op : HostOp) (payload) : IO (UInt8 × List UInt8) :=
  match op.handler with
  | .submit F env label => … NativeHost.receivingSubmitLoaded ctx.config ctx.opened F (env ctx.config) label payload
  | .lookup F env label => … NativeHost.receivingLookupLoaded …
  | .session run => run ctx payload
```

`Host.Main` decodes the byte with `HostOp.ofCode?`, checks the route, and
calls `dispatch`; the 167 arms become table rows.  A `lake exe
emit-host-operations` (in `Host/EmitOperations.lean`) writes
`native/host-operations.rs`: the `pub const` per op, `pub fn
public_route(op: u8) -> bool` and `operator_route`, and the response markers;
`transport.rs` calls the two functions instead of hand-matching byte slices,
and clients import the constants (20 bindings become plain `use`).  The gate
is "emit to a temp file, byte-compare the tracked one".  Deleted:
`protocol/host-operations.json`, `scripts/host-operations.py`,
`scripts/test-host-operations.py`, the generated table in
`protocol/HOST-OPERATIONS.md` (emit it too, or drop it).

What this buys the proof: every `.submit F` op reaches `F.receiveLoaded`
through one `match`, so a theorem stated once over `Family` covers every
submitting op by the handler equation, and "nothing is proved about the
dispatcher" stops being true.

## 3. `Turn.ofAdmission` and `host_submit_is_step`

Today (`Kernel/HostRefinesWorld.lean:1006`, read):
`Turn.ofAdmission B H w (_admitted : NativeAdmission config opened intent) :=
Turn.ofIntent B H w intent` -- the admission is ignored; the turn is
recovered by diffing the intent's bytes against the world.

After:

1. **Typed patch.**  `Family` gains `patch : Prepared env durable command →
   List CellPatch`, `CellPatch := {cell, kind, pre, post, validated :
   ValidatedPatch …}` (the `WorldKindInstance` descriptor → layout → patch
   shape), and `writes` is *derived*: `writes p := (patch p).map
   CellPatch.toWrite` (encode `post`, root it).  `writes_bound` is then
   discharged once and leaves the record.
2. **`Turn.ofAccepted`**, total, from the admission object:
   ```lean
   def Turn.ofAccepted (B : Bridge R D) (H) (w) {F env durable ingress}
       (admission : F.receiver.Admitted env durable ingress) : DTurn R D :=
     { txId := F.txId env ingress
       legs := (F.patch admission.accepted.prepared).map CellPatch.leg
       creates := F.creates admission.accepted.prepared
       nullifiers := F.nullifiers env ingress
       charge := F.charge env durable ingress admission.accepted.prepared
       event := F.event env ingress }
   ```
   No `Except`: the refusals happened in `admit`.  Once over `Family`:
   `ofIntent_ofAccepted : Represents B p w →
   Turn.ofIntent B H w (F.receiver.intent a) = .ok (Turn.ofAccepted B H w a)`
   (because `writes = patch.map toWrite` and the bridge codec round-trips),
   so the existing `ofIntent_run` and `confirmed_represents` carry over.
3. **`NativeAdmission`** gets one constructor
   `| receiver (op : HostOp) (F) (h : op.handler = .submit F envOf label)
   (admission : F.receiver.Admitted (envOf config) opened.durable ingress)`,
   indexing `F.receiver.intent admission.accepted`; the per-family
   constructors (37 today) go as families migrate.  `Turn.ofAdmission`
   matches it to `Turn.ofAccepted`.
4. **`Appended` carries its step.**  `DurableReceiverIO.Appended` gains
   `ready : Ready …` and `nextExact : next = afterCheckpoint (loaded.extend
   ready) stored` (only the read-back branch builds it; no wire change).
5. **`host_submit_is_step`** becomes, over the outcome value that only
   `receive` constructs:
   ```lean
   theorem host_submit_is_step (F : Family) (H) {config} {opened : Opened config}
       {ingress} {admission : F.receiver.Admitted (envOf config) opened.durable ingress}
       {witness : Receiving.Appended opened.durable (F.receiver.intent admission.accepted)}
       {w} (represents : DeployedRepresents opened.durable w) :
       ∃ w', World.admit H w (Turn.ofAccepted bridge H w admission) = .ok w' ∧
         DeployedRepresents witness.appended.next w' ∧
         ∃ cs, F.claims (envOf config) opened.durable ingress = .ok cs ∧
           ∀ q ∈ cs, admission.ok q = true
   ```
   proved once from `confirmed_represents` + `ofIntent_ofAccepted` +
   `nextExact`, and lifted to every submitting `HostOp` by the handler
   equation.  `Kernel.HostRefinesWorld` then moves into the Host closure
   (imported by `Kernel.NativeHost`), and `Represents.journal` can be
   tightened to the derived turn's digest because the turn is now a function
   of the admitted object, not a diff.

## 4. Migration order, and what each step breaks

| step | families | wire / journal | re-genesis |
|---|---|---|---|
| 0 (landed `c46b49f2`) | SubjectKeyRotation | none: intents byte-identical (read) | none |
| 1 | ParticipantKeyEnrollment, ParticipantFactoryProvisioning, FleetTurn, SubjectKeyCommitmentAdoption (the identical ~180-line receivers; claims = sponsor envelope over (marker, request at the authority root) + possession; all computable from `loadDeployment`) | none | none |
| 2 | ApplicationShareIssue + ShareIssueGrain + AgentLifetimeGrant (one family parameterised by spec kind; the AtomicBirth twins become one module) | none | none |
| 3 | DeclaredResourceController as a `Family` (claims = the authority envelope, as `ResourceInvocationSignatureFirst.authenticate` already computes, whose double verification then goes), then Bend*/Fn* on it, Group B (session enrollment, dispatch, failed-start recovery) | none for op 2; Group B order change only | none |
| 4 | Capability Delegation/Revocation/Renounce, PolicyInstall, ResourceBirth, GrainResourceBirth | none | none |
| 5 | Lifecycle Begin/Claim/Completion: keep only the newest version; operator ops 44/45, 50/51, 52/53 emit it | V1/V2 ingress refuses to decode | **yes**: journals holding V1/V2 records no longer re-admit in the audit walk |
| 6 | Pay/C3: PayBook, PayAssignment, RealmWell, ClockTick, Certify, PayClaim; then PayObservation, PurseRefill, JobMoney, PayEnrol (v2 only; v1 deleted) | the last four sign command + marker first, plan after: new frame versions, old frames refuse | **yes** |
| 7 | `HostOp` + emitter; delete json, scanner, `ResourceInvocationSignatureFirst` | opcode bytes unchanged; `host-operations.rs` regenerated | none |
| 8 | typed patch, `Turn.ofAccepted`, `NativeAdmission.receiver`, `Appended.ready`, `host_submit_is_step`, HostRefinesWorld into the Host closure | none (model + evidence) | none |

Steps 5 and 6 re-genesis the devnet and re-emit nothing else (no VK, no
descriptor).  Every step deletes the bespoke module in the same commit.

## 5. Evidence and limits

* compiled, plain `lean` against the read-only olean set of
  `/tank/dregg-build/codex-spk-recovery-endpoint-20261003` (whose sources
  equal HEAD for every direct dependency except `Compiler/DurableReceiverIO`,
  which adds `Transport.sourceGate`, unused here): `Theory.Receiving`,
  `Kernel.Receiving`, `Kernel.Receivers.SubjectKeyRotation`,
  `Assurance.KeyPreRotationAudit`, and the unchanged importers
  `Kernel.{SubjectKeyCommitmentAdoption, PayClaimCommand, PayPendingRotation,
  PayClaimDecision, PayClaimReceiver}`.
* authored: `Kernel.NativeHostReplay`, `Kernel.NativeHost`, `Host.Main`,
  `Host.Json` (HEAD imports modules the farm lacks).  Warm-base command:
  `SWARM_MEM_MAX=16G swarm-build env LEAN_NUM_THREADS=2 lake build
  Theory.Receiving Kernel.Receiving Kernel.Receivers.SubjectKeyRotation
  Assurance.KeyPreRotationAudit Kernel.NativeHost Host.Main`.
* not executed: no Host run, no journey test.  The byte-identity of the
  rotation intent is by reading both definitions lane by lane.
* not modelled: the native verifier (an IO oracle); the theorems say what is
  done with its verdicts.
