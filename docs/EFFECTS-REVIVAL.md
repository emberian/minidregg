# Effects revival: the derivation engine, made able to state the deployed write path

Lane `lane/effects-revival`, 2026-10-27.  Starting point: the deputy's decision,
`docs/review/2026-10-27-untouched-areas/EFFECTS.md` ("Phase-3 design").  This document makes
that design concrete; `Effects/Revival/Statements.lean` states it.  Statements only: no
proof, no migration, no change under `Kernel/` in this lane.

The owner's ruling this answers: hand-written kernel effects are not acceptable.  A new kernel
effect comes out of a declaration, and the hand arm it replaces is deleted in the same commit.

## 0. Present state (lane `registry-effects-2`, 2026-11-14)

The open constructor exists and one effect lives on it. §1 to §8 below are the October design
and its continuation; where they disagree with this section, this section is the tree.

* **`Payload.registered (code : UInt8) (op : (effectAt code.toNat).O)`**
  (`Kernel/ResourceTransaction.lean`). `effectAt` reads `liveEffects`
  (`Kernel/ResourceEffectRegistry.lean`): wire code ↦ declaration. An unbound code's operation
  type is `Empty`, so no payload can carry it. The payload decoder asks the registry first and
  hands a bound tag to its declaration's own prefix decoder; only an unbound tag reaches the hand
  decoder (`legacyPayloadDecode`). Binding a tag a hand arm still owns does not build
  (`legacy_unbound` is what `payloadStream`'s round-trip reads).
* **`Effect`** (`Kernel/ResourceEffect.lean`) is the declaration: typed cell (`L`, `wire`, `pack`,
  `unpack`), `spec : EffectSpec`, the JSON face (`name`, `toJson`, `ofJson`), the display, the
  refusal text (`refusalText`: a refusal's detail in words), and its
  obligations as proof fields (`unpack_pack`, `pack_unpack`, `observes_silent`, `complete`,
  `view_unjoint`). Derived from it: `compute` (header from `accepts`/`version`/`commutes`, then
  the engine's `exec`), `patch` (the emitted descriptor), `observeOnly` (the verb is the observe
  verb under every role), `handler` (the engine handler). `EffectCtx` holds no schema version and
  no expected root, so a semantics cannot compare a root by hand.
* **Engine changes** (`Effects/Revival/Engine.lean`): `DispatchRefusal.refused code name detail`
  and `EffectSpec.refusalDetail` (canonical bytes beside the name); `EffectSpec.view` takes a
  `Site` (signer, cell id); `Handler.select`/`pack` take the context (a declared cell is an
  object's, an account's or a program's, and the role is the transaction's); `Handler.comap`.
* **The cited read is declared** (`Kernel/CitedRead.lean`, `citedEffect`, code 9, JSON
  `fieldRead`). `Payload.fieldRead`, `Reject.citedKey`/`citedStale` and every hand arm of it are
  deleted. Wire bytes of code 9 are unchanged (tag octet 9, then the list of reads). Its refusals
  surface as `Reject.effect (.refused 9 name detail)`; `citedStale`'s detail is the moved keys
  (`citedStale_detail`), printed as `Effect.FieldRead.citedStale [field 5, …]`
  (`dispatchRefusalText`, the one `Repr` of a dispatch refusal: it reads the declaration).
* **An unread payload tag is refused by name at the receiver** (`Kernel/ResourcePayloadTag.lean`):
  command bytes whose payload tag no declaration binds and no hand arm reads are answered
  `Reject.effect (.unregistered tag)`, every other undecodable byte string `malformedCommand`.
  `UnboundTagNamed` is proved: a named octet is bound by nothing, read by nothing, and its bytes
  are not a command.
* **Statements** (`Kernel/EffectsRevival/Statements.lean` §7b), all **proved**
  (`RegistryProofs.lean`): `RegistryKeystone` (`Dispatches hostRegistry liveLegacy
  liveTargetDispatch`; `liveLegacy` is the codes still hand arms), `RegistryPremise`, `RegistryAccepted` (both
  poles of the cited read at an authority cell holding a field-scoped observe capability),
  `RegistryTeeth`, `LiveLegacyCensus`, `LiveLegacyCensusTeeth`. The keystone's heart,
  `liveTargetDispatch_registered`, is proved for an arbitrary declaration: at a bound code the
  deployed functions are the engine's `dispatch`. Binding another code adds no proof there.
  `HostKeystone` (content, code 1) is proved; see below.
* **The census is a script**: `scripts/effect-arm-census.py` (hand arms per payload kind, read
  from the `Payload` inductive; it sees arms of a structure field given by cases and the JSON
  `type` string arms of a request decoder). At `787333fc3` `fieldRead` had 33 constructor arms and
  one string arm in 10 Lean files; it now has none, and a declared kind cannot have one. The nine
  remaining kinds have 294 constructor arms and 16 string arms in 17 files.
* **One JSON vocabulary**: `EffectJson` (`Kernel/ResourceEffect.lean`) is the strict reading both
  a declaration's face and the Host's request decoders use; `Host/Json`'s private copies are
  deleted. (`Host/SourceAgreementJson.lean` still carries its own copy of the request decoder,
  payload arms included: seven of the sixteen string arms are its.)
* **Thin consent displays a registered observation without a view**
  (`NativeThinConsent.registeredRead`, `RegisteredReadDisplayStatement` proved): the effect's code,
  the signed operation's canonical bytes and `Effect.display`'s lines. A registered WRITE is still
  refused `unsupportedPayload` there.

* **`Effect.run` pays no frame check** (`Kernel/ResourceEffect.lean`): what the controller runs
  is the semantics and the guarded replay; `Effect.run_eq_exec` proves it is the engine's checked
  executor, from the declaration's `complete`.
* **Content's declaration is upstream of the registry and over the registry's context**
  (`Kernel/ContentEffect.lean`): `DeclaredResourceController.contentSpec : EffectSpec EffectCtx …`,
  with `contentSpec_complete` (frame and replay, the 450 lines that were in `ContentProofs.lean`),
  `contentSpec_writes` and `JointSlots.contentProject_unjoint` proved there. `EffectCtx` gained
  the two facts of the whole command a content write reads: `operation : Unit → Digest` (the
  operation id, computed when asked) and `sourceRead` (the observe capability of a cell the
  transaction reads observe-only). `Statements.lean`'s `contentSpec` is that declaration under
  `liveEffectCtx` (`comap`), so `ContentAgreement`, `PrepareFactors` and the teeth are now about
  the declaration the registry will bind. The hand arm still runs: code 1 is not bound.

* **Content is bound at code 1** (`contentEffect`, `Kernel/ContentEffect.lean`; JSON `content`).
  `Payload.content` the constructor, `Reject.content` and every content hand arm are deleted;
  `Payload.content` is now a `@[match_pattern]` abbreviation for `.registered 1 command`, so the
  code that builds a content payload or reads one out of a signed command (`match … | .content c`,
  `let .content c := … | none`) stands as written. Wire bytes of code 1 are unchanged (tag octet
  1, then `ContentResource.commandStream`).
  * Its JSON face is `Kernel/ContentJson.lean` (the request grammar moved out of `Host/Json.lean`;
    `Host/SourceAgreementJson.lean`'s private copy of that grammar is deleted and it now reads a
    registered payload through the registry too).
  * **`Effect.opens`**: what an operation claims of OTHER cells of its transaction (a list of
    cell id and a check of that cell as loaded). `openingsRefusal` replaces `openingsCheck`: every
    opening of every registered target names a cell the transaction reads observe-only, which
    holds it. Content's are its transclusions (`contentOpens`); the refusal is
    `Reject.effect (.refused 1 "staleOpening" …)`. `Target.contentStore?` is deleted.
  * **`Effect.viewDemand`** (default: the view, filtered): content's computes only the summaries
    a law names (`ContentResource.projectDemand`).
  * **The bridge** (`Kernel/ResourceTransaction.lean`): `computeTarget_content` and
    `computeTarget_content_arm` (a content target's computation is the deleted arm's expression,
    its refusal now `Reject.effect (.refused 1 name .empty)`), `targetPatch_content[_arm]`,
    `selectTarget_content`. The proofs written over the hand arm rewrite by these:
    `PreparedTarget.content_ratchets`, `transclude_requires_source_coverage`, `ContentAgreement`
    and its teeth, `HostTeeth`, the accepted and moved-root poles, `CommutingAppend`, `KeptPin`,
    `MovedRootAccepted`, `TwoAppendersOneObservation`.
  * **`HostKeystone` is proved** (`hostKeystone`), restated: `RegistryKeystone`, the registry's
    entry at code 1 is the handler DERIVED from `contentEffect`, and 1 is no hand arm.
    `liveLegacy = [0, 2, …, 8]`.
  * Refusal text moved: `Reject.content (ContentResource.Reject.staleAtom)` is now
    `Reject.effect (Effect.Content.staleAtom)`; the rendered clause `content-resource: stale-atom`
    is `content: stale-atom` (journeys `j12`, `j12w`, `j12e`, `j12m` follow).
  * A content cell is now SELECTED under any role and refused `wrongRole` by the computation
    (the declaration's `accepts`); the hand arm refused the role at selection. Same refusal.
  * A content write does not pass through a `List UInt8` on the registry path beyond what the
    codec itself is (`payloadStream` decodes the command from the signed command's bytes, as
    before); the operation is carried as `ContentResource.Command`.

**After the content binding (1 and 2 were owed and are proved; 3 on are open):**

The role is the one behaviour that moved place (selection no longer asks it; the computation's
header refuses it first). `PrepareProofs.lean` proves it did not move in value:
`ContentWrongRole` (the whole value of `prepareTarget` on a content target under a non-object
role is `missingTarget` or `wrongRole`), `ContentWrongRoleUncharged` (no prepared target, so no
preparation of any command holding one, so no compute or money plan), `ContentWrongRoleCommand`
(`prepareOn`'s refusal of a one-target command is `wrongRole`, after the clock and before
everything else), with `sampleWrongRole` and `sampleRole_teeth` on the sample cell.

1. `PrepareFactors` is proved again, restated for every bound code (`prepareFactors`): at a
   registered target whose slot is present, `prepareTarget` (post packed, refusals named under
   the code) is `dispatch hostRegistry` of the operation's bytes, then `genericChecks`. It names
   no effect; binding a code brings its receiver factorization with it.
2. `CommutingPrepare` is proved again (`commutingPrepare`), from `prepareTarget_packed`
   (`Kernel/ResourcePreparePacked.lean`): what `prepareTarget` answers, for every target, is
   `receive` of the slot, the selection, the computation and `afterTarget`, and of those only the
   computation reads the planned root. Any statement about the receiver at two targets, or
   against a dispatcher, is to be proved over that reading, not by walking `prepareTarget`.
3. The hand-written `contentHandler`/`contentHeader`/`contentFresh` (a spec-side twin of
   `contentEffect.handler 1`) are deleted, with `hostLegacy` and `HostPremise`. `HostTeeth`,
   `HostAccepted` and `HostMovedRootAccepted` are stated over `liveTargetDispatch` and the
   derived handler (`contentHostHandler`); the ghost is `Handler.unrotated` of it, not a handler
   written out. `RegistryPremise` is the premise for every bound code.
4. Thin consent refuses a content write (`unsupportedPayload`; the text is now the registered
   one, "content: a registered write is not displayed from a served view").

**The two root-pinning reads are bound** (`Kernel/ReadEffects.lean`): `readEffect` at code 3
(JSON `read`) and `kindReadEffect` at code 7 (JSON `kindRead`). Neither has an operand: the
operation is `Unit`, its codec writes nothing, so the wire bytes are the tag octet alone, as
before, and the JSON is `{"type": …}` alone, as before. `Payload.read` and `Payload.kindRead` are
names for `.registered 3 ()` and `.registered 7 ()` (not patterns: no function has an arm for
either); `sourceReadOf` and an opening's source still find the read by `payload = .read`.
`liveLegacy = [0, 2, 4, 5, 6, 8]`.

* Refusal text moved: a read whose capability is not its observe capability was
  `Reject.observationRequired` and is `Reject.effect (Effect.Read.observationRequired)`; the kind
  read's three (`observationRequired`, `observationRejected`, `fieldNotNamed`) are under
  `Effect.KindRead`. The header refusals (`wrongRole`, `unsupportedVersion`, `staleTarget`) keep
  the controller's names and their order.
* The role moved place as it did for content, and not in value: `RegisteredWrongRole`
  (`PrepareProofs.lean`) says it of every registered effect at every role its declaration does
  not accept, `ReadRoles` that the two reads accept an object and nothing else.
* Thin consent: a registered observation is displayed view-less only when it commutes
  (`registeredRead`). One that pins its root has the empty member patch and goes through
  `checkOpened` at the signed root like every hand arm (`memberPatch`, `Supported`,
  `computeTarget_root` by `Effect.compute_pinned`); `pinned_read_not_viewless` names the two.
  A member signing a `read` or a `kindRead` is shown what it was shown before.
* `Host/SourceAgreementJson.lean` reads `kindRead` now (through the registry), as it came to
  read `fieldRead`.

**Next**, the remaining codes: `kindDefinition` (5), `append` (2, needs a fresh-cell output),
`world` (4), `scalar` (0), `computeFunding` (6), `moneyConsent` (8). The three writes thin consent
displays today (`scalar`, `world`, `kindDefinition`) need the declaration to say which part of
its patch the member can compute from the signed operation and the served store, so that
`memberPatch` reads it from the registry: that field is the next change to `Effect`.

**The payload's JSON has one reader** (`Kernel/ResourcePayloadJson.lean`, `payloadOfJson`). The
grammar of the hand-armed payloads (`action`, `streamRef`, the world descriptor, definition and
action, the money batch) is `Kernel/ResourceGrammarJson.lean`, upstream of the registry, so a
declaration's `ofJson` can be one of its decoders when its code is bound. `Host/Json.lean` and
`Host/SourceAgreementJson.lean` each held a copy of that grammar and of the payload reader; both
are deleted. Which payloads a reader admits is its parameter (`refuses`): the Host's is empty,
the agreement's names `moneyConsent`, which it refuses by name before reading any of it
(executed in `Assurance/RegistryRefusalPoles.lean`). The agreement's refusal of a money consent
used to read "expected scalar, append, …"; it reads "moneyConsent is not admitted by this
reader". String arms: 11 before, 6 after (one reader, six hand-armed types).

## 1. What one effect costs by hand today (counted from the tree at `02ee34e8a`)

### 1a. One more declared-resource payload kind

The deployed write path is `Kernel.DeclaredResourceController` over
`Kernel/ResourceTransaction.lean`.  Its effect vocabulary is the `Payload` inductive
(`ResourceTransaction.lean:61`, nine constructors: `scalar`, `content`, `append`, `world`,
`kindDefinition`, `read`, `kindRead`, `computeFunding`, `moneyConsent`).  Each constructor is
handled by a hand-written case split in every function below.  These are the functions that
name a payload constructor, counted with a script over the source:

| file | case-split sites | functions |
|---|---|---|
| `Kernel/ResourceTransaction.lean` | 22 | `Payload`, its `Repr`, `payloadStream` (encode, decode, round-trip proof), `Target.observeOnly`, `Command.targetsWellFormed`, `payloadVerb`, `requestCost`, `Target.layout`, `Target.materializer`, `packTarget`, `selectTarget`, `computeTarget`, `targetPatch`, `appendedEntry`, `Target.contentStore?`, `targetProjection`, `targetWrites`, `moneyEntries`, `prepareOn`, `prepareCompute`, `funding_unvalidated`, `Reject` |
| `Kernel/DeclaredResourceController.lean` | 12 | `targetField`, `targetAmount`, `targetRatchet`, `targetFullFootprint`, `targetFootprint`, `targetProjection_unjoint`, `Target.isRead`, `moneyPolicySlots`, `moneyReadCovered`, `monetaryFootprint?`, `monetaryDebitFootprint?`, `monetaryVerbs?` |
| `Kernel/NativeThinConsent.lean` | 5 | `computeTarget_root`, `memberPatch`, `memberPatch_money_refused`, `Supported`, `targetPatch_split` |
| `Compiler/ObjectiveInvocationLayout.lean` | 3 | `inert`, `step`, `verbatim` |
| `Host/Json.lean` | 2 | `targetPayload`, `moneyConsentJson` |
| `Kernel/NativeObservationController.lean`, `Host/SourceAgreementJson.lean`, `Host/InspectRender.lean`, `Host/GrainOriginSource.lean`, `Host/FnInboxView.lean`, `Compiler/BendWorldPlan.lean` | 1 each | `streamPayload_sound`, `targetPayload`, `draftLines`, `render`, `targetJson`, `effectsOf` |

That is 49 hand-written arms in 11 Lean files for each kind, plus the Rust client's JSON
builders (`native/resource-client/src/workspace.rs`, `world_kind.rs`, `world_prototype.rs`;
`native/mini-sdk/src/contracts.rs`, `explain.rs`).  The most recent kind, `kindRead`
(`73d123885`), touched 20 files (+774/−26, together with the feature it served).  Two of
those arms are twins of each other: `computeTarget` computes a post store and `targetPatch`
recomputes the patch whose replay is that post.  `PreparedTarget`'s `postExact` and the
`Postcondition` of `targetFamily` exist to tie them back together.

### 1b. The activity effect (transfer, commit), the most recent hand-written kernel effect

| commit | what | lines (hand, excl. generated) |
|---|---|---|
| `a913a98c8` | `Effect` (`transfer`, `commit`), `PlanSource.performed`, `decodePlan`'s two arms, `transferVerdict`, `effectOps`, `withEffect`, `commitYield`/`settle` arms, the two-octet verdict wire, ACTIVITY-RECORD v8→v9 (`PersistedCodecTags`), a `funds` binder threaded through six downstream proof files, keystone stated | +716/−133, 10 files |
| `903642a83`, `e6c52a537` | audit pass 11 on the statements | +33 |
| `5e116ec9c` | keystone proved (`Kernel/ObjectiveActivityEffect.lean`) | +244 |
| `2aaf5ec9d` | the audit's four additions (`FundsAgree`, deposit independence, the law's teeth, the write clause) and a new refusal case (`Delivery.purseApart`) | +259/−12, 3 files |
| `2b9de2487` | build fixes | +7/−3 |
| `e6c7ed429` | six world apps re-expressed on the Plan; `check-preview.ts`; native scenarios | +885/−247, 9 files; plus +30,062/−16,881 of regenerated preview cohorts |
| `0fa0eb98c` | native rows, README, DOMAINS | +43/−16 |

That totals about +2,190/−410 hand-written lines over 7 commits and 2 audit passes, plus a
regenerated pins module.  No receiver arm was added: the effect rides the existing session
operations 210–214 (`Host/Main.lean:6228-6261`, `Kernel/NativeHost.lean:2500`).  The
keystone file is 717 lines, all hand-written for this one effect.

### 1c. The codec census

`Compiler/PersistedCodecTags.lean` registers 640 persisted identities and
`Compiler/PersistedCodecShapes.lean` pins 637 fingerprints.  The activity alone owns 28
identities.  §6 describes what a new payload kind does to this census.

## 2. What of the deployed contract a declaration must say

`DeclaredResourceController.step` (`:627`) builds the policy step context from the
prepared tuple: `projectWithCommon` (the target's projection plus the controller's common
slots), the pre cells (`policyPreCell`) and the post state (`policyPostState`, the replay of
the validated patch).  Around it, `admit*` (`:1755-2095`) runs the authority legs:
signatures, `verifyAndAuthorizeLeg` (verb and capability), `fieldsCheck` over the leg's
footprint, `lawLeaf` (the cell's committed law over the projected view), audiences and the
route.  Each item below is either per effect, so it belongs in the declaration, or generic,
so it belongs to the controller once:

| live function | per effect? | in the declaration as |
|---|---|---|
| `computeTarget` arm | yes | `sem : Ctx → O → State → Except R (List Prim)` |
| `targetPatch` arm | yes, a twin of the above | nothing: the descriptor `sem` emits is the patch (`emitted`) |
| blinding ratchet appended in both | yes (content, scalar) | `rotate`, `rotated` |
| `targetField`, `targetAmount`, `targetRatchet` | yes | `field`, `amount`, `rotated` |
| `targetFullFootprint`/`targetFootprint` | no: `footprintOf` over the three above | derived |
| `payloadVerb` | yes | `verb` (the authority demand) |
| `targetProjection` | yes | `view` (what the cell's law reads) |
| kind/version/root header checks (every arm) | data per effect, check generic | `accepts`, `version`; the check moves to the dispatcher |
| `payloadStream` arm | yes | `opStream` (its wire tag is the registry code) |
| `Target.layout`/`materializer`/`packTarget`/`selectTarget` | yes | the handler's substrate, `select`, `pack` |
| `targetWrites` (Nock run claim) | no for content and stream (the op's bytes) | derived from `opStream`; `scalar`/`world` need a `runWrites` field (step 4) |
| `appendedEntry` (a fresh cell) | stream only | a fresh-cell output, needed at step 4 (`append`), not for content |
| signatures, read legs, audiences, common slots, route, Objective admission | no | controller, untouched |
| the law itself | no: the cell's own data | not in the declaration (only its `view`) |

## 3. The widened declaration (`Effects/Revival/Statements.lean` §1-§3)

* `Substrate`: a state with guarded primitives (`step : Prim → State → Option State`), a
  syntactic footprint per primitive, an observation per location, and the frame law
  `Framed`.  `storeSubstrate L` is the deployed one (`Theory.Store.Op`, guard
  `Op.Enabled`, footprint `writeAddress?`).  The Book's posting algebra is the second one,
  for transfer.
* `EffectSpec Ctx S O R`: `opStream`, `refusalName`, `accepts`, `version`, `sem`, `rotate`,
  `rotated`, `field`, `amount`, `frame`, `verb`, `view`.  Derived from it: `emitted` (the
  full descriptor) and `exec` (sem, then a loud frame check `outOfFrame`, then the replay
  with every guard, loud `guardFailed`).  `Complete` is its proof obligation: neither
  dispatcher refusal is reachable, so every refusal is one the declaration names.
* `Handler` (substrate, declaration, the controller's header check, `select`/`pack` into a
  common cell universe, inverse both ways, so a dispatch cannot rewrite a cell outside its
  selection unseen),
  `Registry := List (Nat × Handler)`, the one `dispatch`, and `LawfulRegistry` (codes
  unique, every handler `Sound ∧ Complete` as proof fields, ATLAS §4's packed-handler
  shape).

### Where this disagrees with the deputy, and why

1. **`sem` emits a patch, not a post state.**  The deputy wrote `sem : Op → State → Except
   Refusal State`.  The deployed path commits a guarded patch.  `computeTarget` and
   `targetPatch` are a twin pair today, held together by `postExact`.  If the declaration
   emits the descriptor and the post is its replay, the twin disappears (law 13), and the
   address-level frame comes free from `Patch.run_frame`.  The deputy's
   `Except Refusal State` is `exec`'s shape, derived.
2. **A context argument `Ctx`.**  The content arm reads the author (subject, kind,
   capability), the operation id (`contentOperation`), the document (`documentOf target`),
   the height and the transaction's source reads (`contentContext`).  None of these are
   the op's payload.  Putting them in `Op` would make `Op` carry a function
   (`Context.sourceRead`) and break the syntactic-payload law (N3).
3. **The frame is fields within one cell.**  The deputy wrote "the cells an op may touch".
   One target is one cell by typing: a declaration's `sem` sees only its own cell's state,
   so it cannot touch another cell.  The frame that has content is the one capability
   scopes bound: `CellField`s (K-FIELDS).  The dispatcher checks the declared frame at run
   time and refuses `outOfFrame` (law 10).  `Complete` proves that check unreachable for a
   lawful declaration, as `prepareCell_ok_of_run` does for `invalidPatch`.  Stream append's
   fresh entry cell is the one case of a second cell.  It needs a fresh-cell output and is
   deferred to step 4.
4. **The authority demand is a verb plus a view, not a `Pred`.**  The `Pred` a write must
   satisfy is the cell's committed law.  The cell's owner chose it and `lawLeaf` judges it.
   It is not the effect's.  The effect contributes the verb its capability must allow
   (`payloadVerb`) and the view the law reads (`targetProjection`).  Admission keeps
   checking the actual footprint against the scope (`fieldsCheck`).  A check of the
   declared frame against the scope before execution would be stricter than today, and
   could refuse commands that are admitted now.  It is left as a later decision, not
   slipped in.
5. **The keystone is a predicate on any dispatcher, with a `legacy` set.**
   `Dispatches R legacy d` takes the candidate `d` as an argument, so a misreading,
   fail-open or unframed dispatcher can be refuted (§4 below).  Defining agreement as
   "`dispatch` equals lookup" would hold by `rfl` through our own reader, which is the
   vacuity the auditor rejected in PlatformCell.  `legacy` names the codes that are still
   hand arms during the migration.  The `noTwin` clause forbids a code from being both
   registered and hand-armed.  The end state is `legacy = []`.
6. **The first declaration is the whole content code, not "append".**  `doc append` signs
   a `Payload.content` target holding `createAtom` plus one `insertRun` per tail run
   (`native/resource-client/src/workspace.rs:5373`, `document_actions`).  It is wire code
   1, and the `content` arm serves all fifteen content actions.  An arm can only be deleted
   for a whole wire code, so the first declaration covers the content action grammar.
   `doc append` is the verb that exercises it.

## 4. The dispatch keystone and its ATLAS fields (`Statements.lean` §4-§6)

| statement | claim | satisfiable | teeth | premise inhabitation |
|---|---|---|---|---|
| `EngineKeystone` | over sound handlers, `Dispatches R [] (dispatch R)` | `EngineSatisfiable`: the two-entry `toyPole` dispatches through itself, admits entry A's `5`, refuses entry B's out-of-frame `false` with `outOfFrame 1` | `EngineTeeth`: refutes the ghost reading (`toyGhostPole`), the fail-open dispatcher (`toyFailOpen`), the unframed dispatcher (`dispatchUnframed`), and a twin (`legacy = [1]`) | `EnginePremise`: every pole handler is sound |
| `CompletenessKeystone` | through a `LawfulRegistry`, every refusal is a declared name | `CompletenessSatisfiable`: entry A lawful, its `tooLarge` surfaces as `refused 0 "tooLarge"` | `CompletenessTeeth`: entry B is not lawful | `CompletenessPremise`: a lawful registry exists |
| `HostKeystone` = `RegistryKeystone` (`Dispatches hostRegistry liveLegacy liveTargetDispatch`), the registry's entry at code 1 the handler derived from `contentEffect`, and 1 not a hand arm | today's target dispatch (payload decode, `selectTarget`, `computeTarget`, patch validation, `packTarget`) dispatches through the one-entry registry, every other payload code in `hostLegacy`; `noTwin` puts code 1 out of the hand arms | `HostAccepted` (the doc-write fixture, owed) | `HostTeeth`: refutes the registry with the seal-less content handler, and code 1 kept as a hand arm too | `HostPremise`: `contentHandler.Lawful` |
| `LiveKeystone` = `ContentAgreement contentSpec ∧ ContentComplete` | the deployed content arm (`computeTarget`, `targetPatch`, `targetField`, `targetRatchet`, `targetAmount`, `payloadVerb`, `targetProjection`) agrees with `contentSpec`; `contentSpec` keeps its declared frame (`contentActionFrame`, per action) | `ContentAccepted`: the live arm admits some content command (intended inhabitant: `Fixtures/NativeDocWriteFixture*`) | `ContentTeeth`: refutes the declaration without the blinding seal (`contentGhost`) and the frame without `annotations` (`contentNarrowed`, `annotate` writes there) | `ContentAccepted` |

`Dispatches R [] (dispatch R)` is the engine's generic theorem, in the same role as the old
`derived_agrees`.  Its content is the discrimination its teeth show.  The deployed content
is `ContentAgreement`: a refinement of today's hand arm, which can be false.  Its clause 2
also tests `contentFrame`, because a live-admitted command that wrote outside the declared
frame would make `exec` refuse it.

`HostKeystone` is the deployed keystone, stated now (the auditor's pass 19): over the
controller's own cell universe (`PackedCell Registry`), against today's target dispatch.
It is **known false today**, by clause: an unknown payload tag is refused `malformed`, not
by name (`unregistered`), and code 1 is still the hand arm, which `agreement` matches only
if `ContentAgreement` and `ContentComplete` hold.  The migration commit makes it true by
rewiring the payload decoder through the registry and deleting the content arms; it is
that commit's gate.  `ContentAgreement` alone would license keeping both arm and
declaration; `HostKeystone`'s `noTwin` is what forbids it.

**The label, said exactly (pass 19):** what is derived after step 1 is the dispatcher, the
frame, the checks and the patch/post relation (one descriptor, its replay).  The content
semantics itself is still the source-owned lowering `ContentResource.run`, reused by
`contentSpec` as it is by `computeTarget`; that is why `ContentAgreement`'s clauses 2 and 5
are near-identities and its real content is clause 4 (refuted by `contentGhost`) plus
`ContentComplete`.  Deriving the lowering itself (its actions as a declared vocabulary
over the hyperdocument layout) is a later rung, not claimed.

## 5. Migration order (each step deletes its hand arm in the same commit)

The commits that follow the opening.  The Host arm belongs to the platform lane (L1,
`lane/lean-critical`).  Per the deputy's seam, one lane holds both sides of each step.

1. **Content (wire code 1, `doc append`).**  The target payload becomes a registered
   operation: an octet code plus that handler's op.  The outer target decoder reads the
   octet and decodes with the handler's `opStream` prefix decoder, exactly as
   `payloadStream`'s tag-1 arm does today, so no byte changes.  The same commit deletes
   the content arms of `computeTarget`, `targetPatch`, `targetField`, `targetAmount`,
   `targetRatchet`, `targetFullFootprint`, `targetProjection`, `Target.layout`,
   `Target.materializer`, `packTarget`, `selectTarget`, `Target.contentStore?`,
   `targetWrites`, `payloadStream` and the `Repr`, and with them `Effects/EffectSpec.lean`
   and `Effects/Placeholder.lean`.  The old engine's `moveEffect` is over the undeployed
   `KernelState`.  Its `derive` is superseded by `Substrate.run`, which is the descriptor
   replay, so keeping it would leave a twin.  The gate is `LiveKeystone` plus
   `HostDispatches` with `legacy` shrunk by 1.  The Host presentation arms
   (`Host/Json.targetPayload`, `SourceAgreementJson`, `InspectRender.draftLines`,
   `FnInboxView.targetJson`, `GrainOriginSource.render`) also need a face from the
   declaration.  **Open:** either a `json` codec field on the declaration, or a JSON layer
   over canonical op bytes.  If neither lands in step 1, those five arms stay as twins,
   and step 1 is not done.
2. **Transfer (activity `Effect.transfer`).**  The substrate is the Book: `Prim =
   CanonicalResourceKernel.Operation`, `step` the floor-guarded posting, `writes = {(source,
   asset), (destination, asset)}`, `field = balance asset`.  `sem` is `transferVerdict`
   over `(config, funds, reserve, written)` as `Ctx`.  A refused verdict (`unfunded`,
   `reserved`, `closed`) is NOT the declaration's refusal.  It is an accepted yield whose
   await records `.performed (.refused reason)` and that commits nothing, so `sem` returns
   `.ok []` with the verdict in the emitted await, never `.error`.  The gate is `TwoLevels`
   (`ActivityStatements.lean`, proved of today's `commitYield`) for the derived executor
   projected to a `YieldCommit`.
   `commitYield`'s `performed` branch dispatches through an activity registry (the same
   `Handler` type, over the activity's turn cell).  Deleted in the same commit:
   `Effect.transfer`, `effectOps`, `withEffect`, the transfer branch of `commitYield`, and
   `ObjectiveActivityEffect.lean`'s Performed/Refused statements for transfer, which become
   instances of the generic agreement plus the activity's own agreement.
3. **Commit (activity `Effect.commit`).**  The substrate is the object's declared state.
   `sem` is `stateWrite`, and its refusal is the object's law (`objectWrite reason`).
   This is the one effect whose refusal is a law judgment inside `sem`.  The declaration
   names it as a refusal and does not move the law into the declaration.  Deleted in the
   same commit: `Effect.commit`, its `decodePlan` arm, and the commit branch of
   `commitYield`.
4. Then the remaining declared-resource codes, each with its arms deleted: `append` (2,
   needs the fresh-cell output), `world` (4) and `kindDefinition` (5) (need `runWrites`),
   `scalar` (0), `computeFunding` (6) and `moneyConsent` (8) (their footprint override,
   `monetaryFootprint?`, becomes a declared `amount`), and the observe-only reads (3, 7),
   which are declarations with an empty `sem` and the observe verb.

## 6. What the codec census and regen must learn

Today: adding a `Payload` constructor changes `payloadStream`.  That moves the fingerprint
of `NativeProtocolFrames.commandFrame` (`"DREGG/RESOURCE/TRANSACTION" ++ [14]`) and of
`familyCommandFrame` (`++ [15]`).  Both frames carry a raw version octet, and
`scripts/codec-shapes-regen.py` cannot bump a raw octet: it exits 2.  The bump is then a hand
edit across Lean and Rust, and every pin nesting the frame moves.  So adding an effect is a
flag day on the transaction frame.

To make adding a declaration a mechanical bump:

1. **Registry-derived identities.**  Each handler's `opStream` is its own persisted
   identity (`DREGG/EFFECT/<NAME>/vN`), declared by the registry entry, not by a hand
   `@[persisted_codec_tag]` line.  The census enumerates the registry as part of the
   reachable set, and `PersistedCodecTags` gains those entries from it.
2. **The table is not in the frame's fingerprint.**  The transaction frame's fingerprint
   hashes the dispatcher, not the registry list.  It is paired with a proved
   `Registry.Extends R R'` (every old code keeps its handler, so every old byte string
   decodes to the same value).  Adding a code is then a compatible extension: the frame
   does not move, a new identity and pin appear, and regen emits them.  Changing a
   handler's codec moves only that handler's `/vN` identity, which regen already bumps
   mechanically.
3. **Raw-octet bumps.**  For the frames that keep a raw octet, regen learns
   `"P".toUTF8.toList ++ [n]` → `[n+1]` in Lean and in the Rust spellings, instead of
   exiting 2.
4. **Wire neutrality of step 1** is a check, not an assumption.  The registry code is one
   octet, the same as `payloadStream`'s tag.  It is not `StreamCodec.nat`, which encodes
   digits plus a 255 terminator, so a `nat` code would change every target's bytes.

## 7. Checking

Nothing in this lane runs Lean on the Mac.  Check command in a warm tree on dregg-ref, from
the tree's root:

    swarm-build lake lean Effects/Revival/Statements.lean

(`lake lean`, not `lake env lean`: the lakefile's `leanOptions` and `moreLeanArgs` apply.)
`Effects/Revival/Statements.lean` is not yet imported by `Effects.lean`.  It joins the CI
closure (law 5) in the commit after it elaborates.

## 8. Continuation (for a successor; present state, 2026-10-28)

**Where the lane stands.**  Every statement is auditor-accepted (passes 19-28 on
`lane/audit-platform`), and every proof of them is accepted too.  All are kernel-checked
(`#assert_axioms`).  `Effects/Revival` holds no `native_decide`, `#assert_compiled` or
`sorry`.  On main through `ae0c78a01` (merge `ac4247487`).  `f46beaa46` (PrepareFactors) was
sent to the integrator and the auditor on 10-28.

**Files** (all `module`s written by `scripts/lean-modularize.py`, never hand-edited headers;
`Effects.lean`, `Effects/EffectSpec.lean`, `Effects/Placeholder.lean` stay non-module because
EffectSpec imports the non-module `Kernel.State`; both old files die at the migration commit):
- `Engine.lean`: the kernel-free engine (substrate, declaration, registry, dispatcher,
  `Dispatches`, keystones, toy pole, census/one-source/extension, prefix consumption).
- `EngineProofs.lean`: engine, completeness, census, one-source, extension, prefix proofs.
- `Statements.lean`: the live content declaration, `ContentAgreement`, `HostKeystone`,
  `PrepareFactors`, `HostLegacyCensus`, live prefix agreement.
- `ContentProofs.lean`: `contentComplete`, `contentAgreement`, `contentAccepted`,
  `contentTeeth`, `hostAccepted`, `contentPrefixAgreement`/`Accepts`/`Teeth`,
  `hostLegacyCensusRefutedToday`.  The witnesses are hand-built cells: a link at a store that
  holds only its blinding (`blindedStore`, `sampleDeployment`, `sampleHostCtx`).
- `HostTeethProofs.lean`: `hostTeeth`.  The cSHAKE256 fact `ratchet_moves` is decided by
  `decide +kernel`, in under a minute.
- `PrepareProofs.lean`: `prepareFactors : PrepareFactors contentSpec`.
- `ActivityStatements.lean` / `ActivityProofs.lean`: `TwoLevels` (with `verdict`, `ok`,
  `turn`) and its satisfiable, premise and teeth poles.

**So:** `LiveKeystone` holds with its poles.  `HostKeystone` has its poles, and the keystone
itself is known false until the migration (it is that commit's gate, with `HostLegacyCensus`).
`PrepareFactors` holds today, so rewiring `prepareTarget`'s content branch through `dispatch`
preserves behaviour.

**Checking.**  hbox private tree `/tank/lanes/effects-revival/src` was synced to the merged
lane (main `d6f0372d8` plus the lane) on 10-28 and has the whole `Effects` closure built as
modules.  To check files: `scratchpad/effects-revival/hcheck.sh <module>...` (rsyncs `Effects/`
and `Effects.lean`, runs `check.sh`, which writes `check.pid`, `swarm-build lake build`).
After a main merge that touches the closure, re-sync the tree with
`rsync -a --delete --exclude=.lake --exclude=.git --exclude=target --exclude=.claude ./
hbox:/tank/lanes/effects-revival/src/`, then start `/tank/lanes/effects-revival/rebuild.sh`
detached.  It writes `rebuild.pid` and `rebuild.log`, builds kernels, then `lake build Effects`.
Lean never runs on the Mac.

**Owed, in order.**
1. **Both recorded fixtures, with run-relative charge lanes** (the integrator's ruling (c),
   10-28; the coordinator is copied).  Deliverable: ONE sha, built on a box with
   `lake build Fixtures`, sent to the integrator (`a34bdb948f1cf4796`).  Until then the umbrellas
   stage is non-fatal.
   - **Why.** A second acceptance run with the same 349e59ef1 binaries gives different byte
     counts: an a2 call of 1015 bytes against 1013, and record lengths 6396/1881/2192/2538
     against 6394/1880/2185/2531.  Per-run random values are written as variable-length
     naturals.  So the hand-written `write.charge.turnBytes = 1047` / `storageBytes = 1474`
     (doc-write) and `first.charge.storageBytes = 3969` (accepted) are luck.
     `first.charge.turnBytes = 2000000` is the signed capacity, which is deterministic; check
     it stays exact.
   - **The change** (one commit, trailer `Authority-Change: the turn and storage byte lanes
     measure run-dependent encodings`):
     - Charge lines today are built in `Fixtures/NativeAcceptedFixtureProjection.lean:169`
       (`first.charge.*`) and `Fixtures/NativeDocWriteFixtureProjection.lean:62`
       (`write.charge.*`), both `toString (record.exactCharge lane)` over `lanes`.  Keep every
       lane exact except the run-dependent ones.
     - doc-write `turnBytes` becomes a relation line, e.g. `write.charge.turnBytes = call+32`,
       emitted only when `exactCharge .turnBytes = callBytes.length + 32` (1045 = 1013 + 32),
       else a line naming both numbers.  The call bytes are the fixture's `callHex` (pass the
       length into the projection).  The constant 32 must be traced to its source, the signed
       frame overhead the Host charges.
     - `storageBytes` (both fixtures) becomes `= legs+images+event`, checked against
       quantities measured independently of `DeployedCharge.storageCharge`.  That function is
       `storageOf history creates legs event` (`Kernel/DeployedCharge.lean:61-71`); re-calling it
       would be the vacuous version.  Use the record's own byte lengths (each leg's encoded
       bytes, each born/post image's canonical bytes, the event's canonical bytes) and say in a
       comment which component each is.
     - The authority texts (`Fixtures/NativeDocWriteFixtureAuthority.lean`,
       `NativeAcceptedFixtureAuthority.lean`) change those lines to the relation spellings.
   - **Teeth (required).**  A fixture theorem showing that a `turnBytes` off by one from
     call+32 is refused by the projection (the relation line does not appear), and the same
     for storageBytes.  A relation that admits any number would be the vacuous version.
   - **Re-record both** from candidate `349e59ef1`:
     - doc-write: the world is ready at `/tank/lanes/effects-revival/world-349e59ef1` (hbox);
       run `/tank/lanes/effects-revival/gen.sh` again after the projection change.  It uses the
       hbox-built verifier, because the candidate's binary needs glibc 2.41.
     - accepted: run its acceptance driver (see `scripts/native-accepted-fixture/generate.sh`'s
       header for the world script) from the same candidate on dregg-build in your own run
       directory, copy the world to hbox, run that `generate.sh`.
     - The hbox tree (main 5e819cb1d, no .lean change since 349e59ef1) has every dependency
       built and a bare `git init` for the scripts' `rev-parse`.
     - The re-recorded data files and the projection/authority edits are .lean changes: build
       `Fixtures` on hbox (`rebuild.sh Fixtures`), commit named files, push, send the sha.
2. **Commuting appends (qualification ruling, 10-28).**  Append-only `createAtom` content
   commands are to admit at any signed root if they admit at `pre.root`; every other content
   action still refuses `staleTarget`.  The keystone worker is `a76c092a8eda237ca`
   (`lane/qualify-doc-contention`).  The root pin is hand-stated today in three places:
   `computeTarget`'s content arm, `contentHeader`, and `ContentAgreement` clause 3.  Clause 2
   is stated only at `pre.root`.  The proposal sent to the worker: a declaration field
   `commutes : O → Bool` from which the header's root check is derived; clause 3 conditional on
   `commutes = false`; clause 2 generalised to every root when the command commutes; the kernel
   arm changes in the same commit.  The statements go to the auditor first.  Then re-prove
   ContentProofs (`computeTarget_content_header`, clause 3 of `contentAgreement`, the host
   witnesses), PrepareProofs and the HostTeethProofs header.  Never hand-edit the clause
   outside this.  **Owner: `a76c092a8eda237ca`, who took it on 10-28 on `lane/qualify-doc-contention`
   with this design (its commit messages carry a pointer).  This lane only reviews.**
3. **The migration commit** (§5 step 1; post-demo; prepare, never land without the
   coordinator's word).  The gate is `HostKeystone` and `HostLegacyCensus` (both provable
   only after it) plus the already-proved `PrepareFactors`.  Its shape:
   - `Payload` loses `content` and gains `registered (code : UInt8) (op : List UInt8)`, with
     canonical op bytes.  `payloadStream` reads tag octet 1 through `readPrefix` of the content
     registry: `ContentPrefixAgreement` says no byte changes.
   - `prepareTarget`'s registered branch becomes `dispatch` then `genericChecks`; this is
     `PrepareFactors`' right side.
   - The content arms of `computeTarget`, `targetPatch`, `targetField`, `targetAmount`,
     `targetRatchet`, `targetFullFootprint`, `targetProjection`, `Target.layout`,
     `Target.materializer`, `packTarget`, `selectTarget`, `Target.contentStore?`,
     `targetWrites` and the `Repr` are deleted in the same commit.
   - About 25 Lean consumers construct or match `.content cmd`.  The heaviest are
     `Kernel/NativeHost.lean` (about 20 sites), `HyperdocumentPublication`,
     `HyperdocumentMergePublication`, `CanonicalCellRegistry`, the Fn consumers and
     `Assurance/HyperdocumentQueryDeployment`.  They build the registered payload from
     `ContentResource.commandStream.encode`.
   - The Host presentation arms (`Host/Json.lean:1380`, `SourceAgreementJson.lean:1082`,
     `GrainOriginSource.lean:167`, `InspectRender.draftLines`, `FnInboxView.targetJson`) need
     the declaration's JSON face.  It is still open which: a `json` codec field, or JSON over
     canonical op bytes.  Without it those arms stay as twins, and step 1 is not done.
   - `Effects/EffectSpec.lean` and `Effects/Placeholder.lean` are deleted.  `Effects.lean`
     then converts to a module.
   - Persisted identities move: `payloadStream` and the transaction frame.  The integrator
     plans the raw-octet bump; this is a re-genesis by the whole-epoch design (§8 item 4
     below), which re-genesis at the homelab absorbs.
4. **Migration step 2 (transfer)** must satisfy `TwoLevels` for its derived executor projected
   to a `YieldCommit` (§5 step 2, corrected 10-28: a refused verdict is an accepted yield).
5. **Whole-epoch compatibility** (design only; no local handler upgrade is promised until it is
   built).  Today `StoreEpoch.current.schemaRefs` hashes the whole persisted corpus, and opening
   is equality, so every registry change is a re-genesis.  The design:
   - the seed carries the corpus itself;
   - opening becomes "H ⊇ S, one fingerprint per identity, a `SafeExtension` registry delta",
     where `ExtensionPreserves` and `PrefixKeystone` give old-byte preservation;
   - a codec change is a new `/v(N+1)` identity, and the old one stays readable;
   - the first record under a code outside S appends an epoch step;
   - the theorem to prove then is "EpochCompatible S H implies replay under H equals replay
     under S".

**Not this lane's:** the census and regen changes (§6); the raw-octet bump (the integrator's).
