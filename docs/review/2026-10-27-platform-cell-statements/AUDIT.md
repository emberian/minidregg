# Platform cell statements: adversarial audit

Object: `Kernel/PlatformCell.lean` at `lane/lean-critical` 984fb241 (statements commit af8832d1), against
GENESIS-COUPLING §C L1/M2, `Kernel/PayBookReceiver.lean:150-260`, and registry codes 240-247. Read, not elaborated (no warm `.lake`).

## Verdicts

| statement | verdict |
|---|---|
| `Admits` (the spec all keystones share) | WEAK: unauthenticated signer, no record validity, empty history admits anything |
| `VersionMonotone` | WEAK: true list lemma; the inductive invariant (admission preserves `Sorted`) is missing |
| `ControllerOnly` | VACUOUS: `P ∧ Q → P` |
| `BirthsReadCurrent` | WEAK, close to a proxy: no height, no tie to the birth receiver, creation tariff only |
| `InstallSatisfiable` | SOUND (as a pole of `Admits`) |
| `InstallTeeth` | SOUND as stated; incomplete (no zero-lifetime or invalid-record teeth) |
| `HistoryInhabited` | WEAK: a singleton list; does not inhabit the premises of `VersionMonotone` |
| `Decides` / `ignoresSigner_not_decides` | SOUND shape; inherits every `Admits` weakness |
| `RefillLawful` | WEAK, and unrealisable by the deployed path: ignores the refill record's own meter debit |
| `refillReference_lawful` | SOUND |
| `lawful_monotone` | SOUND (pointwise per lane, stronger than the sum); one-step scope only |
| `replaces_not_lawful`, `anySigner_not_lawful` | SOUND |

## Per statement

**`Admits controller history install`** says: `install.subject = controller`, and for every `current`
with `history.getLast? = some current`, `current.version < install.next.version`, and
`0 < install.next.lifetime`. (1) `install.subject` is a field the requester writes; "controller-signed" is not modelled. The
deployed authority is the controller's `installPolicy` capability on the cell and a verified Ed25519
signature (`PolicyInstallReceiver` carries subject, capability id and signature; `NativeHostGenesis`
`controlCapability`). This is law 12 and law 4: the statement binds a claimed name, it does not force
the signer. (2) On `history = []` the version conjunct is vacuous, so any install at any version
(including 0) is admitted; the design says genesis's record is always first, so `History` should be
`Platform × List Platform` (genesis, installs), making the empty case unrepresentable. (3) No record
validity. PayBook's monotone theorem carries `next.valid`; here an install with `grainBirth = some ⟨0, _⟩`
is admitted although `Config.grainBirthTariffValue` refuses base 0, so every grain birth after it fails.
A custodian key not 32 bytes is admitted too, and `some key → none` silently turns checked completion
off. Separately, `controller : SubjectId` is a free parameter: every theorem holds for every subject, so
nothing pins the deployment's `factoryController` (law 3: instantiate the deployed value).

**`VersionMonotone controller`**: for every history and install, if the history is `Chain'` strictly
increasing in version and `Admits` holds, every record in the history has version below the install's.
True and non-vacuous, but a fact about lists: nothing states that the cell's history IS sorted. The missing
keystone is the invariant: `Sorted h → Admits c h i → Sorted (h ++ [i.next])`, or better, an inductive
`Reachable genesis : History → Prop` (genesis, then admitted installs) with `Reachable h → Sorted h`.
Without it the `Sorted` premise is never inhabited by any deployed object (law 5). No teeth pole shows
`Sorted` is load-bearing (`[v5, v1]` with an install at v2 is admitted and not above 5).

**`ControllerOnly controller`**: for every history and install, `Admits controller history install`
implies `install.subject = controller`. That is the first conjunct of `Admits`; the proof is
`admitted.1`. Restate over the receiver and the signature:
for the deployed receiver `post`, `post store req = .ok _ → SignatureVerifies controllerKey req ∧
holds store controller installPolicy platformCell`, with teeth a forged-subject request (subject field
equal to the controller, signature by another key) refused.

**`BirthsReadCurrent priceAt`**: for every history and every `current` that is its last element,
`priceAt history = some current.creation`. (a) There is no height. Whoever calls `priceAt` chooses the
list, so a birth receiver that reads a stale prefix satisfies it. "At their height" needs the birth's
pre-state: `priceAt (platformAt store) = ...` where `platformAt` reads the platform cell in the store
the birth commits against, with the cell itself under `rootsMatchCheck`. (b) `priceAt` is arbitrary; nothing names the deployed quote (`Host/Json.lean:2341`): a carrier
without a realizer slot (law 1). (c) Only `creation` is constrained; the grain
birth tariff, custodian key and `{ownerBudget, lifetime}` are not, and the design's "grants carry an
explicit window" (window = birth height + current lifetime) is absent. (d) No poles: no satisfiable
reader exhibited and no teeth (a reader of `history.head?`, the genesis record, after one install).

**`InstallSatisfiable controller`**: there exist genesis (version 0) and next (version 1, lifetime > 0)
with `Admits controller [genesis] ⟨controller, next⟩`. Exhibited concretely with `freeTariff`; a pole of the spec; the proof phase owes the receiver pole (`genesis_change_accepted`
shape, `decide +kernel` on the genesis store).

**`InstallTeeth controller`**: (i) for every history whose last record is `current` and every `next`
with `next.version ≤ current.version`, the controller's install is not admitted; (ii) for every
`other ≠ controller` and any next, `⟨other, next⟩` is not admitted. General refusals for the right reason; (ii) is only as strong as the unauthenticated subject field. Missing: zero lifetime refused, invalid record refused.

**`HistoryInhabited`**: some list has a last element. `[x]` proves it. It does not inhabit
`VersionMonotone`'s premises jointly (sorted, at least two records so `Chain'` fires, plus an admitted
install), and once `History` carries genesis by type it is redundant. Replace with `∃ h i, Reachable h ∧
h.length ≥ 2 ∧ Admits c h i`.

**`Decides controller decide`**: for every history and install, `decide h i = true ↔ Admits c h i`.
Right shape; `ignoresSigner_not_decides` refutes the signer-blind receiver for any
`other ≠ controller`, at `[]`, the corner that should not exist. Worth exactly what `Admits` is.

**`RefillLawful controller post`**: for every remaining meter and refill, a refill whose subject field
is the controller yields `some (raised remaining refill)` (lane-wise sum), any other yields `none`. Same
unauthenticated subject. Worse: the deployed path debits every record. `DurableCommitProtocol.preflight`
refuses `insufficientBudget` unless `exactCharge` is funded from `available`, and the post-state is
`available - charge`. So (a) a deployed refill's post-state is `raised (remaining - charge) refill`,
not `raised remaining refill`, and no receiver on the derived path satisfies the statement unless refills
are exempted from the meter, which nothing states; (b) at an exhausted meter, the moment M2 exists for,
preflight refuses the refill itself. The statement must decide this: either refills are charge-exempt
(and say so, with a pole at `remaining = 0`), or the post-state includes the debit and a liveness pole
shows a refill admitted when `remaining` is below an ordinary record's charge. Replay is also
unaddressed: a refill has no identity, so the same signed posting re-submitted adds twice unless the
nullifier/receipt path refuses it; state that refusal. The issuance-cap half of design M2
(`wellFloorAmend`, lowering refused below current negation) is not stated at all.

**`lawful_monotone`**: given a lawful `post` and `post remaining refill = some next`, every lane of
`next` is at least the same lane of `remaining`. Pointwise (implies the sum); one refill transition only, which the label should say.

**`replaces_not_lawful` / `anySigner_not_lawful`**: concrete hostile receivers (overwrite at
remaining 1, amount 0; any-signer at `other ≠ controller`) refuted. Real teeth.

## The three changes before proof work

1. **Model the signature and the deployed controller.** `Install` and `Refill` carry the capability
   id and signature (as `PolicyInstallReceiver` does); `Admits`/`RefillLawful` require verification
   under the controller's enrolled key and possession of `installPolicy` on the platform cell;
   `controller` is the Config's `factoryController`, not a free parameter. Replace `ControllerOnly`
   with the receiver-level statement plus a forged-signature teeth pole. Decide and state whether the
   completion custodian key may be rotated by the controller alone: Host calls it the "distinct"
   custodian key, and controller-only rotation collapses that separation; at minimum refuse
   `some → none` or require the custodian's co-signature.
2. **Make the history the cell's and give it a height.** `History := genesis × installs`; add
   `Reachable` and the `Sorted`-preservation keystone; add record validity to `Admits` (grain base
   positive, key length 32, positive lifetime, PayBook's `valid` shape). Restate `BirthsReadCurrent`
   over the birth's pre-state store, covering all platform fields and the explicit grant window
   `height + lifetime`, with a stale-reader teeth pole.
3. **Reconcile M2 with the meter debit.** State refill charge-exemption or the debited post-state,
   add the exhausted-meter liveness pole and the replay refusal, and either state the issuance-cap
   amendment or record that it is out of this lane.

## Registry 240-247

Well formed (`reserved`, no routes, no receiver; Rust mirror matches). Three issues. (a) `owner: "platform"` on the meter-refill family: the meter is the
durable commit protocol's seed meter, not a platform-cell field, so either the refill posts to the
platform cell (and the statement should say the meter lives there) or the owner is wrong. (b) The
design names a `platformInstall` family and a `platform` kind `.lawBearing`; the design's alternative
for M2 is extending `realmWell` or a `purseRefill` sibling, and reserving a separate `METER_REFILL_*`
family pre-empts that choice without recording it. (c) Every active SUBMIT in the registry is `effect: append`; these two must flip at activation, and the
registry check should refuse an active SUBMIT with `effect: none`.

## 2026-10-27, second pass: the restatement at cc5ebd26

Deltas only.

| statement | verdict |
|---|---|
| `Authorized`, `Admits` | WEAK: right shape, but `Context.auth` and `Context.encode` are free |
| `StaysSorted`, `VersionMonotone`, `RecordsValid`, `Reachable` | SOUND, except `Reachable.genesis` accepts any valid record, not the deployment's |
| `ReceiverAuthenticated`, `forged_refused`, `trustsSubjectField_not_decides` | SOUND relative to `auth`; teeth real |
| `CustodianStep` / `CustodianNeverDropped` | Drop branch SOUND. Rotation branch has NO POLES |
| `premises_inhabited`, `sorted_load_bearing`, `stale_version_refused`, `invalid_refused`, `zero_lifetime_invalid` | SOUND (poles over `toyAuth`) |
| `BirthsReadCurrent`, `BirthQuoteCurrent` | WEAK: `platformAt = none` is an escape; `BirthQuoteCurrent` has no poles |
| M2 exemption (`RefillChargeExempt`, both poles) | TRUE of `preflight` |
| `RefillLawful` raise | A HOPE: `install` cannot raise `available` |
| `replay_refused`, `forgetful_not_lawful`, `anySigner_not_lawful` | SOUND |
| registry | SOUND |

**The exemption is true; the refill is not realisable.** `DurableCommitProtocol.preflight` refuses
`noCells` only when `rootWrites = [] ∧ nullifiers = []` (line 300), so a nullifier-only intent passes,
and a zero `exactCharge` passes `fundedCheck` (line 310). But `install` (line 162) sets
`available := before.available - intent.exactCharge`, and `Intent` (lines 55-61) has no credit field.
A nullifier-only, zero-charge intent leaves the meter exactly where it was. No intent the protocol can
express produces `raised m.remaining r.amount`. `Meter` is a parallel model of `Snapshot` with no theorem
linking them (law 5). Fix, stated here first: add `Intent.credit`, set `available := before.available - exactCharge + credit`, and
state who may set a nonzero credit: only the refill family, via `RefillAdmits`. Without that, any family
could mint meter. The conservation theorem at lines 227-228 then has to carry the credit term. Add a teeth pole refusing an overflowing credit (the `Theory.ResourceCost` width
boundary).

**Rotation hole: closed on paper, untested.** Naming a first key (`none → _`), drop refused, rotation
only with `verifiesKey old bytes s`: the rule is right. But `toyAuth.verifiesKey` is constantly
`false`, so no pole exhibits a cosigned rotation being admitted. No pole shows an uncosigned rotation
(`some a → some b`, `a ≠ b`, no cosign) refused either; `custodian_drop_refused` covers only the drop.
Add both. `CustodianNeverDropped` is a corollary of `custodian_drop_refused`, not a keystone.

**Realizer slots are still prose (law 1).** `Context` is any `(config, auth, encode)`.
`verifies := fun _ _ _ => true` makes `forged_refused` vacuous (its premise never holds) and every
statement accept forgeries. `verifiesKey := true` reopens rotation. Worse, `encode` need not cover
the record: `toyContext.encode` signs only `[version]`, so a relay could swap the tariff or the new
custodian key under a valid controller signature and custodian cosign. The fix: define
`Context.deployed snapshot config`, with `verifyNative`, `capabilityEvidenceChecked` and the family
codec, quantify the keystones over that alone, and state `encode` injective on `(next, nonce)`.
The same applies to `RefillContext.encode` (the toy signs only the nonce, so the amount goes unsigned).

**Births.** `BirthsReadCurrent` and `BirthQuoteCurrent` constrain only stores where `platformAt` returns
`some`. A store whose platform cell is missing or undecodable may be priced arbitrarily. Add the
conjunct `platformAt store = none → terms store = none` (and `quote … = none`). `BirthView` is free in
the same way `Authority` is, so `currentReader_reads_current` holds by definition. Its teeth
(`genesisReader_stale`) are real. `BirthQuoteCurrent` needs a satisfiable pole and a stale-tariff teeth
pole.

**Small.** `Install.nonce` is never read by `Admits`; install replay is refused by the version clause,
so either drop the nonce or say it is codec-only. `Reachable.genesis` should be
`g = genesisRecord ctx.config`. Refill nullifiers `(subject, nonce)` share the durable nullifier space
with every other family, so they need a family tag.

**Before proof work:** the `Intent.credit` statement, deployed-context quantification with injective
`encode`, and the two rotation poles.

## 2026-10-27, third pass: the restatement at 89dc0e17



| delta | verdict |
|---|---|
| deployed `Deployment`, transcript boundary, `Reachable.genesis = genesisRecord host` | SOUND (boundary stated) |
| `covers` / `wireEncode_covers` / `relay_swap_refused` | SOUND |
| rotation poles `cosigned_rotation_admitted`, `uncosigned_rotation_refused` | SOUND |
| births: absent-cell refusal, `currentQuote_current`, `genesisQuote_stale` | SOUND |
| `Install` nonce dropped | SOUND: an old signed install is below the current version |
| `install_conserves_with_credit`, `installToday_loses_credit`, `overflow_refused` | SOUND as targets, but about a local mirror |
| `CreditConfined` | WEAK: confines by a self-declared tag |
| `family_tag_separates` | SOUND but constructor-trivial; same mirror |

**The meter is still a mirror (law 5).** `installAvailable`, `MeterIntent`, `Meter` and the tagged
`Nullifier` are local to this file. `DurableCommitProtocol` is unchanged, so "the refill's post-state is
the install of its own intent" holds of `installAvailable`, not of `install`. The keystone that makes M2
about the deployed meter is missing. State it now as a Prop: once `Intent.credit` exists,
`(install before intent).available = installAvailable before.available (meterView intent)`, and
`Meter` is `⟨snapshot.available, snapshot.consumed⟩`.

**`CreditConfined` checks the tag, not the source.** Its clause is `family ≠ .meterRefill → credit = 0`.
Any producer that labels its intent `.meterRefill` can mint credit, and the teeth only refute an honestly
mislabelled intent. The confinement that matters is: `committed intent → intent.credit ≠ 0 →
∃ m r, RefillAdmits ctx m r ∧ intent = r.intent`. Its teeth: a `.meterRefill`-tagged intent with credit
and no admitted refill.

**Residuals:**
- The custodian's first key is the controller's choice, and nothing stops the controller naming its own
  enrolled key. `verifiesKey` and `verifies` read the same transcript triples, so the controller's own
  signature would then count as the custodian's cosign. Add `key ≠ keyOf controller` to the
  naming step, or state the trust-on-first-name boundary next to the transcript boundary.
- `Deployment.host` and `Deployment.genesis` have no coherence premise: the controller comes from one,
  the genesis record from the other.
- `wireEncode` has no deployment or domain tag. Across worlds, replay protection relies on the
  envelope pinning `expectedSemantics` (`Host/Json.lean:2322`); cite that in the boundary note.
- `holdsInstall`, `holdsRefill`, `keyOf` and `layout` are still free functions, which is the declared
  realizer boundary.

**May proof work start?** L1 (platform cell, births, custodian): yes. M2: after two statement-level
additions, the install-link Prop and the source-confined `CreditConfined`; proving against the mirror
would reproduce the integration gap ATLAS law 5 names.

## 2026-10-27, fourth pass: the receiver, the holder law, the plan-time birth verdict (6fffa0de)

| item | verdict |
|---|---|
| `admitsObserved_decides` | SOUND as "gate = spec", relative to the oracles |
| `receiverDecides`, `receiverContext` | WEAK: synthetic store, and the signed bytes are not `encode` |
| `installPatch_record_only` (controller fixed) | WEAK: installs only; genesis and other writers not covered |
| custodian rotation by raw cosign | SOUND |
| `unsigned_refused`, `delegate_refused`, `controller_install_admitted` | real gate poles; they do not touch the codec or the signature path |
| `holderPolicy` and its five theorems | SOUND for mutations; "nothing else" overstated |
| capability check before the law | SOUND |
| `grainPolicy_member_witness_refused` | motivating closed instance, not teeth of `holderPolicy` |
| `birthRefusal` | no agreement theorem; three divergences |

**(a) Receiver.** `admitNative` is the real path (`verifyNative`, `authorize`, `cosignAnswer` under the `old`
key `decideRecord` read from the same loaded cell, then the gate). The cosign covers `commandCodec.encode command`, which includes `expectedPlatformRoot`,
so it cannot be replayed onto another pre-state. Rotation is closed. Two gaps:
1. *The sponsor does not sign `encode i`.* The envelope is over the `signingHeader` of `request …`,
   which commits to the command only through `argsDigestBytes` (a cSHAKE of the command bytes and the
   declaration). `receiverContext.encode` is `commandCodec.encode`. So the real verifier's transcript has no entry over
   `encode i`, and the `sponsor` hypothesis of `admitsObserved_decides` cannot be discharged from a real
   receipt. `receiverContext` is never used. Fix: make the context's `encode` the signed header bytes, and state `covers` through the
   header (with hash collision-resistance named as a boundary beside the verifier's).
2. *`receiverDecides` runs the gate on `genesisStore controller h.current`,* a store built from the
   spec, and feeds it the spec's own `oracle`. It is a corollary, not a theorem about the loaded
   cell. Missing: for every durable snapshot reached from genesis,
   `PlatformCellDomain.load` yields `recordOf = some h.current` and `controllerOf = some
   genesis.factoryController`. `installPatch_record_only` is the install half; the genesis
   half and "no other family writes the cell" are missing.

The poles posit `Observed` booleans; add one pure pole through `prepare` on a concrete snapshot.

**(b) Holder law.** For verb-2 mutations outside the refill slot, `holderPolicy_nonowner_only_witness`
forces `witnessCaveat`, which zeroes all four `State` deltas: settlement and management are
unreachable through the witness form. But the outer `.any` also admits verbs 1 and 3 (observe, delegate) and the refill edge
for every non-owner. A holder may re-delegate its parent grant, so witness authority spreads at
holders' discretion, bounded only by the grant carrier's attenuation. Restate it as "nothing else among mutations", or keep delegate out of member grants. Ordering holds: `DeclaredResourceController.authorizeLeg` (lines 706-717) obtains capability evidence
per leg before the law is judged, and `law.admit` consumes it by type.

**(c) Plan versus submit.** `birthRefusal` evaluates `Pred.eval law.predicate step.oldState
step.newState`. `admitBranch` runs `law.admit wanted evidence law.witness …` after the epoch and
revision checks. Divergences: (1) unlike `invokeRefusal`, it skips the range and cast verdicts, so a
`policyInputRange`/`policyCastAlias` refusal at submission stays undisclosed;
(2) a `prepareDraft`/`preparePending` failure at plan returns `none`, so the plan is silent;
(3) plan and submit prepare at different heights and snapshots. The statement owed, on one snapshot
and height:
`birthRefusal … (.birth b c) = some _ → ∀ cred r, (pending.admitBranch .factory cred r) is .error`
(a plan refusal is never one submission would admit), and
`admitBranch … = .error .policyRejected → birthRefusal … = some _` (every law refusal is disclosed).
Both need `law.admit … ≠ none ↔ eval ∧ ranges ∧ casts`.
Across time, claim only that drift makes the submission stale.

**Before proofs:** (a) signed-bytes `encode` and the loaded-cell controller invariant; (b) the
"nothing else" scope fixed; (c) the agreement statement, with range and cast in `birthRefusal`.

## 2026-10-27, fifth pass: fast-forward open statements (lane/hot-path-codec acad2eb7, HOT-PATH §2(h))

| statement | verdict |
|---|---|
| 1 MAC gate over v4 | SOUND (about the deployed `openSealed`) |
| 2 suffix extends snapshot | SOUND, with one unstated scope (truncation) |
| 3 exactness over snapshot + suffix | NOT WELL-TYPED against today's `Loaded`; `representsCheck` cannot run |
| 4 keystone | WEAK: premise is provenance the open cannot decide, no teeth; must be an induction; needs World equality |
| 5 audit | SOUND; needs a refusal pole |

**1.** `openSealed` (`DurableCheckpointCodec.lean:693`) is the deployed gate; its check order matches
the named poles, and the MAC hashes `bodyStream.encode body`, so the new fields are covered.

**2.** Real, but a tail-truncated suffix (rollback to any height above the checkpoint) is accepted,
as replay accepts a truncated log: state it, or bind the open to the head anchor (`headTag`).

**3. The blocking finding.** `Loaded` carries `image : Image` with
`chainExact : chain = chainAfter logStart image.accepted` and
`indexExact : index = PresenceIndex.ofRecords image.accepted` (`DurableReceiverCore.lean:981-1009`).
`representsCheck` (`DeployedRepresentsCheck.lean:68`) reads `image.accepted` for the nullifier keys,
the transaction ids and `w.head = image.accepted.length`. An open that "reads no entry below the
checkpoint" has no `image.accepted` for the prefix. Statement 3 either re-reads the prefix or cannot be built. Before elaboration, `Loaded` needs a
checkpoint-relative shape: `prefix : Body` with
`chainExact : chain = chainAfter prefix.chain suffix`, indexes `= prefix.ix.extendFrom prefix.height
suffix`, and `representsCheck` restated over the six indexes (keys from `spentAt`, txs from `txs`,
head from `height`) instead of `image.accepted`.

**4. Keystone.** (i) *Circularity.* An ff-opened `L` inherits `B`'s World, so its next seal is the replay's value only if `B` was. State it inductively: define `HostWritten key fold : Store → Prop` (genesis; append; a seal by
`storeCheckpoint` of a `Loaded` from either open of a `HostWritten` store). Then prove
`HostWritten s → ∀ checkpoint at h, body = replayBody fold (s.prefix h)`. Inhabitant: the genesis Store plus appends. (ii) *No teeth at the open.* `Body` has no semantics or World-fold identity, and the key is the Store's. A Host binary with a different World
fold that opens the same Store seals under the same key and passes gate 1. "A Store this Host wrote"
is a provenance premise the open cannot decide (law 1). Fix: put `profile.semantics` and a
`worldFoldVersion` in the v4 body (under the MAC) and refuse a mismatch by name (`.foreignFold`). The
teeth pole is then expressible: a body sealed with another fold identity is refused. A same-version fold divergence stays audit-only; say so.
(iii) *`representsCheck` is not enough.* It checks consistency, not equality: `rowOk` is `true`
for every `.head`/`.allowance` row, and spent/journal rows are checked for membership, not value. A `system` that differs from the fold in those rows passes. The keystone
must state `B.system = (foldWorld (prefix h)).system` (and `decodeCells B.state` equal to its cells).
`representsCheck` stays a guard, not the trust argument.

**Light session** (`DurableServed.lean:1059`). It must hold `track` and state, per append,
`track' = WorldTrack.advance track record` (the `ofIntent_run` step). At a seal it must state
`lightSeal L = storeCheckpoint transport rootBytes L indexRoot` byte for byte, so the light sealer is
one more constructor case of `HostWritten`, not a third body producer. `checkpointDifferential` (`:2080`) and the audit
(`DurableStoreAudit.lean:213`) likewise: all three call one `bodyOf L`.

**5.** Add a pole: a Store whose checkpoint at `h` differs from `replayBody` in any field (system
included) is refused naming `h`. A fold divergence is caught nightly, never at open.

**Before `DurableFastForwardSpec.lean`:** the checkpoint-relative `Loaded` and an index-based
`representsCheck`; the fold identity in the v4 body with its refusal; the keystone as `HostWritten`
induction concluding World equality; one shared `bodyOf` for the three sealers.

## 2026-10-27, sixth pass: `Compiler/DurableFastForwardSpec.lean` (lane/hot-path-world-checkpoint 93e94fa2)

| statement | verdict |
|---|---|
| `Derived`, `Body4`, the three `Honest` | SOUND: every field pinned to the genesis replay; World by equality |
| `MacGate`, `MacGateRefusals` | SOUND, but vacuous in isolation (below) |
| `SuffixGate` | SOUND; the anchor closes the foreign-checkpoint hole at the open |
| `TailCutAsReplay` | WEAK: existence only; cuts below the checkpoint uncovered |
| `Exact`, `Wrote`, `Keystone` | SOUND in shape; one `step` for two sessions |
| `AuditSound`, `AuditRefuses` | SOUND |
| `HeadSealZero` | SOUND; the only pole forcing `seal4`/`open4` to round-trip |

**Trivial instantiations.** `ff` cannot replay: its type receives only the checkpoint, the anchor and
the suffix. `bodyOf` cannot carry nothing: `Body4.Honest` pins every `Derived` field. But each `def`
takes its own parameters. With `decode4 := fun _ => none`, `MacGate` holds, and then the checkpoint
branch of `Exact`, `reopenCheckpoint` and `SuffixGate` all hold vacuously (their premises need
`open4 … = .ok`). Only `HeadSealZero` forces `ff` (hence, through `SuffixGate`, `open4`) to accept
`seal4`'s output. **Bundle them:**
one structure `Spec rootBytes logStart semanticsId open4 step bodyOf seal4 ff audit` holding all
eleven, plus `SealOpens : open4 key (seal4 key b) = .ok b` (for this key and semantics), plus an
inhabitation pole: a `Wrote` derivation through `append`, `seal` at a positive height, and
`reopenCheckpoint`.

**Foreign checkpoint versus backup.** `Wrote` reopens only from `(height, body) ∈ store.checkpoints`.
At the open itself the hole is closed by `SuffixGate`'s anchor clause: the stored entry at the body's
height must carry this key's trailer over `body.chain` and its world root, so a different Store's body
fails unless its chain is this one's. An atomic backup is an earlier `Written`, so restore is covered. A non-atomic backup (a checkpoint newer than the copied entries)
leaves the anchor missing. State the Host's selection: the newest checkpoint whose height is at most
the head, falling back to genesis.

**`TailCutAsReplay`.** It needs no named refusal. Rollback detection rests on the signer's `headTag` (ruling (f)). But "as the genesis
replay opens it" is not what it says. It asserts only that some `view'` exists, and only for cuts
inside the suffix. Strengthen it: the cut opens to `View.Honest` of `⟨seed, records.take n⟩`, for
every `n`, including cuts below the newest checkpoint, through the selection rule.

**Light session.** Whole-World equality (`world = worldAt image`) is the right strength. Per append it is the `foldRecords` append step. But `Wrote`
has one `step` and one `genesisView`, while the light session (`DurableServed`) is a separate code
path. Add a `lightAppend` constructor or a theorem `lightStep = step` on `View`; otherwise the light
session is outside the keystone.

**`Loaded` reshape.** Yes, state it now. `View` fixes the observable part, but `representsCheck`,
`chainExact` and `indexExact` still read `image.accepted`. Add `LoadedView : Loaded → View` with
`View.Honest image (LoadedView L)` as the invariant, and `representsCheck` restated over `Derived`.

**Verdict:** proofs may start once there is the bundled `Spec` with `SealOpens` and the inhabitation
pole, plus the light-session clause in `Wrote`. Strengthen `TailCutAsReplay` and add the `Loaded`
Prop in the same commit.

## 2026-10-27, seventh pass: Option A spec (lane/hot-path-v4 41099e07)

**Verdict: unsatisfiable as stated; one change before proofs.**

**`executesNoPrefix` against `exact`.** `exact` requires `view.snapshot = replaySnapshot ⟨seed, pre ++ suf⟩`.
That snapshot is `State.snapshot state (image.accepted.take height)` replayed (`DurableCheckpoint.lean:101-115, 151-156`).
Its model's `journal`, `history` and `consumed` are built from the prefix records. `executesNoPrefix` sets
`view.snapshot = stateSnapshot state` with `state` from `ffState`, whose inputs are the checkpoint and suffix only. Option A
takes the journal out of the checkpoint, so `ffState` has no source for the prefix journal. Two prefixes giving the same body
(a chain collision, which exists by counting) would demand two snapshots from one input. Fix: split the snapshot.
`executesNoPrefix` should speak of the executed part only (`roots`, `available`, the World). Add a clause that `journal`,
`history` and `consumed` are a pure function of the decoded `below ++ suffix` (the same non-executing rebuild as the indexes).

**Does it forbid execution?** Only extensionally. An `ff` that replays the prefix as a check and then returns the
checkpoint's World satisfies it. A fold divergence does break it: a replaying `ff`'s World differs from `ffState`'s, which
reads `body.world`. Non-execution is a cost claim, so make it structural. Define `ff` in `Impl` as
`ffState` ∘ `rebuild (decode below)` rather than a free field, and the type then proves it. That is ATLAS law 5: one
executable path, no twin.

**Dropping the anchor.** Safe, and stronger. The recomputed prefix chain must equal the MAC'd `body.chain`, which binds every
prefix byte, not one tag.

**Tamper guarantee.** The same as the sixth pass for the reader, but it now rests on the chain hash's collision resistance
rather than on per-entry KMAC tags. Name that boundary in the spec's header beside the MAC's.

## 2026-10-27, eighth pass: `Theory/ReceivingVerifier.lean` (lane/un-pred-census 726e1c09)

State of the tree: the module is imported by nothing, `Theory/Receiving.lean:105` still has the old
`Vouchers verify`, and `Ran` does not exist yet in `Compiler/CredentialSignatureAdmission.lean`. So this
pass judges the shape.

| statement | verdict |
|---|---|
| `Verifier`, `pureVerifier` | SOUND |
| `Vouchers` (private `mk`) | WEAK: `ofAnswered` is public, so the privacy is cosmetic; the docstring's "only use is `admitVia`" is false |
| `not_verified_of_not_answered`, `pure_false_not_verified`, `pure_observed_eq` | SOUND teeth, relative to `V` |
| `exists_for_true`, `pureVerifier_poles`, `Verifier.exists_refuting` | SOUND, but all at `Id` |

**(a) Index.** The deputy's worry is right. `Verifier IO` is an open structure:
`⟨fun _ _ => True, fun _ => pure (.ok ⟨true, trivial⟩)⟩` builds without the shim, and `Vouchers` over it
carry nothing. `Theory/` cannot name `receiverVerifier` (import boundary), so the index belongs one layer up.
Every deployed receiver's `prepare`, and every top-level receiver theorem, must be stated at
`Vouchers receiverVerifier`, never `∀ V`. Generic `∀ V` lemmas stay in Theory as tools. Add a census row:
no `Verifier IO` value besides `receiverVerifier`, and no deployed receiver whose type is polymorphic in `V`.
Either drop `ofAnswered` and mint only in `admitVia` (keeping `mk` private), or correct the docstring. The
proofs, not the privacy, carry layer 1.

**(b) `Ran` outside the shim.** A private constructor is unreachable from other files, but `Ran` leaks
through anything its own file exports. Before the conversion lands, check: no lemma or def in that file
returns `Ran q b` for caller-chosen `b` other than the shim; no derived or explicit `Inhabited`/`Nonempty`/
`Decidable` instance for `Ran`; no `unsafe` or `@[implemented_by]` near it (`#assert_axioms` does not see
`unsafe`). Then the only inhabitant is the shim's post-`verify` mint, which is the named layer-2 trust.

**(c) Pilot.** Enough to prove the shape, on three conditions. The pilot must use both `verified` and
`observed` (a `false` answer the family decides on), not only `verified`. Its top-level theorem must be
stated at `receiverVerifier`. And it must carry an IO-level teeth pole: an ingress whose signature the
shim answered `false` yields no voucher for it, which is `not_verified_of_not_answered` instantiated at
`Ran`. Today every satisfiable and inhabitation pole is at `Id`; the pilot must give one at `IO`.

## 2026-10-27, ninth pass: lane/hot-path-v4 571f9981

**Verdict: proofs may start.**

`Impl.ff` (:210) is now a definition: `ffState` (whose type has no prefix), then the chain gate (prefix count
equals `stateBase.1`, the recomputed chain equals `stateBase.2`, and `suffixGate` pins that pair to the MAC'd
body), then decoding. A replaying `ff` cannot be written. `Opened.view` (:224) pairs the executed part
(`stateHead`, `stateWorld`) with `rebuildDerived` and `State.snapshot head records`, so the prefix journal,
history and consumed set come from decoding, and the pass-7 contradiction is gone. `exact` (:346) pins the
executed head's snapshot over `pre ++ suf` to the replay's, and the World to the fold's. It is satisfiable:
a v3 `resume` at `height = length` is exactly `State.snapshot st records`, and a head state exists because
`storeCheckpoint` seals at any height. The laws are bundled: an `ffState` that always errors fails `exact`,
`inhabited` and `headSealZero`. `viewOpened` ties `ofOpened` to the open's view.

One note for the prover. The first lemma `exact` needs is that replaying the suffix from
`State.snapshot base pre` equals `State.snapshot head (pre ++ suf)` for the head state the executing part
builds (roots by `rootTable`, consumed, journal, history). If that equation fails at some corner (a
retired cell, absent bytes), suspect the `State.snapshot` shape before the prover. The `representsCheck` of
earlier passes is replaced by `representsFromDerived`; no change is needed.

## 2026-10-27, tenth pass: `Kernel/ApplicationStreamContinuityFresh.lean` (lane/un-stream-continuity 351dab72)

**Verdict: not yet; two changes before proofs.**

**The left side is weaker than "a fresh opening read".** `Held.verifiedRead : Option (List UInt8)` is a bare
option, and `decide` verifies no MAC. Admission reduces to "some tag equals the tip's tag, and the record and
height equal the tip's". A re-read that copies the tip entry's tag into `verifiedRead` without running
`DurableHistory.Head.verify` satisfies the iff, so the authentication the docstring promises is absent from
the statement. Fix: make `verifiedRead : Option {tag // Head.verify key height record tag = true}` (the
verifier `readerWith` uses), or add that conjunct to the iff. `headTag`'s authentication is `Loaded`'s
invariant; name it as a hypothesis in the same shape.

**Deployed path.** `decide` is called "the pure core of `withOpenedFreshTip`"
(`ApplicationStreamContinuity.lean:208`), but nothing ties them, and today's `withOpenedFreshTip` does not
call it. Add `withOpenedFreshTip_refuses : … = .ok _ → decide … = .admitted`, or define the IO by `decide`,
in the same commit.

**Teeth.** These are named refusals, but as closed `decide +kernel` instances (law 9). The general content
is the iff plus `noRead_noAdmission`, which is adequate. Stale and forked tips share `.tipChanged`; that is
acceptable.

**`Loaded.extend` dropping the tag.** It is a defect against `Loaded.headTag`'s own docstring ("read from
(or appended to) the Store"). `extend` (`DurableReceiverCore.lean:1434-1480`) is pure and cannot know the
tag, but the IO append that wrote the entry computed it under the key. The cleaner fix is
`Loaded.withHeadTag` set by the append path, with
`appended_headTag : (append …).headTag = some (DurableHistory.trailer key height …)`. That makes the
re-read unnecessary on the Host's own path. Keep (a) for robustness only. Pin the append lemma in this
statement module too, so the fix cannot regress to `none` silently.

## 2026-10-27, eleventh pass: `Kernel/ObjectiveActivityEffect.lean` (lane/un-effects 60cd8f64)

**Verdict: proofs may start on Performed, Refused, Verdict, TransferMoves and Resumed. Three
statement additions come before the Delivery\* and CommitJudged proofs.**

**On the deployed path.** Yes. `commitYield`, `transferVerdict` and `settle` are the kernel's own
functions, and the Delivery\* statements quantify over `Delivery`, whose `batchExact` (`ObjectiveActivity.lean:3296`)
is the deployed batch. The ordering is right: `settlePurse` checks `pair + deposit` on the purse after the
delivery's charges AND the effect transfer (`:2456-2461`), so a transfer can never leave the purse
underfunded. Safety holds even where the verdict errs.

**`VerdictStatement` is complete over `transferVerdict`'s four outcomes** (reserved, closed, unfunded, settled).
But it judges against `funds.book`, which for a delivery is `applyOperations book (purseCharges …)`
(`deliveryFunds`, `:3119-3123`). The batch applies `deliveryCharges …`, and nothing states that these
agree on the purse balance and the open-account set. If they disagree, a transfer judged `settled` is
refused at `settlePurse` as `awaitsFunding`, which refuses the whole turn under the wrong name, or a
covered one is recorded `unfunded`. **Add `FundsAgree`:** the purse balance and the `accounts` of
`funds.book written` equal those after `deliveryCharges` (and likewise for the birth's funds, `:2722`).

**Storage-deposit independence is asserted, not stated.** The verdict is judged with the reserve of a
`settled` await (`commitYield`), while `settlePurse` charges the deposit of the record actually committed,
whose await may be `refused r`. They agree only because `VerdictWire` is two octets for every verdict (a
comment at `:255`). **Add** `storageDeposit config (nextRecord … ⟨…, .performed v, …⟩)` independent of `v`.

**`CommitJudgedStatement` binds to the same `admitWrite`** that `Delivery.judged` (`:3318`) uses, with the same
`factsOf payer height object 2 (some pin)`, so a commit and an await are judged by one law. But (i) it is an
instance of the existing `judgeWritten_ok delivery.judged` (`:5207`), so it adds no content beyond the
`Delivery` field. (ii) Births (`:2781`, other facts) are not covered, though a first segment can yield
`commit`. (iii) Its "a law-refused commit admits no turn" has no pole. **Add** a birth clause and a teeth
pole: an object whose law refuses the write makes `deliver` return `.error (.objectWrite _)`. Also
inhabit the premise `committed.written = some _`: `SatisfiablePole`'s `commit {write: {}}` may build
`none`.

**Deputy's additions.** (a) *Issuer well as `config.asset`:* this is the kernel's convention, not invented
here. `CanonicalResourceKernel.lean:63` says "an asset is named by its issuer-well account", and `:150`
says "the asset identifier is its issuer-well identifier". `AccountId` and `AssetId` are both `Nat` (`:64-65`), and
`ObjectiveActivity.lean:3721` already refuses `request.account = config.asset` as the issuer well.
(b) *`TeethPole`* is quantified over the context but fixed in its numbers (purse 10, reserve 3, amounts 8
and 1). It is a non-vacuity witness, which law 9 permits, not the general teeth. The general shape is
`RefusedStatement` with `VerdictStatement`'s refusal clauses, so that is adequate. Its docstring's
"purse, recipient and state untouched" is not in the Prop; that claim belongs to
`DeliveryRefusedStatement`, so the docstring should point there.
(c) *Changed conclusions.* `Delivery.yield_reserves_deposit` now reads the purse after the effect transfer
too. That is **stronger**: a transfer only lowers the purse, so the old conclusion follows. Justified.
`commitYield_spec`'s write clause went from `stateWrite … = .ok committed.written` to
"∃ built, stateWrite = .ok built ∧ committed.written = some w → built = some w". That is **weaker than
needed**: it is justified only for a refused transfer, which drops the built write, but it gives up equality
for every other plan, and for `none`. Restate it as `committed.written = built ∨
(committed.await.source = .performed (.refused _) ∧ committed.written = none)` so consumers of the
equality keep it.

## 2026-10-27, twelfth pass: L1 restatement 7e39fe90 (pass-4 (a) gaps)

**Verdict: two of the three gaps are closed. Proofs may continue. Two statement items are owed before
the receiver is called "decided on the deployed cell".**

**Gap 1, signature coverage: CLOSED.** `receiverContext.encode current i = m.frame current (commandAt roots i)
i.validUntil`, the signed header's frame that `verifyNative` receives. `CredentialSignatureAdmission.prepare`
refuses unless `controller.envelope.header = header snapshot … validUntil` (`sourceBinding`), so the frame
is the receiver's own. The custodian cosigns the same frame.

**`PinCollision`: a real collision, not the old vacuity.** Its two fields are `source p i ≠ source p j`
and equal `pinDigest customization` of exactly those two strings. It is inhabited only by an actual
cSHAKE collision on compared inputs, which matches the `ArgumentCollision` pattern. `Context.binds` derives
it from `pins` (realised through `frame_effectsDigest`) and `sourceCovers` (the injective codecs). No
statement takes it as a free escape.

**Gap 3, a pole through the real path: CLOSED.** `signed_command_admitted` builds the ingress with
`ingressCodec`/`commandCodec`/`canonicalEnvelopeCodec`, decodes it back, shows the envelope frame is
`encode`, and admits through the gate and `Admits` with the verdict recorded under the enrolled key. That
is the transcript boundary, as agreed.

**Gap 2, decided on the loaded cell: HALF.** `Reachable.controller_stays` and
`platform_written_only_by_install` (from `kernelOnly [.platformInstall]`) are proved. `receiverDecides`
now quantifies over any loader satisfying `Reachable` and `holds`. Two things are still owed. (i) The bridge
from the deployed loader: for every durable snapshot the Host reaches, `PlatformCellDomain.load d snap =
some L → Reachable d.controller L.cell.logical`. This is the conjunction of the writer theorem and a
genesis clause. (ii) The genesis clause has no producer. `NativeHostGenesis` seeds no platform cell
(no `PlatformCellLayout.genesisStore` in the seed), so on today's genesis `load` is `none` and every
install is `platformUnavailable`. That is expected until L1's re-genesis, but state it as the owed
keystone, not leave it as a hypothesis.

**`validUntil`: checked, but by the verifier, not the spec.** The deployed path refuses an expired
header: `CredentialSignedEnvelopeController.prepare` tests `envelope.header.validUntil < state.height`
(`:293`) against the request's admission height (the Host's logical height, not a wall clock), and it
surfaces as `CredentialSignatureAdmission.Reject.expired`. But `PlatformCell.Admits` never mentions
`validUntil`, so the spec admits an expired install that the receiver refuses. Soundness holds (the
receiver refuses more), but `receiverDecides` covers only the gate. Add `height ≤ i.validUntil` to
`Admits`, with a teeth pole `expired_refused`, so the spec and the full receiver agree.

## 2026-10-27, thirteenth pass: prefix entries with tags (hot-path-v4; judged on the described amendment)

The pushed tip (`107f040d`) still passes record bytes, so this pass judges the amendment as described.
**Verdict: nothing from passes 7 and 9 breaks, on one condition.** `ffState` still has no prefix in its
type, so execution stays impossible. The added prefix `verifyTags` from the seed's chain is a further
refusal, and an honest Store passes it because `exact`'s `OwnEntries` already verifies every entry's
tag, so `exact` stays satisfiable. Reading receipt roots from the tags is decoding, not execution. The
reader's prefix guarantee moves back from chain-hash collision resistance to KMAC; update the header.
**The condition:** the root log read from the tags is new served state. `Opened.view`/`View` must carry it,
and `View.Honest` must pin it (each entry's receipt root equals the replay's root at that height), or `exact`
and `keystone` leave it unstated.

## 2026-10-27, fourteenth pass: partial `ofOpened` and `reopens` (hot-path-v4 aa025c8d)

**`reopens` is the right form.** It is stated under `exact`'s hypotheses, not over `Wrote`, and that is
the stronger and more reusable choice. A `Wrote` reopen already carries `ofOpened opened = .ok loaded`
as a premise, and every `Wrote` checkpoint is honest by the keystone, so a per-`Wrote` restatement would
only be a corollary. `inhabited` now includes a successful build.

`reopens` is true only if the build refuses nothing the replay accepts. Both of its checks meet that bar:
- *Nullifiers:* a suffix record carrying a prefix nullifier fails `preflight`'s `nullifiersFreshCheck`
  (`.alreadyConsumed`).
- *Transaction ids:* `DurableCommitProtocol.execute` (`:427`) answers a recorded transaction id with
  `.replayed`/`.transactionConflict`, never `.accepted`.

So the proof rests on `replay` demanding `.accepted` for every record; cite that lemma. Admissibility for
`pre ++ suf` from admissibility for `pre` should follow from `mem_cellIds_append`.

**Missing teeth: the build's soundness.** `viewOpened` and the keystone constrain builds only on Stores
this Host wrote. Nothing states what a successful build guarantees on a MAC-valid Store whose suffix
reuses a prefix nullifier. Either instantiate `Loaded4 := Loaded`, so the real resume proof makes it hold
by type (say so in the spec), or add `buildSound : ofOpened opened = .ok loaded → (impl.view
loaded).snapshot = (protocol resume of the image)`, with a teeth pole: a suffix record carrying a prefix
nullifier makes `ofOpened` refuse.

**Addendum, fce764f7.** `buildSound` (`:391`) has the right shape, but `Impl.stateCheckpoint` (`:214`)
appears in no gate. Nothing ties it to the MAC'd body's `state` (or to `State.ofSeed seed` from genesis),
so the law is relative to whatever starting state `ffState` reports. Add `stateCheckpoint state =
body.body.state` to `suffixGate` and `stateCheckpoint state = State.ofSeed seed` to `genesisGate`.
Then `buildSound` is about the checkpoint the reader authenticated.

**Addendum, un-effects 2aaf5ec9: the pass-11 additions are stated. Proofs may proceed.**
- `FundsAgreeStatement` states agreement on purse balance and open accounts for every `written`. Its
  birth clause holds by definition. The disagreement it found (the submitter or the collector is the
  purse) is now refused before the verdict (`Delivery.purseApart`). That is a new refusal, which is right,
  though `payerInvalid` is a loose name for "the collector is the purse".
- `DepositIndependentStatement` quantifies over both verdicts and every other yield field, so it is the
  general form.
- `BirthCommitJudgedStatement` covers births.
- `DeliverLawRefusesStatement` follows `deliver`'s order and names `.objectWrite reason`.
- `commitYield_spec` keeps equality except for a refused transfer, as asked.

One remaining weakness: `CommitLawRefusedPole` exhibits only the `judgeWritten` refusal. No witness
satisfies `DeliverLawRefusesStatement`'s twelve premises jointly. Add one through a concrete delivery
when the fixtures allow; until then, that statement's premises are not shown inhabited.

**Addendum, un-stream-continuity-wip e0916a53 (not yet elaborated): the pass-10 gaps are closed.**
`decide` = `decideWith held.authentic`, where `authentic` is `Head.verify` at the held height, chain
and frontier. `hotRegistration_iff` names `Head.verify … = .ok head` for whichever tag is the
candidate, so copying the tip's tag is refused (`teeth_copiedTagUnverified`, `openingUnverified`).
`withOpenedFreshTip` builds `Held` from the session's own `durable` (height, `headTag`, chain,
frontier; `ApplicationStreamContinuity.lean:236-237`), not from the physical read, and runs the
handoff exactly when `gate (decide …) = none` (`handoff_runs_iff`).

`appended_headTag` pins `Appended.next.headTag = some entry.tag`. The stale, forked and below-birth teeth
quantify over every verifier `v` through `decideWith`, which is stronger than a closed instance, not
weaker. Proofs may start once the file elaborates green.

**Addendum, un-pred-census 0d7156f19 (reasoned, not built).** The shape requested in the eighth pass is
in place:
- `Ran` is the live `Answered`, minted once, after `verify`/`verifySshsig` returned `.ok`.
- `live_voucher_has_ran` is the IO-level tooth over the type.
- `admitted_live_ran` (`Kernel/Receiving.lean:512`) is the top-level theorem at
  `receiverVerifier (.live config)`, and it covers both verified and observed.
- `receiverVerifier` is restricted to the receiving modules, and `ofAnswered` is honest in its docstring.

Two gaps remain:
1. **`Ran` has no fields, so `by constructor` or `⟨⟩` in any other file mints one without writing
   `Ran.mk`.** The module's own comment says it: private `mk` "stops names but not `by constructor`".
   `check-receiver-verifier.sh` counts the text `Ran\.mk`, so it misses that. The guarantee therefore
   rests entirely on `TokenCensus` checking, at the term level, which compiled constants reference
   `Ran.mk`. Confirm the restricted row is checked over the environment (not by grep), and add a plant
   (`⟨⟩ : Ran c q a` in another module) that the gate must catch.
2. **`.recorded`:** `receiverVerifier (.recorded t)` vouches for whatever a constructible transcript
   says. That is fine for fixtures, but the Host's receivers must be shown to run at `.live`. Add a census
   row or check that `.recorded` is named only in fixture or assurance modules.

**Addendum, un-pred-census f013827d6.** Gap 2 is closed: `.recorded` is refused outside fixtures,
assurance and tests, and is never allowed in `Host/`, with a plant. Gap 1 is narrowed but **not closed**.
The gate refuses files that *name* `Ran`, but a forged proof need not name it. Each of these elaborates to
`Ran.mk` by unfolding:
- `theorem x : oracleAnswered (.live c) q a := ⟨⟩`
- `(receiverVerifier (.live c)).Answered q a := ⟨⟩`
- `Vouchers.ofAnswered … (fun _ _ => ⟨⟩)` at the live verifier

`oracleAnswered` and `Vouchers.ofAnswered` are not restricted. The only spelling-independent guard is
term-level. Every forged proof's value contains the constant `Ran.mk`, so add one environment scan,
theorems included, that admits `Ran.mk` only inside `receiverVerifier`. This is a small Lean check over
`env.constants` for one constant, not the whole census. Add a plant for the `oracleAnswered` spelling.

## 2026-10-27, fifteenth pass: clock law controller clause (lane/lean-critical bc88a5ab, not built)

**The clause must require the clock unchanged.** `clockPredicate`'s `.monotone` conjuncts forbid only
regress. Under `controlClause`, a step whose subject is the controller with a management verb may move
`clock/now` and `clock/slot` *forward* by any amount. A forward jump is not harmless. Every `validUntil`
(`CredentialSignedEnvelopeController.lean:293`), every deadline and every expiry reads that clock, so a
jump expires all of them at once, and that is controller authority the ruling did not grant ("manage,
never tick").

Relying on the clock cell's writers never projecting a management request onto a clock write is a
premise outside the law (law 1). It holds for today's writers, but no theorem pins it, and any future
family or a generic receiver path breaks it silently. Legitimate management (install, revoke, delegate)
changes the cell's policy and grants, not its `now`/`slot`, so requiring them unchanged costs nothing.

**Change:** `controlClause controller := .all [subject = controller, verb ∈ controlVerbTags,
.eq "clock/now/delta" 0, .eq "clock/slot/delta" 0]` (or whatever the clock's projected delta slots are
named). Add the teeth pole `pole_controller_advance_refused`: a controller management step that moves
`now` forward is refused.

The remaining statements read correctly:
- `clock_refuses_nonticker_tick` now covers the controller, because no management tag is tick tag 11.
- `clock_control_present` and `clock_control_cannot_tick` mirror the pay pair.
- `platform_seeded` (`NativeHostGenesis.lean:893`) answers the twelfth pass's owed genesis clause: the
  platform cell is in `baseCells`, and its store is `Reachable` under the controller. The loader bridge
  (`load d snap = some L → Reachable …`) for snapshots after genesis is still to be composed from it and
  `platform_written_only_by_install`.

**Addendum, lean-critical 2b521b2b (not built): accepted.** Management is now a separate top-level
disjunct that requires `clock/now` and `clock/slot` *absent*. `controlClause_clock_false` proves it is
false on every step that carries the clock, and every clock write projects the clock. So the controller
can never move the clock, by the law's own text, with no premise about the writers. This also fixes the
second bug L1 found: in bc88a5ab an install was refused because `.monotone` fails closed on its slotless
step. The one remaining premise (management steps project no `clock/*`) fails safe. Breaking it narrows
management and never widens it. That direction needs no theorem, only a note on the clause.
`pole_controller_advance_refused` is the requested teeth.

## 2026-10-27, sixteenth pass: plan against submit, L1c (lane/lean-audit-c 23bae6bbc, not built)

**Verdict: the statement owed in pass 4 (c) is now stated, on the deployed path. Two things are needed
before calling it done.**

`Pending.judgeBranch` is `admitBranch`'s own tail. It names binding, unsupported, range and cast refusals
before `law.admit`, so `policyRejected` now means the law's verdict and nothing else. `planVerdict` makes
the same three compiler checks plus `eval`, on `config.step = branchStep` (by `rfl`). The three keystones
have the right shape and scope (one `Pending`, one snapshot and height):
- `PlanRefusalSound` (a plan refusal makes `BranchAccepted` empty);
- `PlanPassNotLawRefused`;
- `LawRefusalDisclosed`, the converse asked for in pass 4.

`factoryVerdict_congr` is the honest claim across time. `birthRefusal` now refuses where it used to pass
silently. `planVerdict` leaves out binding, which is correct: binding depends on the evidence, and
`PlanPassNotLawRefused` allows it as a separate cause.

1. **No poles for the three keystones.** `PlanRefusalSound` is vacuous if no `Pending` has
   `factoryVerdict = some false`. Both pass-throughs are vacuous if `BranchAccepted … .factory` is never
   inhabited. Reuse the concrete descriptor of `:816` ("Both poles on one concrete descriptor"): a
   satisfiable `Pending` with verdict `some true` and an accepted factory branch, and a teeth `Pending`
   whose law evaluates false, with verdict `some false` and admission `.error .policyRejected`.
2. **Disclosure of preparation errors.** `birthRefusal` now returns `s!"birth preparation: {repr reason}"`
   and `"birth admission: {repr reason}"` on the observation channel. The law's refusal goes through
   `publicRefusal (grantFields …)`, but these strings are unfiltered. Check that no `ResourceBirthController`
   or `ResourceBirthPolicyController` `Reject` carries state the requester's grant does not name
   (balances, other cells' roots, revision numbers). Otherwise map them to names without payloads.

The known gap stays open and should be listed in the lane's state file:
`GrainResourceBirthAdmission.Pending.admitBranch` still lets `law.admit`'s `none` cover binding.

**Addendum, lean-audit-c 64903e599.**
- *Disclosure: accepted.* `preparePending`'s refusals carry no payloads. The one payload in
  `PreparationReject` (`room`) is the requester's own room, with a reason the gate already filters by
  grant. The string was already printed on the same authorized channel.
- *Poles: the probe is accepted as an interim witness, not a replacement.* `scripts/kn2/neutral-birth.lean`
  exercises both poles on the real receiver path: a passing plan that commits, and a refused plan that
  admission refuses `policyRejected`. That shows the keystones fire on deployed inputs. ATLAS law 2
  still wants the witnesses at declaration level, though, gated beside the axiom pin. The concrete
  `Pending` in Lean stays owed, and the keystones are not "done" until it exists. List it in the state
  file next to the Grain gap.

## 2026-10-27, seventeenth pass: births priced from the platform cell (lean-audit-c d68a9afe4, statement only)

**Accepted: the ordinary birth is the first scope.** Two conditions apply.

`ReceiverReadsCurrent` is about the deployed object:
- `receiveLoaded`'s accepted birth;
- `platformAt` read on the very durable image it commits against;
- tariff and `{ownerBudget, lifetime}` equal to the record's;
- the platform cell in the read guards, so a concurrent install makes the birth stale;
- `platformUnavailable` by name when the cell is absent.

It instantiates `BirthsReadCurrent`/`BirthQuoteCurrent` through `deployedView`, and its teeth (a reader
of `opened.pins` after a tariff-changing install) are the right refutation. Carrying the template beside
the profile is forced by the profile hashing `profile.template` into the semantics. Changing
`AcceptedBirth.indexed`'s text for it is justified.

1. **State the scope in the claim.** The label must say "ordinary births". The owed families
   (grain-birth tariff, application grain, share issue, agent lifetime, provisioning, pay enrol, and
   completion's custodian key) are listed with file:line in the state file, not implied by the keystone's
   name.
2. **No silent twin at the re-genesis.** `profile.template` stays in the semantics, so every owed site
   that still reads `profile.template.ownerBudget/lifetime` or `config.tariff` would serve the
   *genesis* value after an install, without error. That is the twin that law 13 says to delete. Before
   the one digest change ships, each owed site must either read the cell or be shown to read only
   `issuer`/`birthSlack`. Gate this with a census row that refuses any reader of those fields outside the
   cell path. Otherwise the re-genesis that is meant to be the last one leaves stale pricing in families
   nobody re-checked.

**Addendum, lean-audit-c f2010f574 (unbuilt): the first half is accepted.**
- `pricedAt` refuses an absent cell (`platformUnavailable`) and a tariff that disagrees with the record
  (`platformStale`) on the committed image, before admission. While `opened.pins` is not yet read from
  the cell, a birth after an install is therefore refused loudly instead of being priced stale. That is
  the right interim behaviour.
- `readGuards_platform` carries the premise "the birth does not write the cell". Discharge it from
  `platform_written_only_by_install` (the birth family is not `.platformInstall`), so the guard holds
  unconditionally.
- Condition 2 is met: the field-reader census refuses new readers and holds `--ship` while any owed row
  remains (73).
- The keystone, the cell-read `opened.pins`, `templateAt` in `preparePending` and the audit (c) Lean
  poles remain owed. The label "ordinary births" is correct.

## 2026-10-27, eighteenth pass: item 3, the deployed keystone `ReceiverReadsCurrent` (lean-audit-c e421c0830, statement only)

**Verdict: accepted as stated. One change to the spec module, one interim condition.**

**(1) Pricing into `Pending`, deleting `pricedAt`: correct.** Over `AcceptedBirth` the keystone needs no
assumption, and the IO check would be a twin of the admission check (law 13). The IO receiver commits
`DurableReceiverIO.receiveLoaded … (intent accepted)` directly (`ResourceBirthReceiver.lean:602`), so
"the theorem covers every value the receiver commits" is true by the code's definition and needs no
lemma.

**(2) The vacuity argument: correct.** It also says something about `PlatformCell` itself.
`BirthsReadCurrent view terms guards` over a store-only `terms` is satisfied by `currentReader` by `rfl`,
so as a keystone it constrains nothing deployed. Its job now belongs to `ReceiverReadsCurrent`. **Change:**
in `PlatformCell.lean`, either delete `BirthsReadCurrent`/`BirthQuoteCurrent` and their poles, pointing to
`ReceiverReadsCurrent`, or relabel them as the store-level shape, explicitly *not* a keystone. A
vacuous-by-construction keystone left standing beside the real one is the shape law 2 forbids.

**The statement.** Each conjunct is about the deployed object:
- the record on the image the birth commits against;
- `priced` and `FeeBound` at `record.creation`;
- `template` built from `record.ownerBudget/lifetime`, reaching the grant through `RootGrantShape`/`BirthWindow`;
- the platform cell's *exact root* in `(intent accepted).readGuards`.

Teeth are real and general: `unpriced_empty` for absence, `preparePending_stale` for a genesis-tariff
reader after an install, and the pre-f2010f574 guard list failing the last conjunct. The premise
`platformRecordAt = some` is inhabited on the deployed genesis by `platform_seeded`. The label states
its scope and the 87 owed rows. Item 6's discharge from the birth's own write list is sound:
- allocations are at ids `allocate` requires absent, while the platform cell is present;
- the factory, book and authority cells differ from it by observed kind.

**Interim condition, the same as pass 16.** The satisfiable pole needs a concrete loaded, signed
`AcceptedBirth`. That is the same owed Lean object as item 7, and one witness serves both.
`neutral-birth.lean` is accepted as the executed interim witness only. The keystone is not "done" until
the declaration-level witness exists.

## 2026-10-27, nineteenth pass: effects revival statements (lane/effects-revival d084ef449, not elaborated)

**Verdict: proofs may start on the engine, completeness and `ContentComplete`. Two statement changes
before the live keystone is claimed as "the derived path".**

**Engine keystone: honest, and near-definitional, as claimed.** `agreement` and `unregistered` hold of
`dispatch` by its definition plus `Sound`'s `select ∘ pack = id`, and `frame` follows from `exec`'s
`InFrame` check plus `Framed`. The content is the discrimination. The four teeth (ghost, fail-open,
unframed, twin) each bite a distinct clause, and `frame`'s existential (decoded `op`, selected `s`/`s'`)
also stops a dispatcher from admitting undecodable bytes. **One hole:** `agreement` constrains `d` only
on `pack s`, and `Sound` gives `select (pack s) = some s` but not the converse. On a cell where
`select cell = some s` but `cell ≠ pack s` (content outside the selected state), a dispatcher may rewrite
that outside content. `frame` checks only the selected locations. Add `select cell = some s → pack s =
cell` to `Handler.Sound` (selection is exact on its role), or extend `frame` to `cell'` agreeing with
`cell` outside the selection.

**Completeness keystone: sound.** Its inputs are `encode op` and `pack s`, so `malformed`, `wrongRole` and
`unregistered` cannot occur, and `Complete` removes `outOfFrame` and `guardFailed`. Entry B's
non-lawfulness is the right teeth.

**Live keystone.**
- *Real content:* `ContentComplete`, the frame law over `ContentResource.run` with the blinding seal
  replaying; and clause 4 (`targetPatch = descriptor ++ seal`, which `contentGhost` refutes).
- *Near-identity:* clauses 2 and 5, because `contentSem` reuses `ContentResource.run`, which
  `computeTarget` also calls.
- The label must say so: the dispatcher, frame and checks are derived, while the content semantics is
  still the source-owned lowering, not a derived effect.

**`HostDispatches` must be stated now, not at migration.** Statement-first (ATLAS law 2) applies to the
deployed keystone above all. As stated, `ContentAgreement` certifies that the hand arm *agrees* with
the declaration. That licenses keeping both, which is the twin law 13 forbids. `Dispatches` already
has the migration window built in. State
`HostDispatches : Dispatches [(1, contentHandler)] legacyCodes hostTargetDispatch` over today's target
dispatch, with every other payload code in `legacy`. That is a `Prop` even if its proof waits for the
decoder rewiring. `noTwin` then forces code 1 out of the hand arms at the moment the theorem closes.
`ContentAccepted`'s inhabitant (the native doc-write fixture) is owed, as noted.

**Addendum, effects-revival 3dac92b91 (not elaborated): both changes are accepted.** Going further than
asked was right. `agreement` over every cell through `Handler.fire` (header, then select, then exec)
removes the packed-cell restriction entirely. `HostKeystone` is stated over today's `hostTargetDispatch`
with `hostLegacy`, and it is labelled as known false by clause: unknown tags give `malformed`, and code 1
is still the hand arm. Those are exactly the two things the migration commit must change, so the
keystone is honest as a gate. Two notes for the proofs:
- `HostPremise`'s new `pack (select cell) = cell` holds for `⟨.content, value⟩` only if
  `CellState.materialize contentMaterializer value.logical = value`, that is, `Materialized` is
  canonical. Prove that lemma first; if it fails, the premise is false.
- `HostTeeth`'s ghost clause needs an admitted command whose seal is non-empty, because otherwise both
  dispatchers refuse alike. Its proof therefore rests on `HostAccepted`'s owed fixture, the same object.

## 2026-10-27, twentieth pass: completion custodian key from the platform cell (L1d, design, before code)

**Verdict: the design is accepted, with one requirement on the light route.**

The keystone is about the deployed object:
- `keyCurrent` over each admission's private-mk `Candidate` reads the record from `ground.view`, the state
  the completion's guards are taken on.
- The physical report's verifying key is `custodian.key` by the type of `physical`.
- The platform cell's exact root is in `Core.intent`'s read guards, so a key-rotating install between
  prepare and commit makes the completion stale.

`Read.stale` is general teeth: no `Read` carries a key other than the record's, which refutes the
`config.completionCustodianKey` reader after a rotation. `select_unavailable` names absence. One shared
module, with `platformRecordAt := recordOn … durable.snapshot` by `rfl`, avoids a four-way copy.
Historical re-admission reading the record in force at that height is what replay agreement needs.

- **(a) `platformReadOnly` as a checked refusal: accepted.** It fails safe, refusing by name rather than
  admitting, the same shape as `packageGuardReadOnly`. The theorem form can come second. The owed
  concrete accepted `Candidate` must also show the check passes on an honest completion, so it is not a
  liveness trap.
- **(b) Pre-platform worlds refuse every completion with `platformUnavailable`: accepted.** It is
  consistent with births and with the one re-genesis.
- **(c) Host pre-checks reading the opened image: accepted**, as diagnostics only, since admission
  re-reads.
- **Requirement, the light route.** A served ground's `canonicalBytes` covers the ids its basis
  *served*. Light plans request keyed bases (`light.basis keys`, as `prepareInstallLight` does). Unless
  the completion's basis keys include `cellIdOf deployment`, the platform cell reads as `absentBytes`,
  `load` is `none`, and every light-route completion refuses `platformUnavailable`. State, and prove, that
  each completion family's light key set contains the platform cell id.

**Correction to the twentieth pass: the light-route requirement is withdrawn.** It rested on a wrong
premise. Basis keys name only transactions and nullifiers (`DurableView.Keys`,
`Kernel/DurableView.lean:143`). A basis's cell bytes are the served state's whole
`canonicalBytes`, whatever the keys (`Basis.view_canonicalBytes … := rfl`, `Compiler/ServedBasis.lean:126`).
`Served`'s private constructors (`ofLoaded`, `ofStateAt`, `advance`) all carry full cell state. So a
seeded platform cell is present on every light ground. L1d's replacement is the right declaration:
`recordOn` agrees across any two key sets over the same `served`, by `rfl`.

## 2026-10-27, twenty-first pass: M2 proof phase, `Intent.credit` and the refill family (L1d, design)

**Verdict: the shape is accepted, with one finding that must change before code.**

The extension is right:
- one `credit` field, threaded protocol → data intent → record;
- `install := available - exactCharge + credit`, with no truncation, because `preflight` funds
  `exactCharge` first;
- `sameCheck` comparing credit;
- the codec carrying it as a field (v3, riding the re-genesis), not derived from event bytes, so
  "the label grants nothing" rests on a field.

K1 instantiates M2-d on the real `Snapshot.install`. K2 instantiates M2-c on the deployed receiver.
K3 instantiates M2-b over what replay can produce. The teeth (replay, overflow, forgery, tagged mint)
are the accepted ones.

**Finding: the overflow check must happen at commit, not plan.** `fitsCheck (raised remaining amount)` is
computed against `remaining` at plan time. A second refill, or any later-charged record, can land between
plan and commit, and no guard covers the meter: it is `Snapshot.available`, not a cell. So the committed
`available - 0 + amount` can exceed `WordLayout`. That is the machine-width boundary `Theory.ResourceCost`
checks at persistence, so a Store would accept a record it cannot encode. Put the fit into the
protocol: `preflight` refuses when `available - exactCharge + credit` does not fit the layout (a named
`creditOverflow`). Restate `overflow_refused` against the commit-time `available`. With credit 0 for
every other family, this costs them nothing.

- **(a) Authority-cell guard: right**, since it is the revocation race. Take the controller from the same
  source as the install family: `controllerOf` of the platform cell, proved equal to genesis's by
  `controller_stays`. Reading `config.factoryController` here would be a second source of controller
  identity. With `controller_stays`, the platform cell needs no guard for this read.
- **(b) Bounded only by fit: accepted.** The meter is the operator's resource, and the issuance cap stays
  out of the lane, as recorded.
- **(c) Quantify over the `NativeAdmission` arms: right**, because replay is the meter's source of truth.
  It is sufficient only if replay compares each record's `credit` with its arm's re-admitted intent.
  State that link: a record whose credit differs from its arm's intent is refused (the `sameCheck` credit
  clause). Then an IO receiver cannot commit a credit the arm would not reproduce.

**Correction to the twenty-first pass: the overflow finding is withdrawn, and option (A) is chosen.** I
checked on main. `ResourceCost.WordLayout` is referenced nowhere in `Kernel/`, `Compiler/` or `Host/`
except `PlatformCell.RefillContext.layout`. The meter persists only through
`DurableReceiverCodec.chargeStream` (ten unbounded `StreamCodec.nat`). So the deployed meter is an
unbounded `Nat` end to end, and no record becomes unencodable. A fit check would guard nothing (and
this pass's own pass-2 overflow pole asked for one on that same false premise). Drop
`RefillContext.layout`, the `fitsCheck` conjunct and `overflow_refused`. The remaining M2 statements
stand. Record in `PlatformCell.lean`'s header that the meter is unbounded by design: any future
fixed-width emitter of `available` must carry its own bound at that emitter (law 3).

**Addendum, M2's deployed statements (L1d, local, unbuilt): the deployed forms are accepted. Retire the
spec-level twin.**
- K1, `protocol_install_matches` over the real `Snapshot.install`, with teeth against the uncredited install:
  accepted.
- K2, `AcceptedRefill.sound`, states the deployed facts: sponsor = `controllerOf` of the platform cell, the
  verified envelope, the stored capability evidence, the unspent marker, and the exact intent shape
  (no writes, zero charge, one marker nullifier, `credit = amount`, guards at the durable root). Together
  with `intent_install_refilled` it is a stronger, more concrete M2-c than `RefillLawful ctx post`. The
  deployed receiver is not a pure function of a meter and a refill, so a `post` would be invented for the
  instantiation.
- K3, the `credit_confined` disjunct naming an `AcceptedRefill` (private mk, built only by admission) with
  `recordMatches_iff` carrying credit, is the deployed content of `CreditConfined` and needs no
  `RefillAdmits ctx` wrapper.

So the abstract `RefillContext`/`RefillAdmits`/`RefillLawful`/`CreditConfined` in `PlatformCell.lean`
would now be parallel statements no live code instantiates (law 5). **Delete them, or relabel them as the
shape and not keystones, pointing to K2/K3**, exactly as pass 18 did for `BirthsReadCurrent`. Then **move
the teeth onto the deployed type**: `IsEmpty (AcceptedRefill …)` when the marker is spent (replay) and
when the sponsor is not the platform cell's controller (forgery). K3's own statement already refutes a
non-refill arm carrying credit.

## 2026-10-28, twenty-second pass: thin-consent birth (lane/thin-birth 7410dd6d9, statement text)

**Verdict: REVISE, two statements. The rest is accepted.**

1. **`EffectsBinds` as a premise: change it to the compared-pair collision disjunct.** As a hypothesis,
   `effectsDigest signed = effectsDigest d → signed = d` is supplied by the caller, and its inhabitation
   pole `∀ d, EffectsBinds d d` is the trivial case (the conclusion is `d = d`). The case the teeth
   need is the other one: in `SwapAfterConsentRefused` the premises `signed ≠ d'` and
   `EffectsBinds signed d'` together just say "their digests differ", and nothing inhabits that. Use
   the pattern already accepted for `PinCollision`/`ArgumentCollision`: drop the premise, and conclude
   `… ∨ EffectsCollision signed d`, with `EffectsCollision := signed ≠ d ∧ effectsDigest signed =
   effectsDigest d`. Both theorems then stand unconditionally, and the collision is a named event on
   exactly the two descriptors compared. Stating it over descriptors rather than bytes is fine, because
   `sourceEncoding` is canonical (the plan check already pins `encode finalized = finalBytes`).
2. **`HonestPlanAccepted`'s pins premises: require the lemma.** `opened.pins.federation =
   config.federation` and `opened.pins.policyId = ⟨factoryId⟩` are premises no theorem inhabits. That
   makes the satisfiable pole conditional on unproved facts, which is the shape the satisfiable field
   exists to rule out. `validateLoaded` builds `Opened` from `parts.pins` after `validateChecks`. Prove
   `Opened.pins_federation`/`pins_policyId` from that construction (or the checked parts' exactness), and
   drop the premises.

Accepted:
- **(2) Conjuncts 3 to 7** are true of every `PreparedBirth`, and they gain their force from conjunct 2
  (`encode (userPart d) = shown.draft`) and conjunct 4 (auxiliary creates are the kernel's). That is the
  `delegate_display_is_commit` pattern, and it is fine as stated. A one-line corollary with `userPart d`
  rewritten to `decode shown.draft` would make "commit = f(shown, kernel-owned, pre)" literal; it is
  optional.
- **(3) `author` as a Host-instantiated parameter**, with Host-side completeness witnessed by the journey
  row: accepted, provided the label says the re-authoring fixed point is a row, not a theorem.
  Soundness of display-is-commit does not depend on `author` being correct.
- **(5) Coordinates shown, not judged**, gated at admission (`RootGrantShape`, `BirthWindow`, policy epoch 0,
  `BornLineage`), with the window shift named in the display: accepted.
- `SwappedPlanRefused`'s two refusals are general and named.

**Addendum, thin-birth 909de2bca: ACCEPT.** `EffectsCollision` is a compared-pair event on exactly the
two descriptors, and it cannot be proved without an actual cSHAKE collision. Neither theorem now takes a
hash premise, so the disjunct is no escape hatch. In `DisplayIsCommit` the consented-header premises force
equal digests, so either `signed = d` (the conjuncts) or the collision holds. `OpenedPinsPublicStatement`
replaces the uninhabited premises with a statement about every `Opened`. Carrying the invariant as a field
built at `Opened`'s three construction sites is the right realisation. The re-authoring fixed point is
labelled as jpriv2 row 19.

## 2026-10-28, twenty-third pass: the World carries M2's credit (L1e, design, before proofs)

**Ruling: option (A).** Option (B) (`intent.credit = 0` on the four `SnapRepresents` theorems) would cut
whole-World equality on every log containing a refill, which passes 6 to 9 rest on. It is a weakening.
Under (A):
- `World.Turn.credit : Charge := 0`;
- `meterPatch` writes `avail - charge + credit` on lanes where either term is nonzero, which is exact,
  since `fundedCheck charge` is unchanged;
- `turnOf` sets `credit := intent.credit`.

The four refinement theorems keep their statements, plus a `credited` sibling of `charged`. This
section corrects pass 21, which missed the World side. Conditions for the stated text:
1. **Regression pole:** `meterPatch lanes charge 0 avail = debits lanes charge avail` (or the same as an
   equality of `World.step` on credit-0 turns), so every pre-M2 turn provably steps as before.
2. **Satisfiable pole:** a credited turn's post-meter on a lane is `avail - charge + credit`, with
   `credit > 0` raising it.
3. **Say where confinement lives.** The World admits `credit` as turn data without deciding it, as it does
   subject and capability. Its docstring must say minting is confined only by K3 (`credit_confined` over
   the replay arms), so no one reads the World law as a meter-safety statement. I found no World-level
   theorem on main claiming the meter never increases. Any future one must carry the credit term.

**Addendum, L1e's exact text for (A): ACCEPT.** All three conditions are met:
- the credit-0 regression poles (`meteredLanes_uncredited`, `meterPatch_uncredited`, `sysPatch_uncredited`);
- the satisfiable pole `step_meter` on every lane, with the concrete refill turn taking 0 to 5, which is
  item 7's World-level half;
- the docstring placing confinement in K3.

`sysPost_allowance`'s case split agrees with `step_meter`, because an untouched lane has
`charge = credit = 0`. `turnCheck`'s unchanged `fundedCheck` keeps the subtraction exact. `turnOf_credit`
and `ofIntent_credit` give the `credited` sibling. The four `SnapRepresents` statements are unchanged.

On the World-level tooth: `decodeTurn_encodeTurn`, with `decodeTurn` reading the credit, already makes
`encodeTurn` injective in it. Add the one-line corollary `encodeTurn_credit_ne`, turns differing only in
credit having different bytes, as the stated tooth. Then a future codec that drops the field fails a
named theorem instead of passing silently through a roundtrip on a defaulted value.

**Addendum, `SnapRepresents.meter` strengthened (L1e): ACCEPT.** A credited lane at an exhausted meter may
hold `none`, so the World's guarded allowance write would refuse the very refill the 0→5 pole admits. The
`getD 0` field cannot distinguish `none` from `some 0`. Strengthening the field in place to
`w.allowanceOf l = some (snap.model.available l)`, with `meter_eq` as the old field for current readers,
is the right fix. It is a stronger premise every producer inhabits, not a new hypothesis, and deployed
genesis records every lane (`TurnLog.genesisSystem`), which writes preserve. `representsCheck_sound`
moving to the `some` comparison keeps the open deciding it. Restating `charge_le_allowance`'s second
conjunct as `step_meter` is required by the credit and accepted.

## 2026-10-28, twenty-fourth pass: how item 7's witnesses may be evaluated (L1e)

**Ruling: option 3, amended. The signature needs no native evaluation.** `CheckedSignature.source` already
admits a recorded run of the native verifier "only in a pure evaluation" (`CredentialSignatureIO.Oracle`
`.recorded`, `CredentialSignatureAdmission.lean:287-296`), and `scripts/check-native-transcripts.sh`
re-submits every recorded verdict to the native process. Build the signed poles (`AcceptedBirth`, the
completion `Candidate`) over a recorded transcript holding the fixture signer's verdict. The verdict is
then data, and the trust boundary is the one passes 3 and 8 accepted: statements relative to the
transcript, which the native check re-verifies. Ed25519 never enters the kernel.

The remaining cost is cSHAKE over the image's roots. Measure one root under `decide +kernel` on a box
first.
- If it is feasible, every pole is kernel-evaluated over a minimal hand-written coherent image. A witness
  need not be the deployed genesis, only a real coherent snapshot through the real
  `preparePending`/admission.
- If it is not, a separate witness module evaluated by `native_decide` is acceptable as the fallback. Its
  axiom pin names `Lean.ofReduceBool` explicitly; no keystone module imports it; it is graded and
  confessed per law 9.

Either form meets law 2 only if the module is built by the merge gate with its pin checked, so a broken
witness turns the gate red. An executed script does not count. `neutral-birth.lean` stays as the
end-to-end run.

## 2026-10-28, twenty-fifth pass: JDISCLOSE scalar oracle and installed-law explanation (lane/red-jdisclose-scalar, statements)

**Verdict: REVISE A, accept B with one transfer lemma.**

**A. Revise.**
1. **The `none` branch keeps the oracle open.** `scalarScopeCheck` returns `true` when the authority cell
   holds no such capability, so `prepareCell`'s guards still run before admission refuses
   `capabilityRejected`, and `guardRejected` versus the later refusal is an equality oracle for a
   requester with *no* grant at all. "Observation-phase authority precedes prepare" is a claim about the
   plan channel, and no statement here proves it. Close it fail-safe: `none => .error .capabilityRejected`,
   refused before any guard. That is the same name admission would give, only earlier. Then
   `computeTarget_scalar_unnamed_refused` has a sibling for the `none` case, equally quantified over every
   `pre`.
2. **The teeth cover guards only. State the non-interference.**
   `computeTarget_scalar_unnamed_refused` shows that a guard on an unnamed field refuses independently of
   values. But if `prepareCell` reads any other field (a cross-field invariant, a balance check, an
   existence test outside `guardKeys`), a fully named action can still refuse differently on unnamed
   values. The property the row needs: when `scalarScopeCheck = true`, the *error* `computeTarget …
   pre` returns is a function of the named fields alone, that is, `pre` and `pre'` agreeing on
   `NamedBy stored…fields` give the same refusal. `computeTarget_scalar_named_as_before` is the accepting
   pole, not a confinement statement.

**B. Accepted.** Dropping the neutral guard in `explained` is display-only (the decision is unchanged).
`owner_told_value_installed` is the satisfiable witness. `narrowed_hides_uncovered_installed` (4242 and 5
both give `none`) is the right teeth, but it is a closed instance (law 9 permits it as a witness). Add
`narrowed_installed_le : narrowed fs (Pred.all [(neutralComponent law).guarded]) old new = some r →
narrowed fs law old new = some r` (the installed law tells nothing the raw law does not). The existing
general non-leak results for raw laws then carry over to every installed law, and the known coverage limit
(installed hides more) is consistent with it.

**Addendum, JDISCLOSE owner's reply: A lands, A2 is owed, the B lemma is withdrawn.**
- *A1 taken:* an unheld capability is refused `capabilityRejected` before any guard, with
  `computeTarget_scalar_unheld_refused` over every `pre`. Accepted.
- *A2:* my confinement as stated is false by design. `staleTarget` compares the requester's
  `expectedTargetRoot` with the whole-cell root, which is the one bit `RefusalReason`'s header already
  concedes. The owner's alternative ("equal roots and agreement on named fields give the same refusal")
  would be near-vacuous, because equal roots pin the whole cell up to a collision. The non-vacuous form
  to record as owed: `computeTarget … pre = .error e → e = .staleTarget ∨ e = f (namedPart pre)
  declaration command` for one `f` fixed across `pre`. That covers the remaining checks (`preLaw`,
  `admissionCheck`, `FieldClosure`, `postLaw`). Not blocking: A closes the measured oracle, and A2 is owed,
  not claimed.
- *B:* `narrowed_installed_le` is false (the installed leaf path differs) and unnecessary, because
  `narrowed_congr` already quantifies over every law, installed ones included. Withdrawn.

## 2026-10-28, twenty-sixth pass: thin consent over salted openings (lane/thin-birth, invocation arm, statements)

**Verdict: ACCEPT, with one strengthening of the keystone.** The replacement removes the defect JP2 row 22
measured: re-encoding a blinded cell can never reproduce its signed root, because salts derive from a key
the Host never serves. It also removes `RootBinds`, the caller-supplied carrier of the kind refused in
pass 22, in favour of a named collision. No twin is kept.

- **(a) The sealed exclusion: strengthen it, do not just exclude.** As stated, the keystone says nothing at
  `SealedIn` addresses, so a Host that seals more leaves those commits unconstrained by the claim. The
  owner's own argument (patch ops carry explicit before values, so a member patch cannot write an address
  it was not shown) proves something stronger, and that is what should be stated: for an address that is
  `SealedIn` and not `KernelOwned`, `prepared.post address = prepared.pre.logical address`. What the member
  did not see is left exactly as it was. Then "a Host can narrow what is shown but cannot change what
  commits" is a theorem, not prose.
- **(b) The collision disjunct is shaped correctly.** It is a compared-pair event at both layers of the
  commitment, at the actual pre-state, not an arbitrary one: equal list roots over different leaves
  (length differences included), or equal leaves over different openings at one position. Neither layer
  can be inhabited without a hash collision.
- **(c) The satisfiable pole at declared-object scope is accepted as the first scope.** The label must say
  "declared-object scalar targets", and since `checkServed` is deleted for every kind, the other kinds'
  acceptance must be listed as owed (a pole or a journey row each). They go through the same
  `resourceView`, but that is a reading, not yet a witness.

## 2026-10-28, twenty-seventh pass: effects revival after the architecture review (dde029eb4, statements)

**Verdict: accept 2. Revise 1 and 3.**

**1. `OneSource` is extensional and adds nothing to `Dispatches.agreement`. Revise.** Any `d` that agrees with
`dispatch R` on registered codes satisfies it, by taking `legacy := d` (since `composeDispatch R d = d` on
exactly those `d`). So it cannot show the hand arm was deleted, which is the review's point. What would
show it is structural, and it can be stated now as a Prop: the legacy dispatcher's input type has no
constructor for a registered code, `∀ p : LegacyPayload, tagOf p ∉ R.map Prod.fst`. When `content` moves,
the type `Payload` loses that constructor, and the theorem fails to typecheck if it does not. State that
census as the Prop now, and keep `OneSource` only as the extensional shadow, or drop it.

**2. Registry extension: accepted.** `ExtensionPreserves` covers acceptances and refusals, and
`SafeExtension`'s no-rebinding-of-retired-codes rule is the policy for new codes. The `octet` bound ties
codes to the tag byte, and the teeth are right. The owed items (prefix consumption by the outer decoder,
whole-epoch fingerprint) are listed.

**3. `PrepareBridge`: right object, but clause (b) has an escape disjunct. Revise to a factorization.**
Stating it against `ResourceTransaction.prepareTarget` itself answers the review. But (b) lets the routed
dispatch accept while `prepareTarget` refuses for a `ControllerGeneric` reason (`invalidPost`,
`policyUnavailable`, audience), and nothing pins those refusals as independent of the effect. Say what the
deployed path is: `prepareTarget … = routed >>= genericChecks …`, with `genericChecks` reading only the
post, the policy source and the audience, never the payload. Then (a), (b) and (c) are corollaries, and
"the generic refusals are not a place for the effect to disagree" is part of the statement. At the
migration commit, that factorization is the shape `prepareTarget` takes.

The two items listed for later (whole-epoch compatibility; two-level activity refusals) are acknowledged.

## 2026-10-28, twenty-eighth pass: prefix consumption, two-level activity refusals (effects-revival c7bed9760, statements)

- **1. Prefix consumption: ACCEPT.** `ConsumesPrefix` is a predicate on any reader, and its three clauses
  (exactly one encoding consumed with the suffix untouched, unregistered octets refused, acceptance
  canonical) are the right ones. The keystone includes preservation under `Extends`. Each of the three
  teeth bites a distinct clause, and the rebinding tooth shows the code binding matters.
- **2. Live prefix: ACCEPT.** The agreement is with the deployed `payloadStream.decodePrefix` on code 1
  (the migration window), with acceptance of any command plus suffix. The code-3 tooth shows the binding
  is the deployed one.
- **3. Two-level refusals: revise, one clause.** `TwoLevels` constrains the refused-verdict case (`verdict`)
  and keeps turn errors as errors (`turn`). It says nothing where the reference *admits*, so a candidate
  that turns a settled transfer, or any accepted yield, into an `.error` satisfies it. That is the
  opposite collapse from the one the teeth refute. Add `ok : reference i = .ok c → candidate i = .ok c`.
  `verdict` stays as the named clause, the review's point, and is now also a consequence for the
  reference. Keeping the dropped declared write on the refused branch matches `commitYield`, and pass 11's
  restated write clause covers it.
- **4. Whole-epoch compatibility as a design without a Prop:** acknowledged. "Every registry change is a
  re-genesis until the seed carries the corpus" is the honest current statement.

`ContentFixture.lean`: when it checks, a single `native_decide` pinned by `#assert_compiled`, with kernel
lemmas from that Bool to the statements over an arbitrary witness, is the confessed, graded witness law 9
permits. The fixture is not cSHAKE-bound the way item 7's images are, so I will ask then whether a kernel
`decide` of that Bool is feasible.

## 2026-10-28, twenty-ninth pass: the four scavenge findings (main, as of this pass)

1. **`MultiCellHyperedge` joint apex: CONFIRMED, an identity carrier.**
   - *What happens:* `step` sets `jointApex := declaration.header.apex` regardless of the carrier and the
     turn (`Kernel/MultiCellHyperedge.lean:556`, and `:577` in `SemanticHyperedge`). `turnId` reads that
     field back. So `agree` is `rfl` (`:592`), and `turnId i (step c t)` does not depend on `turn.post` or
     on any cell's committed state.
   - *Witness:* the instance satisfies `agree` for any `Commit`, including one whose legs commit under
     different transactions. `Hyperedge.legs_agree`, and `HyperedgeKnowledge`'s distributed-knowledge
     reading of it, therefore say nothing about deployed joint turns.
   - *Corrected statement:* `turnId i` must read the apex from what the deployment records per leg. A
     cell's post-state holds no apex, but the durable journal does: the transaction that last wrote cell
     `i`'s root. Set `turnId i S := lastWriterTx S (cellId i)` over the committed snapshot. `agree`
     becomes "every leg's root was last written by the one intent whose `transactionId` is
     `header.turnId`", which follows from the joint commit installing all `rootWrites` in one `Intent`.
     It is non-trivial, and its teeth are two legs committed by two intents.
   - *Until it is restated:* label `legs_agree`'s instance at `MultiCellHyperedge` as definitional
     (no deployed content).

2. **`Pred.writeOnce` on 0: the predicate is honest. The authoring surface overstates.**
   - *The predicate:* its own docstring states the semantics ("absent-old or `old[slot] = 0` ⇒ any",
     `Pred/Core.lean:196`). The circuit's zero-indicator lowering forces 0 to be the unwritten sentinel,
     since a field element has no "absent". Witness: old `{x:0}`, new `{x:5}` evaluates `true`. Teeth:
     `eval_writeOnce_change` (`{x:3}` → `{x:5}` is `false`).
   - *The hazard:* it is at the author surface. `Compiler/ObjectiveBendLaw.lean:15/57` offers
     `writeOnce(FIELD)` to law authors with no mention of the sentinel, so a field whose legitimate value
     is 0 (a status, an owner id, a counter) is not write-once.
   - *Correction, down to the truth:* the author-facing spec reads "a *nonzero* value, once written,
     never changes; 0 is unwritten". Add a pole `eval_writeOnce_zero_rewritable` stating it. Either have
     `ObjectiveBendLaw` refuse `writeOnce` on a field whose declared domain includes 0, or document it in
     the grammar.

3. **`[LC-fs-adaptive] CLOSED`: CONFIRMED overstated.**
   - *What the theorem covers:* `lightClientGrinding_sound` (`Selvage/LightClientGrinding.lean:455`)
     bounds the probability, over coins `c : Fin qs.length → F`, that some chain among a family `chs`
     fixed in advance folds, with the query list `qs` (nodup, covering every chain's link prefixes) and
     the per-chain data `d` fixed *before* `c`. That covers an adversary adaptive in which chain it
     outputs after seeing the answers. It does not cover one whose *queries* are chosen adaptively: query
     `k+1` depending on answer `k` is a decision tree, not a fixed `qs`, and `Oracle.ofList qs c` cannot
     express it.
   - *Corrected label:* `[LC-fs-adaptive] PARTIAL: adaptive in the output chain; the query sequence is
     fixed before the oracle answers. Adaptive (tree) query strategies are owed.`
   - *Closing it properly:* the standard reduction answers queries by position. With fresh uniform answers
     per distinct query, a depth-`t` strategy's bad event is bounded by the same per-query union, so the
     statement over strategies `Strategy := (List F → LcQuery)` would carry the same bound. The manifest
     docstring at `Assurance/SelvageV0Manifest.lean:1238` currently says "issuing `t` oracle queries"
     without the qualifier, and must change with the label.

4. **`Pred.witnessed` lowers to constant false: CONFIRMED. A fail-open-under-negation trap, not a
   compiler lie.**
   - *Where it stands:* `eval` (first-party) fails closed on it and the circuit indicator is constant 0
     (`Compiler/PredCompile.lean:621`), so compiler and spec agree. But `supported` returns `true` for it
     (`:667`), and `PolicyRecordCodec` decodes it from installed policy records (`:73`, `:136`). The
     deployed path has no discharge oracle, so `.not (.witnessed vk)` compiles and is *always true*. A law
     author's "deny when credential X is presented" silently admits everything.
   - *Correction (law 10, loud refusal):* `supported profile (.witnessed _) = false`, with the theorem
     `supported p = true → p has no witnessed leaf`, and teeth: a policy containing `not (witnessed vk)` is
     refused `policyUnsupported` at install and at admission. Deleting the constructor (ZK D1) is the
     end state. Until then, refusing it is the minimum.

**Lanes:** (1) Kernel hyperedge owner; (2) the Pred/bend-law owner; (3) the Selvage owner, plus the
manifest; (4) the PredCompile owner. Routed via the root.

## 2026-10-28, thirtieth pass: commuting content appends (lane/qualify-doc-contention ed3f512f9, statements)

**Verdict: the effect-level statements are sound. One cross-lane consequence must be stated before this
merges: it breaks thin consent's opened-view keystone for commuting commands.**

1. *Non-vacuity.* `CommutingAppend` (the result is independent of the planned root header when
   `commutes`) is near-definitional once the arm's only root use is the guarded `staleTarget`. Its content
   is the header's claim that this was the *only* root pin (`planOf` zeroes `preStateRoot`/height,
   `readRequest` observes at the loaded cell). `MovedRootAccepted` and `TwoAppendersOneObservation`
   (two orders over one observation, with built witness data) carry the real content. Accepted.
2. *`CommutingPrepare`'s satisfiable pole* inherits the doc-write fixture's role. The effects-revival lane
   has since proved its poles over `blindedStore` without the fixture, so reuse that witness.
3. *No blinding in the witness.* Every born cell has one, and the kernel rotation is a guarded write
   computed from the *actual* pre-state. That is exactly the part a moved root exercises. Rebuild the
   witness on a blinded cell (`ContentProofs.blindedStore`), so the pole shows commuting through the
   rotation.
4. *Replay.* State `ReplayRefused` through the durable nullifier (the operation id is consumed), not
   through atom presence at the produced post. That holds at every later state without a non-deallocation
   lemma.

**The cross-lane break.** Thin consent's `OpenedDisplayIsCommitStatement` (pass 26, now proved on
lane/thin-birth) concludes `prepared.post address = shown address` for every address that is neither
kernel-owned nor sealed. `shown` is the patch run on the store *opened at the signed root*. For a
commuting command the executor now prepares at a moved pre-state, so addresses other appenders wrote
differ between the actual post and `shown`. Its collision disjunct does not fire, because the two roots
legitimately differ. So the proved keystone either becomes false for commuting commands, or its premises
exclude them, and neither is stated. The honest statement for a commuting command is narrower and is the
member's actual consent: `prepared.post a = shown a` for every address the *member's patch writes*, and
`prepared.post a = prepared.pre.logical a` elsewhere (others' appends kept). Either thin consent gains that
commuting variant, or `checkOpened` refuses thin consent for `commutes = true` commands until it does. That
decision belongs to the thin-birth owner and the root; this branch should not merge before it.

**Correction to the thirtieth pass: the cross-lane break is withdrawn.** Thin consent never accepts a
`.content` target. `memberPatch` refuses it (`unsupportedPayload`, content reads policy coordinates and the
height), and `honest_content_stream_write_named`, accepted earlier, proves the honest content view reaches
that refusal. `OpenedDisplayIsCommit`'s proof closes the content case via `Supported target`. So the
keystone's premise has no content inhabitant, and the commuting relaxation, confined to `computeTarget`'s
`.content` arm, cannot reach it. Commuting appends are consented only through the full-peer provider. The
contention lane may merge as far as thin consent is concerned. Owed only if content ever gains a thin arm:
the commuting variant, in that same commit. The other three thirtieth-pass points stand.

## 2026-10-28, thirty-first pass: share-issue plan window (lane/un-share-window-statement-2 d08d8c1b0, statements)

**Verdict: the shape is right. Revise before proofs, one item blocking.**

The relaxation is honest. `PlannedWithinWindow` accepts the signed descriptor iff it is the rebuild at some
plan height `p ≤ h < p + lifetime`. `lemma_plan_height_determined` makes that `p` unique (`notBefore := p`).
`strict_implies_window` keeps every old admission. The expiry and altered-byte teeth are general. Both the
rebuild and the window read the same submit-time `record`/`authority`, so an install or an epoch move between
plan and submit makes the rebuild differ and the issue stale, never mixed.

1. **Blocking: settle `prepareSourceBirth`'s height.** `admitNative:117` calls
   `GrainResourceBirthController.prepareSourceBirth … ambient.height`. If the submit height reaches what the
   birth *commits* (a grant window, a birth height) while the signed descriptor carries `p`, then the
   committed object differs from the signed one. That is a soundness gap, not just liveness. State it as a
   lemma before proving anything: either `prepareSourceBirth`'s height reaches no committed or
   descriptor-bound field, or it is passed `p`, with the committed windows equal to the signed ones.
2. **Derive the future-plan teeth.** `pole_refuses_future_plan` assumes that every `q ≤ h` rebuilds
   differently from `p`, which `lemma_plan_height_determined` already gives (since `q ≤ h < p`). Drop the
   premise and derive it, so the teeth are unconditional.
3. **The satisfiable pole of the replacement field.** `pole_admits_after_one_tick` covers only the descriptor
   leg, and `premise_inhabited` only asks that a ready ticket with `lifetime > 1` exist. Owed: a
   witness of `AcceptedWindowFields` itself, including the delegation leg's `Prepared … p` with a `Checked`
   envelope. It comes from the same fixture family as item 7, over a recorded transcript.
4. **Location.** These are `scratch/` Props over the admission's types. Move them beside `Accepted` in the
   admission module when the field replaces the strict ones, or they are a parallel statement nothing
   instantiates (law 5).
