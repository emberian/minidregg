# Fleet interfaces: what an agent fleet needs from Mini, as shims Mini can replace

Fleet is an agent orchestration system: many concurrent agent lanes land onto one git `main`, a
keeper attributes and reverts reds, and releases are followed by sha. Its storage backend seam
(`chatnode.backend`: `none | dregg | mini`) has only `none` built today. This directory states
each interface fleet uses or needs, as an interface, its invariants and fleet's behaviour today,
so a Mini (or next-dregg) receiver can be designed against it and checked with the same vectors.
`CLAUDE.md`'s north star names this application ("review verdicts and land-receipts as receipts on
chain"); [`../FLEET-SURFACE.md`](../FLEET-SURFACE.md) is the Mini side that exists.

Nothing here changes Mini. It is fleet's reading, offered as data:

| file | what |
|---|---|
| `schemas/*.v1.schema.json` | JSON Schema 2020-12 for LandRecord (S1), Verdict (S7), AnchorRef (S0), HabitRecord (S10), FireRecord (S11) |
| `vectors/*.json` | conformance vectors, each `{name, why, input, expect}`; derived by `make_vectors.py`, never hand-edited |
| `fleetif.py` | the reference reading: canonical bytes, digests, Ed25519, staleness, ledgers |
| `chat_backend.py` | the S0 ChatBackend contract as a suite any backend can be run under, with known-red controls |
| `FleetLaws.lean` | S5-S8 and S10-S11 reference laws with proofs and concrete teeth (Lean core only, no `sorry`) |
| `evidence/` | nanodregg's GATES-30 reverts gate run over this repo's `main` (S6) |

## Why (fleet's numbers)

Fleet main had 51 red episodes in about 24 hours (fleet's own census, 2026-11-12). By cause:

- 37%: a lane broke a whole-tree rule it never ran (a check over the whole tree that the lane's
  focused test selection did not pick);
- 24%: composition reds, two changes each valid against their base and red together;
- 8%: a stale test double (a fake that no longer matches the thing it stands for);
- the rest: flakes, environment, and plain bugs.

The first two are what S5-S7 address: a check's verdict must say what it read, a land must be
refused when what its checks read has moved, and a red must be attributable to the commits that
touched what the red unit read. Fleet landed 124-168 first-parent commits per repo per day in
October (measured 2026-10-16), from about 10 concurrent lanes.

## Canonical bytes, digests, signatures

- Canonical JSON: keys sorted, no whitespace, UTF-8, integers only (a float is refused).
- `digest(kind, body) = "sha256:" + hex(SHA-256(DOMAIN[kind] || 0x00 || canonical(body)))`, with
  `DOMAIN` = `FLEET.LAND-RECORD/v1`, `FLEET.VERDICT/v1`, `FLEET.READ-SET/v1`, `FLEET.ANCHOR-REF/v1`,
  `FLEET.CHAT-ROW/v1`, `FLEET.HABIT-RECORD/v1`, `FLEET.FIRE-RECORD/v1`, `FLEET.FIRE-BATCH/v1`.
  The record digest excludes `sig`. SHA-256 because git and fleet already use
  it; a Mini receiver would re-hash under cSHAKE256 for its own roots (board/RULINGS.md "Hashes"),
  and these digests stay outside identities, the way `MINI.FLEET-SIGN.RECEIPT-HASH/v1` does
  (FLEET-SURFACE.md:120-126).
- `sig` = Ed25519 over the 32 digest bytes; key ids are `ed25519:<64 hex>`.

## Read sets

A read set is what one check run read of the tree, as nanodregg's tracer reduces a strace
(nanodregg `gates/readset.py:1-12`): entries `{path, how}` with `how` one of `read` (opened),
`absent` (looked up, missing) or `list` (directory listed). A change `{op: add|modify|delete, path}`
moves `read` on modify or delete of the path, `absent` on add of the path, `list` on add or delete
of a direct child. `fleetif.hits` and `FleetLaws.hits` are the same function.

## S0. ChatBackend (the unbuilt seam)

- INTERFACE: `sign(domain, payload) -> row`; `anchor(rows) -> AnchorRef | none`;
  `verify(row, AnchorRef?) -> {valid, anchored: none|pending|final, reason}`;
  `status() -> {backend, lag_rows}`; `refresh(AnchorRef) -> AnchorRef`.
- INVARIANTS (each is a test in `chat_backend.py`): (1) `sign` is local and never waits on `anchor`;
  (2) `anchor` is idempotent on identical rows (exact retry, same ref); (3) a row with no anchor is
  valid if its signature checks, `anchored = none`, never an error; (4) anchoring only strengthens:
  `pending -> final`, never back, and a failed proof leaves the anchor `pending` with the reason named
  and the rows valid; (5) changing backend never changes a row's bytes or signature (the AnchorRef
  sits beside rows, never inside them); (6) an unavailable backend degrades to `none` with visible
  `lag_rows`, never dropped rows.
- PROOF TIMING: `anchor` returns after admission (a receipt exists), not after any proof; a later
  proof or audit flips `proof_state` and never gates a land or a post. Numbers fleet needs from a
  backend: admit p95 per batch, proof lag, max batch, and cost flat in Store height.
- TODAY: `none` only. Rows are signed with a per-seat Ed25519 key or counted as keyed-unsigned; no
  anchor, no proof state.
- MAPS TO: `mini fleet --action publish` for `anchor` (one turn per batch needs several events per
  turn, minidregg#10); the operation record's exact retry for invariant 2 (FLEET-SURFACE.md:128-138).
- RUN A BACKEND: `chat_backend.run_suite(make_backend, seed)` runs three planted broken backends
  first (one blocks signing on the anchor, one weakens a final anchor, one re-stamps rows); if any of
  them passes, every result reads `UNREAD`.

## S1. LandRecord (a land receipt)

- INTERFACE: `append(rec) -> appended | replayed | refused`; `get(land_id)`; `by_sha(sha)`.
- RECORD (`schemas/land-record.v1.schema.json`): `land_id` (`git patch-id --stable`), `repo`,
  `base_sha`, `landed_sha`, `tested_tree`, `test_receipt` (digest of the test run's log and module
  list), `verdicts` (sorted digests of cited S7 verdicts), `member`, `ts_ms`, `sig`. Canonical form
  at most 1024 bytes.
- INVARIANTS: (1) append-only; an exact retry answers `replayed`; (2) appending never blocks the git
  push to main (written after it, in the background); (3) `landed_sha` reaches `base_sha` by first
  parents; (4) one record per `land_id` (other bytes under the same id: `conflict`); (5) `member`
  held `lander` at `ts_ms`.
- TODAY: an unsigned JSONL ledger per repo, lines up to 24 KB because they carry the module list;
  no external anchor.
- MAPS TO: an operation identity per record (FLEET-SURFACE.md:128-138 gives (1) and (4) already);
  a topic stream per lander account (FLEET-SURFACE.md:41-56).
- VECTORS: `land-record.json` (8), `land-ledger.json` (one 6-step sequence).

## S2. Signer

- INTERFACE: `sign(domain, bytes) -> (sig, keyid)`; `verify(domain, bytes, sig, keyid)`.
- INVARIANTS: (1) a signature under one domain never verifies under another; (2) a key rotation
  keeps old signatures checkable by (keyid, epoch); (3) signing needs no network; (4) a seat signs
  only as itself.
- TODAY: a profile-derived Ed25519 seat key; domain separation is per record kind only in this spec.
- MAPS TO: `mini fleet-sign`, the drop-in for Bread's signer (FLEET-SURFACE.md:86-126). Open: Mini
  must enrol fleet's existing seat public keys so signatures made under `none` verify under `mini`.

## S3. RoleTable

- Roles: lane (its own refs), lander (advances main), reviewer (publishes verdicts, cannot land),
  keeper (compensates). INVARIANTS: delegation only narrows; `check` is pure in (table, member,
  verb, scope, time); revocation applies to every later check.
- TODAY: implicit in git hooks and fleet's verbs; no signed table, no expiry.
- MAPS TO: `TypedAuthorization` already narrows (`Scope.Narrows`, Theory/TypedAuthorization.lean:852)
  and revokes (`revokeCapability`). The open part is minidregg#8: `appendObject` ("may speak, may not
  edit", Theory/TypedAuthorization.lean:114-116) exists for streams, but a fleet turn pays from the
  topic's account, so speaking still needs `transfer` (FLEET-SURFACE.md:244-247).

## S4. Settle (attempt table)

- INTERFACE: `next(attempt_state, last_reply) -> submit | lookup | confirm | probe | done(...)`, one
  data table; final only by the verifier's own fold.
- INVARIANTS (nanodregg Protocol/Attempt.lean:10-24): a lost reply is a lookup of the same bytes,
  never a second submit; Host says committed but the own fold says open or forgotten:
  `contradicted`, attempt stays open; `declined` leaves it open; no second copy of the rule in a client.
- TODAY: a land is a request plus a git compare-and-swap; retries only on a server error or a
  remote rejection, never on a refusal; the keeper reads origin/main directly. No `contradicted` state.
- MAPS TO: `mini fleet-sign retry --attempt` and `replayed` (FLEET-SURFACE.md:93-95). Ask: publish
  `mini fleet-sign`'s one-JSON-object outputs as a versioned schema with vectors like these, so a
  non-Rust client can be checked, not just run.

## S5. PinnedLand (the staleness refusal)

- INTERFACE: `land(patch, base_sha, read_set, evidence) -> landed | stale(moved[])`.
- INVARIANTS (`FleetLaws.lean`, proved): (1) `landed` iff no change since base hits the read set
  (`landed_iff_nothing_moved`); (2) a refusal names every moved entry, not the first
  (`land_stale_names_every_moved`); (3) two lands whose writes miss each other's read sets are both
  admitted in either order (`land_commutes`); (4) no partial effect.
- TODAY: git compare-and-swap on the base sha only; a composition red is found after the land.
- MAPS TO: nanodregg's `touches` pins (Kernel/Turn.lean:6-12: "the pin is the one staleness
  refusal"), with the pin taken from a traced read set instead of the diff. Mini's disjoint authors
  already commute (`fleet_disjoint_authors_no_replan`, FLEET-SURFACE.md:58-65); one shared head
  serialises (FLEET-SURFACE.md:197-215).
- VECTORS: `pinned-land.json` (6).

## S6. Gate runner

- INVARIANTS: (1) a unit whose known-red control does not read red is `unread`, never green
  (`green_needs_red_control`; nanodregg gates/runs.py:11-18); (2) read sets include absent paths and
  listings; (3) a red is attributed only to range commits that touched the unit's newest read set
  (nanodregg gates/converge.py:22-30); (4) the report refuses and reverts nothing (the keeper does);
  (5) a commit that takes back hunks of recent landings is flagged unless it says so (GATES-30).
- TODAY: whole-tree checks run after the land; no stored read sets; the keeper bisects.
- MEASURED HERE: `evidence/2026-11-13-reverts-on-main.md` runs nanodregg's GATES-30 gate over this
  repo's 790 non-builder commits since 2026-10-31: 9 flags, one an unnamed take-back still absent
  on `main`.

## S7. VerdictStore

- RECORD (`schemas/verdict.v1.schema.json`): `unit`, `subject` (tree id), `result`, `control`,
  `read_set` (digest), `read_set_size`, `producer`, `role` (`runner | reviewer`), `ts_ms`, `sig`.
- INVARIANTS: (1) one subject per verdict; (2) current for a later tree only while nothing it read
  moved (`stale_persists`: once stale, never current again); (3) a reviewer's verdict is signed by
  the reviewer and a lander cannot forge one (vector `forged-producer`); (4) never deleted or edited;
  staleness is computed, not stored.
- TODAY: reviewer reads are rows in fleet's task store; test receipts are digests in the land ledger;
  no staleness.
- MAPS TO: nothing yet. A turn cannot cite an outside fact; see the external-fact issue linked from
  the pull request.
- VECTORS: `verdict.json` (6).

## S8. Compensation (keeper revert)

- INTERFACE: `compensate(target_land, cause_verdict, scope) -> comp_land | refused(outside[])`.
- INVARIANTS (`FleetLaws.lean`, proved): only paths the target wrote
  (`compensate_within_target`); a refusal names every outside path
  (`compensate_refusal_names_every_outside`); undoing an undo is the original diff
  (`inverse_inverse`); a well-formed diff then its inverse restores every path
  (`apply_inverse_restores`). Not modelled: only a keeper may compensate; both entries stay in the log.
- TODAY: the keeper bisects and `git revert`s; the cause is in the commit message by convention.
- MAPS TO: Kernel/IrreversibleEffectSettlement.lean models a land precisely (a grant names principal,
  target, action, window and attempts, :65-77; release only against the current pre-root, :441-455),
  but its compensation is planned before settlement by the same principal (:236-249). A keeper's
  revert comes hours later, by another principal, citing a verdict.

## S9. ReleaseCert

- INVARIANTS: ok iff a threshold of distinct listed certifiers signed the same (sha, tree, receipt);
  bytes are hashed against the pin before decode; rollback names an earlier certified release.
- TODAY: releases are followed by sha name, no certificate.
- MAPS TO: nanodregg Protocol/Certified.lean (a stranger checks a head from genesis and a
  certificate) and Protocol/Thin.lean (start from a pinned base). Mini's carry already keeps a
  lineage across a re-genesis (docs/RECEIPT-CARRY.md:118-140), so fleet asks nothing new there.

## S10. HabitRecord (an owner-signed trigger and rule)

- RECORD (`schemas/habit-record.v1.schema.json`): `trigger = {kind: fact|event, value}`,
  `steer = {rule, scope}`, `budget = {max_fires, window_ms}`, `owner` (Ed25519 key id),
  `retirement = {idle_ms}`, `ts_ms`, `sig`, plus `kind` and `v`. Identity is the domain-separated
  digest of the unsigned record, not an editable name. Canonical signed bytes at most 1024.
  Rule and scope are identifiers for a receiver's rule table, not executable natural language.
- INTERFACE: `check_habit_record(rec)`; `habit_matches(habit, fact_digest, admitted_facts)`;
  `habit_budget(habit, fire_times, at_ms)`; `habit_status(habit, fire_times, now_ms)`.
- INVARIANTS: a fact trigger names an admitted fact digest; an event trigger matches the event
  kind of an admitted fact, never an unadmitted string. Only the named owner's signature verifies.
  The budget is a pure planning rule over distinct validated fire identities in the open-left,
  closed-right window `(at_ms-window_ms, at_ms]`. It never blocks an already completed act's receipt.
  Retirement folds the complete local history: an idle gap **at least** `idle_ms` is absorbing;
  a later fire cannot resurrect the same habit. Changing a rule or reviving a retired one means
  a new signed record/digest. Out-of-order inputs are sorted; future fires are ignored.
- TRUST BOUNDARY: the admission index, owner authority to install a rule (S3), rule table,
  verified complete fire history and trustworthy time are supplied by the receiver. An owner
  signature alone does not grant authority. Missing/partial history means UNKNOWN, not proof
  of no fires. The fold is a reference law over supplied timestamps, not a Mini exclusion/time
  proof. Neither this schema nor the Lean statements implement those external admissions.
- CONTROL: `test_fleetif.run_habit_suite(answerer)` executes the synthetic inputs and seven
  planted weakenings. Its result uses S6 `verdict_reading`: missing, incomplete or surviving
  planted controls give `unread` (UNREAD), never a qualified green. A signed rule or a delivered
  checklist is not itself evidence that its trigger/rule was tested or followed.
- VECTORS: `habit-record.json` (12), `habit-fold.json` (7). Existing S0-S9 vectors are unchanged.

## S11. FireRecord (a local receipt AFTER an act, never its gate)

- RECORD (`schemas/fire-record.v1.schema.json`): habit digest, admitted `trigger_fact` digest,
  completed `act` digest, `turn`, `lane`, delivered `bytes` digest, `member` (seat key id),
  `delivery = attempted|delivered`, `ts_ms`, `sig`, plus `kind` and `v`. Canonical bytes at most
  1024. `bytes` references the exact content; it does not inline private text. `obeyed` is not
  a field: a delivery receipt cannot certify comprehension, in-context presence or obedience.
- INTERFACE: `check_fire_record(rec, habits, admitted_facts, completed_acts)`;
  `FireLedger.append(rec) -> appended|replayed|refused`; `fire_batches(verified_records)`.
- INVARIANTS: a validated record binds the exact admitted habit, trigger and completed act,
  including seat, turn, lane, content and delivery outcome; both fact time and habit creation
  time <= act time < receipt time. Historical admitted facts may trigger a newer habit.
  The completed-act index must come from a verified external adapter, not from the prospective
  receipt. The local ledger is append-only: identity is `(habit, trigger_fact, turn, lane, member)`;
  exact retry is `replayed`, different bytes under that identity are `conflict`. Input mutation
  cannot edit the stored snapshot. Late truthful receipts remain valid even after retirement.
- ORDERING: the act happens first. Missing keys, recording refusal, unavailable logging/anchoring
  or failed proofs cannot prevent or undo it. `act_then_record` demonstrates this causal order
  with a real callable and a failing recorder; it is **not** a production scheduler and does
  not promise asynchronous completion. A runtime integration must move recording off the act's
  critical path. Nothing here changes a hook, action route, running fleet or Mini runtime.
- BATCHING: keep signed FireRecords in a durable local per-seat log. For a closed UTC hour,
  `fire_batches` sorts/deduplicates fire digests, hashes
  `{kind: fleet.fire-batch, v: 1, seat, hour, fires: sorted_digests}` under its own domain, and
  returns `{batch, seat, hour, count}`. Sign that small payload using S0
  `sign("fleet.fire-batch", payload)` and `anchor(rows)`: **one row per seat-hour, never one
  Store admission per fire**. AnchorRefs cover those S0 rows; the retained local manifest
  provides the individual fire digests. Retry/order produce identical batches. Do not finalize
  an incomplete hour: late-arriving records require a new explicit batch, never silent rewriting
  of an existing anchor. Completeness/retention/recovery remain adapter obligations.
- SCALE: order `10^4` fires/day is a synthetic design workload, not a measured runtime result.
  The test feeds 1000 distinct fires to one seat-hour and checks that its S0 adapter admits one
  row, including retry. Store-height cost, latency, durability and deployment cost are UNKNOWN.
- VECTORS: `fire-record.json` (19), `fire-batch.json` (5), plus ledger conflict/retry tests,
  exact budget-boundary probes and fail-closed control probes.

### Use case: a synthetic review checklist

An admitted `example.review.ready` fact selects the owner-signed
`example.show-review-checklist` rule for `example/lane`. The budget allows at most two plans
per 1000 ms; an idle gap of 5000 ms retires that record. A seat completes the checklist delivery
at `T+100`, then signs its FireRecord at `T+101`. The same-time `T+100` receipt, an unknown
trigger, a changed turn/content or a claimed `obeyed` field is refused. A real recorder
exception occurs only after the example act's visible side effect and is returned as a named
record failure. At `T+5000` with no earlier fire the habit retires; a fire at `T+6000` cannot
resurrect it. A delivered checklist with `obeyed = false` is an explicit counterexample in the
tests and Lean examples, not a claim to measure a model's mind.

`FleetLaws.lean` proves `fire_never_gates`, `habit_stale_persists`,
`absent_control_reads_unread`, and `delivered_does_not_imply_obeyed`, with concrete evaluated
inputs and guarded axiom footprints. S7 `stale_persists` is preserved. These are reference /
conformance laws over this directory's types, **not proofs of Mini receiving-path behavior,
external-clock truth, admission completeness, or model obedience**. A receiving implementation
must restate/bind them to its actual inputs; passing this suite alone is not deployment evidence.

## Where each part lives (proposal)

Mini: S2 domains and rotation, S3 grants, S4 table, S5 refusal, S7 verdict kind (if accepted), S8
law, S9 checking, S1 receipt format. Fleet: git bindings of S1/S5/S8 (patch id, CAS, hooks), the S6
runner and tracer, keeper policy. Joint: these schemas and vectors, versioned together.

## Verify

```
python3 docs/fleet-interfaces/make_vectors.py --check
python3 -m unittest discover -s docs/fleet-interfaces -p 'test_*.py'   # needs cryptography, jsonschema
lean docs/fleet-interfaces/FleetLaws.lean                              # Lean v4.35.0, core only
```

The unit tests include known-red controls: each planted weakening of the reference (signatures
ignored, only the first moved entry named, listings ignored, the control rule ignored, anchors
allowed to weaken) must fail some vector, or the vector set has no teeth.
