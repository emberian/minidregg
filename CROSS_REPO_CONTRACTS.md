# Cross-repository contracts — current truth, 2026-08-14

This file is the narrow interface sheet for the receipts-native compute
fabric.  It is not a deployment claim or a second architecture narrative.
`REORIENTATION.md` explains why the boundaries exist; this file says what may
cross them.

All artifacts are neutral data until the receiving layer decodes them,
checks their registered version and source identity, and proves the relation
it owns.  No producer may serialize authority, acceptance, or durability into
existence.

## 1. Preoscript / leanuweave → minidregg

### Planning-data crossing

Use a checked **Projection V3** artifact for rich partial-computation data:
declarations, guarded fields, futures, query/result/certificate rows, selected
plans, escalation actions, and witnessed budgets.

The artifact must carry:

- schema and codec versions;
- stable declaration/session/plan/budget identifiers;
- the exact source/artifact identity;
- canonical bytes and a bounded successful decode/validation result; and
- the selected resource profile and its realized budget evidence.

minidregg may use those values to construct or constrain a request.  It must
independently bind the request kind, subject, target, verb, arguments, effects,
pre-state root, policy, nonce, and cost context.  A plan is never an
authorization witness, scheduling permit, semantic receipt, or proof-system
acceptance bit.

### Context-auth crossing

Use the checked **RuntimeAuth V4 sidecar** only where a runtime crossing needs
context-bound grant/roster/resource facts.  Its decoded manifest remains
neutral.  minidregg must independently validate the context pin, signature or
attestation profile, authority and membership policy, nonce/operation scope,
and exact request binding.

Projection V2 is not the default new crossing.  The independently owned
`Compiler/UwueavePreoProjectionV2.lean` lane must not be merged merely because
its generated Rust data is well formed; first decide whether the consumer
needs V3 planning data or the narrower V4 context sidecar.

## 2. breadstuffs / Dregg2 → Selvage and minidregg

The implementation rail may emit only candidate data and versioned verifier
artifacts.  The minimum proof-suite export is:

```text
ZkmlSuiteArtifact
  source repository + source commit + artifact content identity
  statement/proof/transcript codec versions
  base field modulus and canonical base-field codec
  extension degree, defining polynomial, basis, and extension codec
  Poseidon2 width, rate/capacity, S-box, round schedule
  round-constant and linear-layer canonical data/identity
  leaf/node/domain-separation rules and digest layout
  Merkle arity, leaf packing, path codec, root codec
  protocol id and mode (IR-v2 FRI or BaseFold/RS)
  code rate/domain layout, query count, grinding rule
  exact Fiat--Shamir alphabet and ordering
  checker/controller id, version, and content identity
```

The producer must attach checked meaning to the first-order export and retain
known-answer/refusal vectors.  Selvage must not hand-copy constants, infer a
suite from benchmark fixtures, or treat Rust/Plonky3 verification as its own
theorem.

One native computation response has the shape:

```text
CandidateComputation
  exact request/statement identity
  model and weight identities/roots
  canonical input identity/root
  candidate canonical output bytes/root
  proof bytes or an explicit native error
  selected suite/checker identity
```

Native success means only that bytes were returned.  Decode failure, version
mismatch, wrong request/statement identity, wrong root, checker rejection, or
an unavailable registered suite all fail closed.  Native code never returns
the minidregg acceptance bit.

## 3. Selvage → minidregg

Selvage returns checked evidence about one exact typed statement.  An accepted
evidence object must bind:

- the exact statement and C/A/B commitment roots;
- the contraction claim and claimed output root;
- the exact transcript/checker/suite/codec identities;
- every opening and verifier decision consumed;
- the named algebraic, proximity/query, commitment-collision,
  Fiat--Shamir/ROM, grinding/beacon, and registry terms; and
- the claim ceiling (exact recomputation, interactive IOR, ROM theorem,
  executable checker, or deployment evidence).

The raw BaseFold theorem currently supplies
`m·3/|F| + (1−τ)^q + Pr[accepted position equivocation]` and an exact
flat-hash collision witness.  A deployed Merkle/Poseidon2 suite must replace
that final event with its own path/codec collision reduction and price the
remaining sponge/ROM game.  The Tower256/cSHAKE additive-FRI controller is a
proof pattern, not the zkML suite.

Evidence does not authorize a request.  minidregg admits it only under the
request-indexed disclosure/audit policy of the same `CommittedTurn` whose
authority, effects, pre-state, post-state, and delta it already owns.

## 4. minidregg → durable history

Only a semantically accepted turn may produce the durable envelope.  The
envelope must bind:

- transaction id and exact request identity;
- canonical result bytes and their post-state root;
- read guards, writes, nullifiers, and exact charge;
- versioned receipt/audit event bytes; and
- the exact replay identity.

Install is atomic at the logical model.  An identical retry is replay; the
same transaction id with changed result or audit bytes is conflict.  These
facts do not prove SQLite, FFI, filesystem, fsync, stable media, power-loss,
replication, consensus, or liveness.  Each physical adapter needs its own
refinement statement and evidence.

## 5. zkml-research → engineering decisions

Research verdicts are decision inputs, never runtime inputs.  A promoted
decision must name the verdict commit, underlying source/measurement commits,
measurement unit, security regime, and any withdrawn/conjectural premise.

Current pins:

- production-shaped IR-v2: BabyBear, Ext4, Poseidon2-w16, FRI,
  `(log_blowup, queries, grind) = (6,19,16)`;
- its query column is 34 UDR / 73 JBR / 130 withdrawn-CBR bits;
- `(2,57,16)` is priced but not landed and requires a recursion-verifier
  `num_queries` pin first; and
- the selected multilinear research route is BaseFold/RS in the unconditional
  `(1−ρ)/3` regime, eventually instantiated over the intended zkML
  extension-field/Poseidon2 suite.

## 6. First end-to-end target

The target remains one authorized audited linear-layer turn:

```text
checked Preoscript planning data
  → exact minidregg request and authorization
  → breadstuffs candidate output/proof bytes
  → versioned Selvage checker and explicit failure ledger
  → exact semantic post-state/effects/receipt
  → atomic durable envelope, reopen, and tamper refusal
```

`Assurance/ZkmlMatmulAuditTurn.lean` is the landed semantic floor: exact tiny
recomputation, authorized evidence disclosure, canonical logical install,
history append, replay, and adjacent refusal.  It does not yet consume a V3/V4
artifact, native candidate, succinct checker, deployed registry, production
codec, or physical store.  Those crossings should replace its fixtures one at
a time without weakening its request binding or refusal teeth.
