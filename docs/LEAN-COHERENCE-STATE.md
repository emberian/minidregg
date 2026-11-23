# Lean coherence lane: state (lane/fae-4)

The Lean lane of `docs/BACKLOG-2026-10-27.md` §3, as it stands. Worked on the Mac warm tree
`/Users/ember/dev/minidregg-lanes/fae-4`. Main carries everything through `aaf73ce1`.

## What landed

- **FB4 (O15–O17).** 23 modules, 2,071 lines deleted: the three uncalled lifecycle receivers, the four
  census-only V1 lifecycle modules, `Host/WorldPrototypeDefinitionAuthor.lean`, and 15 orphan case
  batteries. The orphan list was derived from the `^import` graph against the `Host.Main` and
  `Host.ClientConsentSession` closures: a file qualified if it had at least five theorems, at least 60%
  of them closed cases, and only umbrella importers. Kept from the triage list:
  - `AirSumcheckCubicConformance` and `ZkmlMatmulConformance` write `prover/testdata`.
  - `ObjectiveBendC4Vectors` is used by `check-objective-frontend.sh`.
  - `DefaultLaw` is used by `scripts/gen-default-laws.lean`.
  - `ZkmlTraceCheck` is a reader, `MixedFieldBudget` is pricing, and `ObjectiveBendDigestChecks` holds
    axiom pins and a teeth witness.

  `TotalProof` is gone. `mix_append` and `composition_associative` are deleted: tying them needs a
  semantic theorem about `Term.mix`. `every_admission_is_turn` is now `census_shapes_admitted_at_w0`.
  `Host/ApplicationBirthAuthoringCheck` gained the `payControlCapability` genesis field (main was red
  after S1).
- **O20.** The Host closure carries no Selvage module: 787 → 776 modules (Selvage 12 → 0, Theory +1),
  ceiling 776. `Theory/BinaryCubeAddress.lean` holds the cube-address equivalence, which
  `Selvage.BinaryLookup` re-exports. `Compiler/AuthenticatedColumnSelvage.lean` holds the
  controller-to-Selvage adapters. The Deployed closure is Selvage-free too.
- **O18 so far.** `Theory/CollisionFloor.lean` exhibits the vacuity:
  - `HashBytes.collision_of_fixed_width`
  - `collision_of_cshake256Bytes`
  - `AuthTrie.collision_of_finite_digest`

  The scoped floors are `AuthTrie.CollisionAmong` (over `TreeNode` and `ClimbNode`) and
  `HashBytes.CollisionAmong` (over named preimages), each with `mono` and `global`. These theorems are
  restated and reproved, axiom pins unchanged:
  - AuthTrie: `tree_dig_terminal`, `climb_sound`, `verify_sound`
  - `AuthTrieCache.root_lastVal_eq`
  - `DurableIndex.lookup_sound` and `Answer.sound`
  - `ObjectiveBendDigest.binds_or_collides` and `sealed_binds_or_collides`
  - `HashEqDigest.binds_or_collides`
  - `HashEq`: `hashEq_binds_or_collides`, `hashEq_reveal_binds`, `hashEq_reveal_binds_each`,
    `hashEq_context_bound`
  - `SealedMarket.market_reveal_binds`
  - `PredCompile.lower_hashEq_binds`
  - `LogAccumulator.rootOfPath_sound` and `verify_sound`, then `DurableHistory.verifyAt_sound`
    (`NodeCollisionBelow`: a second preimage of an honest block below the covering frontier block)

## O18 remainder, by file

The shape for each:
1. Name the finite set the proof's witness pair comes from.
2. State `P ∨ CollisionAmong H S`.
3. Thread membership through the proof (`CollisionAmong.mono` at each recursive call).

Consumers that are not restated yet take `CollisionAmong.global` and stay vacuous until their own pass.
Re-grep `∨ Collision`; the old statements are often multi-line.

- `Kernel/DomainEpoch.lean`: 11 theorems (about 382, 392, 503, 509, 515, 549, 610, 747, 780, 963, 992),
  each ending in `Collision (cshake256Bytes tag)`. `collision_of_cshake256Bytes` makes them true
  outright. Use `HashBytes.CollisionAmong` over the absent, tick and cell preimages each proof hashes.
- `Theory/AuthTrieRange.lean` (114, 182, 264): the reveal path. Mirror AuthTrie's `TreeNode`, plus the
  reveal's node set. Then `DurableIndex.reveal_sound`.
- `Selvage/BinaryMerkle.lean` (43 `LeafCollision ∨ NodeCollision`, 200, 264, 278), then
  `Compiler/Tower256CshakeMerkleBinding.lean` (254).
- The coordinator's list also names StoreCodec, AuthMapCommitment and CanonicalResourceEffect. A plain
  `rg '∨ Collision'` does not find them; search for multi-line statements.
- **Sites that weaken back to the global floor:**
  - `Kernel/WorldRoot.lean` `deployedRoot_binds`
  - `Kernel/ReceiptContinuity.lean` `opens_sound` (via `worldDig_collision`, which also needs a scoped
    form)
  - `DurableIndex.reveal_sound`
- **`¬ Collision` premises** (the same vacuity flipped: the premise is uninhabitable at a fixed-width
  digest). Replace each with a hypothesis on the hashed inputs, in the `RowsCollision` shape of
  `Compiler/DurableIndex.lean:692`:
  - `Kernel/WorldRoot.lean` `rootBinding_of_noCollision` (`nodes : ¬ AuthTrie.Collision dig`)
  - `Compiler/CommittedTerminalRealizer.lean` (503, 507)
  - `Selvage/BinaryMerkle.lean` (287)
  - `Selvage/HashFamily.lean` (110, 119)

## O19 (not started)

`HostStep.derived` (`Kernel/HostRefinesWorldCore.lean:418-434`). Statement first: add the refusing
pole `Turn.ofAdmission … = .error r → ∀ ready, prepare … ≠ .inl ready`, or make `Turn.ofAccepted`
total (RECEIVER.md §3). Measure the refusing-path gap before any proof. Then put `World.admit` in gate
mode on the receive path (plan C1, `Host/WorldSim.lean`).

## O61, for L1 to land with genesis frame v8 (do not bump the frame here)

Mirror the pay control on the clock cell:

- **Genesis field and capability.** A new `Config.clockControlCapabilityId : CapabilityId`, parsed as
  `clockControlCapability` beside `payControlCapability` in `Host/Json.lean` and
  `Host/SourceAgreementJson.lean`. Define:
  ```lean
  def clockControlCapability profile config : Capability .program :=
    rootCapability profile config .program config.clockControlCapabilityId
      config.factoryController.subject <clock cell physical id>
  ```
  Its scope is `{installPolicy, revokeCapability, delegateProgram}`, never the tick verb. Add it to
  `entries` (`Kernel/NativeHostGenesis.lean` near 669 and 735).
- **Statements.**
  - `clock_control_present`: the mirror of `pay_control_present` (`NativeHostGenesis.lean:1126`). The
    entry is in `entries`, the holder is the factory controller, the targets are exactly the clock cell,
    and the verbs include the three above.
  - `clock_control_cannot_tick` (controller not among the tickers):
    ```lean
    (other : config.factoryController.subject.value ∉ config.clockTickers.map (·.value))
    (named : new.get "request/subject" = some (Int.ofNat config.factoryController.subject.value))
    (ticking : new.get "request/verb" = some (Int.ofNat tickVerbTag)) :
      Pred.eval (clockPredicate config) old new = false
    ```
    The proof is `clock_refuses_nonticker_tick` (`Kernel/ClockLaw.lean:156`).
- **Poles.**
  - Satisfiable: a law installed by the controller that names a new ticker admits that ticker's tick
    (the shape of `pole_tick_admitted`, `ClockLaw.lean:253`).
  - Teeth: the controller's own tick is refused (a decided instance of `clock_control_cannot_tick`).
- **Registry and client.** Nothing new.

## Working here

- `lake env lean FILE` needs `--load-dynlib=.lake/native/libmini_kernels_lean.so` for anything that
  hashes; run `scripts/build-mini-kernels.sh` first.
- **The Mac's open-file ceiling is known.** A Virtualization.framework VM holds about 213K of the 491K
  system file slots. As a result:
  - `Selvage.PolishchukSpielman` and `Assurance.TwoRegimeQueryBudget` (`import Mathlib` whole) never
    elaborate here.
  - Large parallel builds hit ENFILE at random; rerun and the build resumes.

  Do not fight it.
- `scripts/check-host-closure.sh` counts `git ls-files`: run `--update` after `git add` of new modules.
