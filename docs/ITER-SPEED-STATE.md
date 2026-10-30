# Iteration-speed lane: state (present-state; rewrite whole, never append)

Agent: the iter-speed lane (successor, 2026-10-30 evening). Order of work, from ember: step 0 the Lean bump,
then (1) interface seams, (2) lane-tree warm pool, (3) hot-swap into a kept world. The integrator asked that,
right after the bump, the umbrella stage get its own warm tree (item 2 first).

## Step 0: Lean v4.30.0 -> v4.35.0 (HOLD LEAN declared; waiting on the hbox build)

- Pins: `lean-toolchain` v4.35.0; Mathlib tag v4.35.0; deps by `lake update mathlib`; REPL pin v4.35.0 in
  `scripts/pipeline/lean-ask-install-repl`. v4.35.0 is installed in both `~/.elan`s.
- The bump is ONE commit on `origin/lane/iter-speed`, rebased on main 929eac696. Mac working tree:
  `/Users/ember/dev/minidregg-lanes/iter-speed-land` (shared packages, Mathlib oleans by cache).
- Mac result: the whole closure (`lake build Minidregg Fixtures ObjectiveProofs CensusChecks
  +Host.Main:leanArts +Host.ClientConsentSession:leanArts`) builds, except `Fixtures/NativeAcceptedFixture` and
  `Fixtures/NativeDocWriteFixture`. Both are red on main 7d90da717 itself, from the private-cells event-id/codec
  change (integrator log hbox:/home/hbox/lanes/integ/umbrellas-out/20261030T214013Z). The proofs lane re-records
  them. The bump also rotates the Objective front-end identity (below), so the accepted fixture needs one more
  re-record, which integ-build4's rerecord stage produces on the bump candidate.
- Integrator protocol: HOLD LEAN sent 10-30 evening. The integrator builds the bump alone on hbox. That build is
  blocked while hbox `/` is at 95% (writes paused, awaiting ember). Kimi reviews the statement and pin diff
  (`claude-kimi -p`, the prompt and output are in the session scratchpad `iter/kimi-*`).
- What 4.35 broke, and the fixes used (statements unchanged throughout):
  - `backward.isDefEq.respectTransparency` is on by default: terms whose types mention non-reducible type-level
    defs no longer unify in instance search, `rw`, `simp`, `exact`. Real fixes where they exist: layouts and their
    Key/Value families `@[reducible]` (35 attributes); explicit `have h : T := e` bridges; `subst` before `exact`;
    simp lemmas (`DataIntent.erase_exactCharge`, `erase_credit`; a file-local `throw e = .error e` in
    Effects/Revival/ContentProofs; `Candidate.intent` of `.ordinary` in Host/DryRun). Where only the old unifier works
    (Mathlib's own `deriving Fintype`, classical `decide` in instances, dependent `rw`s), the declaration carries
    `set_option backward.isDefEq.respectTransparency false in`. There are 187 of these, each on one declaration and
    never file-wide, the same pattern Mathlib v4.35 uses in 1,470 files. One irreducible def needed it too:
    `unseal portal in` for `authorize_names_stored` in Kernel/ResourceObservationAdmission.
  - `throw` in `Except` no longer unfolds under `simp`; proofs that relied on it end with `rfl` or use the lemma.
  - A `match` on a variable inside `do` no longer refines a dependent return type: the match moved outside the
    `do` (ResourceBirthPolicyController, NativeObservationController.checkGrants, Host/Json and
    Host/SourceAgreementJson `verb`).
  - Module visibility: Batteries' derived `DecidableEq (Except ..)` is hidden, so `decide` on `Except` equalities
    became `rfl`, or the file imports `Theory/ExceptDecidableEq.lean`. `String.compare` is hidden in
    `Init.Data.Ord.String`, so Host/Json imports it `all`, the same pattern as its other `Init` imports. ZMod and
    big-Nat `decide` became `decide +kernel` (34 sites). `open private ... from` is gone, replaced by
    `import all Kernel.NativeHost` (NativeThinBirth).
  - Removed core axioms `Lean.ofReduceBool`/`Lean.trustCompiler`: `Theory/AssertAxioms`, `Theory/AssertCompiled`,
    and `scripts/module-hidden-bodies.sh` recognise native_decide by its `_native` auxiliary axiom only.
    `TokenCensus/NativePinSelfTest.lean` plants a native_decide under a standard-three pin and must fail.
  - API: `Std.Internal.Async.TCP` became `Std.Async.TCP` (Host/FnArchivePublisher); `String.trim` became
    `trimAscii.toString`; `alias` is a keyword, so the local identifier in Compiler/ObjectiveBendElaborate became
    `importAlias` (comments and messages keep "alias"; this rotates the Objective front-end identity). Also: the
    Kummer lemma takes irreducibility over `AdjoinRoot`; `dvd_of_fraction_map_dvd_fraction_map` lost a premise;
    `Finset.mem_antidiagonal` became `HasAntidiagonal.mem_antidiagonal`; `HashSet.distinct_toList` uses `==`;
    `Mathlib.Util.MemoFix` is gone; `AddMonoidAlgebra` is a structure; `simp` no longer computes `List.length` of a
    literal cons; norm_num primality of 31-bit primes needs `maxRecDepth 8192`.
  - Slow modules: CommittedTerminalCompose and CommittedTerminalFiatShamir went through `Nat.card` (they took 45+
    minutes after the bump). TokenCensus takes 1,818 s of the Mac umbrella run.
  - Axiom pins: 324 pin sets changed, all within propext/Classical.choice/Quot.sound: 300 gained Classical.choice,
    8 gained Classical.choice and Quot.sound, 3 gained Quot.sound, 8 lost Classical.choice, 4 lost Classical.choice
    and Quot.sound, and 1 lost Quot.sound. 4.35 also wraps long axiom lists across lines, which `#guard_msgs`
    compares, so pins print in the wrapped form.
- Repair tooling (session scratchpad `iter/`): `round.sh N` (build, pin refresh, per-error autofix), `loop4.sh N`
  (rounds until green, the two main-red fixtures excepted), `try.sh FILE` (elaborate one file with the lakefile's
  options), `pins.py BASE` (pin changes, flagging non-standard axioms). Lesson: `guardfix.py` writes the pin text
  verbatim, because 4.35's wrapping matters to `#guard_msgs`.

## After the bump

1. Umbrella stage in a second warm tree (the integrator's 25-30 min umbrella stage holds the main tree's lock):
   send the integrator the command.
2. Seams (design `docs/BUILD-INVERSION-2026-10-28.md`): on main, StoreCodec has 537 Host-closure dependents,
   Theory.Store 630, WorldRoot 443, PersistedCodecTags 478. Measure the recompile count of a representative edit
   before and after each seam; continue only where it moves.
3. lane-tree warm pool: fix the empty-path acquire bug; shared packages plus Lake cache; pools on hbox NVMe and the
   Mac.
4. Hot-swap (rebuild one crate or the Host, swap it into a kept world, rerun one phase). Integrator requirement: the
   swap replaces the binary and re-pins it in the candidate's manifest.json, SHA256SUMS and the Hermes runtime root
   (`deploy/hermes/build-runtime-root --rebind`) together, atomically, and records the overlay in provenance. A
   Store restart otherwise crash-loops on the sha256 mismatch (seen on the rehearsal-3 world).
