# Performance ledger

This file records reproducible measurements, including bad news. It is not a product benchmark
page. Each row names the exact path measured, because the current full-trace reference protocol
and the intended succinct additive protocol are different algorithms.

## Remote committed-source build evidence — 2026-08-09

These are distributed build checks, not performance measurements. Both workers received the same
hashed `git archive` for commit `7ddc9387a267344af65bc6994101d54c560eeefb`, built in unique
project trees with Lean 4.30.0, and retained raw logs plus project-olean hash manifests. Package
artifacts were cached under a host-local lock; no project build output was shared.

| Evidence | Host | Exact target | Result | Claim ceiling |
|---|---|---|---:|---|
| [`E-…1944`](evidence/runs/E-20260809T161944-82276-hbox-7ddc9387a267-lake.json) | hbox, i9-12900 | `Assurance.SemanticAdditiveFriCheckpoint` | pass | This exact committed target builds |
| [`E-…1947`](evidence/runs/E-20260809T161947-82277-persvati-7ddc9387a267-lake.json) | persvati, Ryzen AI 9 HX PRO 370 | `Assurance.BfvNativeBufferAdmission` | pass | This exact committed target builds |
| [`E-…2313`](evidence/runs/E-20260809T162313-5506-hbox-b2c674aee996-cargo.json) | hbox, i9-12900 | pinned-Rust `cargo check --lib` | pass | Native kernel crate compiles at this commit |
| [`E-…2434`](evidence/runs/E-20260809T162434-6741-persvati-4f02bdb3ef9b-lake.json) | persvati, Ryzen AI 9 HX PRO 370 | `Theory.CanonicalTransition` | pass | Canonical transition target builds |
| [`E-…3133`](evidence/runs/E-20260809T163133-21335-persvati-d68e55163d61-lake.json) | persvati, Ryzen AI 9 HX PRO 370 | `Theory.AcceptedCellEffect` | pass | Accepted private cell-effect target builds |
| [`E-…3301`](evidence/runs/E-20260809T163301-22338-persvati-dba294b063d4-lake.json) | persvati, Ryzen AI 9 HX PRO 370 | `Assurance.SemanticHistoryWARPAdditiveJoin` | pass | Dual-root history/checkpoint join target builds |
| [`E-…3622`](evidence/runs/E-20260809T163622-28529-persvati-2851f08caeef-lake.json) | persvati, Ryzen AI 9 HX PRO 370 | `Kernel.DeclaredHyperedge` | pass | Declared N-incidence hyperedge target builds |

The records explicitly make no native-semantics, benchmark, or cryptographic-security claim. The
initial runner trials also caught and fixed SSH argument transport, writable package-hook, and Lean
worker-memory assumptions before these passing records were promoted. See
[`D-0003`](decisions/D-0003-remote-evidence.md) and
[`scripts/remote-check.sh`](../scripts/remote-check.sh).

## Dense/sparse equality-functional crossover — 2026-08-09

This is the first routing benchmark whose two paths target the same Lean expression.
[`mle_sparseTable`](../Compiler/SparseEqualityWorkProfile.lean) proves that MLE evaluation of a
dense scatter-added table equals direct equality-weight accumulation over the active address rows.
It also owns the exact `m = 12`, density, and repetition profile emitted to the native harness.
There is still no Lean/Rust refinement theorem: the Rust run checks the two native outputs are equal
on each deterministic fixture before timing them.

The dense kernel was first changed from `O(m 2^m)` independent products to the exact prefix
recurrence (`O(2^m)`) that shares each equality prefix. The measured plans are then:

* dense: materialize 4,096 equality weights and a 4,096-element scattered table, then dot them;
* sparse: evaluate the 12 equality factors and row-value product only at each active address.

The Lean profile counts `12,286` multiplications for the dense plan and `13q` for `q` active rows;
it also records 262,144 bytes of dense plan-specific live `Tower256` buffers. Common inputs,
allocator metadata, and cache effects are excluded from that byte count.

```sh
bash scripts/run-sparse-equality-benchmark.sh
```

Exact immutable commit: `21d045b08a315f0c1bbcddcbfb0543f141d7b866`. The raw runs are
[`hbox`](evidence/runs/E-20260809T181237-66027-hbox-21d045b08a31-bash.json) and
[`persvati`](evidence/runs/E-20260809T181238-66028-persvati-21d045b08a31-bash.json); both command
and post-run source-integrity checks passed. Their evidence envelopes authenticate source,
dependencies, host, limits, and raw output; they do not turn wall-clock samples into a native
semantics, proof-security, SIMD/GPU, or production-prover claim.

| active rows | density | hbox dense/sparse | persvati dense/sparse | observed route |
|---:|---:|---:|---:|---|
| 64 | 1.5625% | 12.044× | 12.069× | sparse |
| 256 | 6.25% | 3.017× | 2.995× | sparse |
| 512 | 12.5% | 1.508× | 1.501× | sparse |
| 768 | 18.75% | 1.005× | 1.011× | tie |
| 1,024 | 25% | 0.749× | 0.844× | dense |
| 4,096 | 100% | 0.189× | 0.188× | dense |

Here `dense/sparse > 1` means sparse is faster. The two CPUs independently put the crossover at
essentially 18.75% density. A conservative current routing policy is therefore sparse at or below
12.5%, dense at or above 25%, and profile-dependent in between. This is not yet a universal
threshold: it applies to the current scalar recursive `Tower256`, 4,096-point equality functional,
and these allocation strategies. The architectural conclusion is narrower and stronger: the
controller should retain both native work plans and select one from Lean-owned public shape data;
forcing every lookup through a dense column, or forcing every dense table through address-native
evaluation, leaves repeatable factors on the table.

## Archived full-trace reference baseline — 2026-08-09

The benchmark and Rust-owned reference verifier were deleted. These numbers are historical evidence
about the discarded algorithm, not a currently runnable command or selected protocol.

Command:

```sh
cargo run --release --manifest-path prover/Cargo.toml --bin reference_bench -- 7 11 8
```

The fixture is a deterministic topological chain with one public input and `2^log_gates`
alternating add/multiply gates. `ReferenceProof` carries the full trace; the prover densely
evaluates its trace polynomial over the whole multiplicative RS domain; the verifier recomputes
the trace and codeword. `proof_field_words` counts logical BabyBear words, including four words per
extension element and nine per wide digest. It is not serialized bytes or Rust allocation size.

Source snapshot: `b4e20d4447cc` plus the in-progress fix-forward working tree containing
`prover/src/bin/reference_bench.rs` and the reference protocol.

### persvati

AMD Ryzen AI 9 HX PRO 370, x86_64, 12 cores / 24 logical CPUs, release build:

| log2 gates | gates | wires | prove ms | verify ms | proof field words |
|---:|---:|---:|---:|---:|---:|
| 7 | 128 | 129 | 150.870 | 64.826 | 8,248 |
| 8 | 256 | 257 | 298.721 | 109.977 | 10,036 |
| 9 | 512 | 513 | 617.226 | 203.531 | 12,096 |
| 10 | 1,024 | 1,025 | 1,370.081 | 411.047 | 14,556 |
| 11 | 2,048 | 2,049 | 3,403.646 | 891.463 | 17,672 |

### Local laptop

Apple M2 Max, arm64, 96 GiB. The shorter diagnostic run used four queries:

```sh
cargo run --release --manifest-path prover/Cargo.toml --bin reference_bench -- 5 9 4
```

| log2 gates | gates | wires | prove ms | verify ms | proof field words |
|---:|---:|---:|---:|---:|---:|
| 5 | 32 | 33 | 99.671 | 46.138 | 2,696 |
| 6 | 64 | 65 | 187.191 | 78.673 | 3,420 |
| 7 | 128 | 129 | 382.373 | 139.438 | 4,248 |
| 8 | 256 | 257 | 772.468 | 257.764 | 5,212 |
| 9 | 512 | 513 | 1,609.322 | 497.069 | 6,376 |

## Additive transform kernel — 2026-08-09

`prover/src/additive_ntt.rs` implements the full shift-aware unnormalised LCH schedule over an
arbitrary validated GF(2)-independent basis and affine offset. The comparison oracle literally
evaluates the novel-basis transform densely; it is `O(n^2 log n)`, while the new forward transform
is `O(n log n)`. These numbers establish algorithmic crossover and regression targets, not an
end-to-end prover advantage.

```sh
cargo test --release --manifest-path prover/Cargo.toml \
  --test additive_ntt_runtime benchmark -- --ignored --nocapture
```

| host | points | fast µs | dense µs | speedup |
|---|---:|---:|---:|---:|
| persvati | 16 | 25.93 | 151.12 | 5.8× |
| persvati | 64 | 90.88 | 2,335.58 | 25.7× |
| persvati | 256 | 448.97 | 47,485.17 | 105.8× |
| persvati | 1,024 | 2,134.59 | 938,193.45 | 439.5× |
| hbox | 16 | 24.93 | 157.58 | 6.3× |
| hbox | 64 | 126.47 | 3,202.09 | 25.3× |
| hbox | 256 | 621.62 | 63,746.44 | 102.5× |
| hbox | 1,024 | 3,029.43 | 1,245,023.20 | 411.0× |
| M2 Max laptop | 16 | 39.30 | 233.72 | 5.9× |
| M2 Max laptop | 64 | 174.48 | 4,905.49 | 28.1× |
| M2 Max laptop | 256 | 946.14 | 102,851.32 | 108.7× |
| M2 Max laptop | 1,024 | 4,462.59 | 1,924,805.79 | 431.3× |

Correctness tests compare the fast transform with the dense definition across coordinate and
nontrivial triangular bases and offsets, exercise inverse round trips through 256 points over
GF(256), and reject dependent bases and malformed shapes. Still open are exact Lean-selected basis
coherence, Lean-owned scheduling, and commitment/transcript/query integration.

### Archived full-opening additive-FRI round

The Rust proof/verifier and benchmark test were deleted. These are historical measurements of the
discarded full-opening composition; the pure transform/fold kernels remain.

`additive_fri_reference` fast-transforms coefficients, commits all `n` input evaluations, folds
all `n/2` pairs, commits the complete folded word, and verifies both roots plus every equation. Its
proof carries `n+n/2` tower elements, so the round-trip column below mostly measures the current
demo wide commitment—not a succinct protocol.

```sh
cargo test --release --manifest-path prover/Cargo.toml \
  --test additive_fri_reference benchmark -- --ignored --nocapture
```

| host | input points | fold µs | folded Melem/s | full prove+verify µs |
|---|---:|---:|---:|---:|
| persvati | 16 | 11.17 | 0.716 | 1,631.09 |
| persvati | 64 | 21.62 | 1.480 | 6,763.51 |
| persvati | 256 | 59.76 | 2.142 | 27,301.82 |
| hbox | 16 | 35.25 | 0.227 | 5,808.16 |
| hbox | 64 | 72.19 | 0.443 | 24,945.82 |
| hbox | 256 | 190.95 | 0.670 | 99,563.39 |
| M2 Max laptop | 16 | 11.93 | 0.670 | 4,486.51 |
| M2 Max laptop | 64 | 25.00 | 1.280 | 18,157.11 |
| M2 Max laptop | 256 | 68.96 | 1.856 | 73,756.54 |

The commitment leaf encoding is fixed and injective:
`BTL1 || tower level || four little-endian u16 chunks`. Remaining work is transcript-derived
challenge scheduling, sampled openings, multi-round proximity composition, audited commitment
parameters/CR, basis coherence, and Lean-emitted control around unverified compute kernels.

## Archived exhaustive committed-accumulator append baseline — 2026-08-09

The exhaustive Rust verifier and benchmark binary were deleted. These rows are historical
measurements of the discarded full-opening algorithm, not a runnable selected path.

```sh
cargo run --release --quiet --manifest-path prover/Cargo.toml \
  --bin committed_accumulator_bench -- \
  --log-domain 6 --depths 0,1,2,4,8,16,32,64 --markdown
```

This is the landed full-opening reference: each proof contains all 64 values and all Merkle paths,
each append verifies both complete inputs, and code membership uses a direct inverse DFT. It uses
the accumulator-specific transcript wrapper, so the base-field fold challenge is derived only
after both complete claims and roots are absorbed. It is not the queried/RBR/folding-PCS design.

Apple M2 Max, `n=64`, degree bound 2, final-state-only:

| history depth | link commits ms | folds ms | final verify ms | final proof F-words | final claim F-words |
|---:|---:|---:|---:|---:|---:|
| 0 | 0.000 | 0.000 | 32.585 | 3,520 | 74 |
| 1 | 5.048 | 71.645 | 33.157 | 3,520 | 74 |
| 2 | 10.354 | 139.639 | 32.492 | 3,520 | 74 |
| 4 | 20.965 | 313.057 | 40.744 | 3,520 | 74 |
| 8 | 46.878 | 679.208 | 36.698 | 3,520 | 74 |
| 16 | 83.620 | 1,176.974 | 59.600 | 3,520 | 74 |
| 32 | 241.919 | 3,621.989 | 36.290 | 3,520 | 74 |
| 64 | 374.095 | 4,876.871 | 34.791 | 3,520 | 74 |

At depth 64, persvati took 115.968 ms for link commitments, 1,592.517 ms for folds,
and 11.536 ms for final verification; hbox took 398.621 ms, 5,411.307 ms, and 40.742 ms.
Fold totals are approximately linear in history depth at this fixed word size: about 24.9 ms per
append on persvati, 84.6 ms on hbox, and 76.2 ms on the laptop in the depth-64 run. The final object
remains 3,594 field words regardless of depth because only the current accumulator is retained.
With `--retain-history`, retaining all 65 states costs 233,610 field words and measured Linux
high-water RSS was 4,584 KiB on persvati and 3,856 KiB on hbox.

## Interpretation

This path is a correctness and scaling baseline to replace, not evidence of competitiveness. Its
dense evaluation and full-trace proof make proving roughly linear-to-superlinear over this small
range, and verification is deliberately linear in the trace. Plonky3, Binius, Mina, or any
succinct production prover comparison would be misleading at this resolution.

The next comparable rows should separately measure:

1. the sampled, multi-round additive-FRI protocol around the now-measured full-opening round;
2. a native binary receipt/hash trace, reporting constraints and bytes moved;
3. the succinct/RBR accumulator on the same append-depth workload;
4. the first succinct gate-to-LDT proof, including serialized proof bytes; and
5. single-machine and distributed scaling at the exact rate and security parameters used.
