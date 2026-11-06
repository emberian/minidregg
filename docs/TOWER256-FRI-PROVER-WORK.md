# Tower256 additive-FRI prover: the native work item, specified in counts

2026-11-06. LEAF-PROVER-DECISION (zkml-research `docs/LEAF-PROVER-DECISION.md`) option (3),
step (c). It specifies what native code computes for the succinct controller
(`Compiler/Tower256AdditiveFriSuccinctController.lean`), what Lean keeps, and how many
operations each side performs. Everything below is counted from the Lean definitions by
zkml-research `notes/construction-search/tower256_fri_counts.py`. Rerun it after any transcript
or codec change. Counts, not clocks.

## 1. Ownership

| owned by Lean (authority) | computed natively (opaque, checked) |
|---|---|
| the public statement `SuccinctStatement` (tower basis and offset, degree schedule, query count, input root) and `TranscriptPins` | the prover's words at every level: the encoding of the input and the `m` folds |
| every transcript byte: `challengeInput`, `queryPrefix`, the seed suffixes, customizations | the Merkle trees at levels `0..m` under `Tower256CshakeMerkleController.hashLeaf/hashNode` |
| the receipt byte codec, a `LawfulCodec (SuccinctReceipt ell m q)` (to be written, Lean-owned like `NativeWorkProfiles`' request codec) | the challenges and seeds, recomputed from those bytes so it can fold and open |
| `SuccinctAccepts` and its decision. The decision must become a `Bool` with `check_iff` (§4) | the openings: three per query per round, with paths |
| the soundness theorem `succinct_accepts_ideal_or_collision` | the final coefficient list: interpolation of the last word |

Native code produces receipt bytes and nothing else. Its reply has no authority until the
Lean codec decodes it and Lean's check accepts it: `Tower256AdditiveFriRawController.run`'s
pattern, with an `OpaqueProofRunner`. Native code needs:
- Tower256 add and multiply in Fan–Paar coordinates. These are the operations Lean now has as
  `Coordinate.add/mul`, proved equal to the field (`Theory/BinaryTowerCoordinateArith.lean`).
  The existing work profile 9101 (dot product) already ships the 32-byte coordinate codec.
- cSHAKE256. `mini_cshake256_32` already exists (`Theory/Sp800185Cshake256Native.lean`).
- An additive NTT over the tower's subspace basis.
- The receipt encoder matching the Lean codec.

**Request** (Lean encodes it): `pins.statementBytes`, the basis and offset (`ell` + 1
coordinates), `m`, `q`, the degree schedule, and the input word's coefficients. The proof's
statement is then the input word's root, which the native reply carries and Lean compares with
`initialRoot`. **Response:** the receipt bytes. The work profile is registered (§5).

## 2. The counts

Parameters: `n = 2^ell` domain, rate `2^-lb`, `m = ell − lb − 2` folding rounds (the final
polynomial has 4 coefficients), and `q` queries for 100 provable unique-decoding bits
(`q = ⌈100 / −log2((1+2^-lb)/2)⌉`, no proof of work). Keccak-f counts exclude cSHAKE's
customization block, which is constant per customization and so cached once. A Lean `xofDigest`
call that does not cache pays one more Keccak-f per call.

| ell | lb | m | q | prover Keccak-f | of which Merkle | of which seeds | prover mults: encode / folds / final interp | proof bytes [A] | verifier Keccak-f | verifier mults |
|---:|---:|---:|---:|---:|---:|---:|---|---:|---:|---:|
| 14 | 2 | 10 | 148 | 73,585 | 65,493 | 7,666 | 114,688 / 32,736 / 32 | 1.46 MB | 53,263 | 3,024 |
| 16 | 2 | 12 | 148 | 271,557 | 262,099 | 8,870 | 524,288 / 131,040 / 32 | 1.93 MB | 68,985 | 3,616 |
| 20 | 2 | 16 | 148 | 4,206,670 | 4,194,255 | 11,410 | 10.5M / 2.10M / 32 | 3.02 MB | 105,982 | 4,800 |
| 22 | 2 | 18 | 148 | 16,791,170 | 16,777,165 | 12,746 | 46.1M / 8.39M / 32 | 3.66 MB | 127,256 | 5,392 |
| 16 | 1 | 13 | 241 | 277,648 | 262,114 | 14,892 | 524,288 / 131,056 / 12 | 3.25 MB | 115,805 | 6,298 |
| 20 | 1 | 17 | 241 | 4,214,396 | 4,194,270 | 19,053 | 10.5M / 2.10M / 12 | 5.03 MB | 175,827 | 8,226 |

Mults are Tower256 multiplications. A single Fan–Paar product is 4^8 = 65,536 GF(2) ANDs in
`Coordinate.mul`'s recursion, and native code uses carry-less multiplies instead.

**What the table says.**
- **The prover is Merkle-bound.** Leaves and nodes each fit one Keccak-f block (66 and 131
  data bytes). That is about `4·2^ell` Keccak-f across all levels, independent of `q`. The
  encode NTT is the only other term of size `2^ell·ell`. For a 4 KiB record (2^12 rows at
  rate 1/4, so ell = 14) the commitment of one column costs 65k Keccak-f. That is roughly
  2,100× the 31 Keccak-f of the record's own cSHAKE content root, which is the leaf's real
  witness cost.
- **The verifier is path-bound.** It is about `q·Σ_j 3(ell−j)` Keccak-f, and every query
  costs three paths per round. Low and high openings are siblings at the same level, so a
  shared path would save about 1/3. That is a receipt-codec change, not a transcript change.
  **Landed (bytes only):** a round opening now carries the `k − 1` siblings above the leaf pair
  (`CPairOpening.pairPath`, level `k = ell − j`); each leaf's full path is that list plus the
  other leaf's hash, rebuilt in `openingDenote`. Per query and round the wire drops `k + 1`
  digests and two length prefixes: `3k − 1` digests become `2k − 2`, so path bytes fall by
  `(k+1)/(3k−1)`, toward 1/3. Measured at ell = 2, m = 1, two queries: openings 551 → 337
  bytes, receipt 724 → 510.
  **Landed after the 2026-11-06 merge:** (a) the checker recomputes one path per pair
  (`recomputesC_pair`, from `recompute_pair` and the last-address-bit lemma `liftBitC_apply` /
  `addressBits_apply`), halving the pair's verifier hashing; (b) no next-level leaf travels.
  Round `j`'s next leaf is round `j+1`'s pair leaf on the side of its last coordinate
  (`coherent_succ`), or at the last round the final polynomial's evaluation, whose path the
  denotation reads from the final column (`CReceipt.nextOf`); `opened_all_iff` shows the compact
  checks are the full ones given the last-root clause. Per query-round the wire now carries two
  coordinates and `k − 1` digests (`3k − 1` digests and three coordinates originally).
- **Proof bytes are path-bound too.** They run from 1.5 to 5 MB at UD-100. Rate is a
  per-leaf trade. At equal message size 2^14, rate 1/2 (`ell` = 15) halves the prover's
  Keccak-f (145k against 272k) but costs 1.48× the proof bytes (2.86 MB against 1.93 MB) and
  1.49× the verifier Keccak-f, because UD-100 needs 241 queries against 148. This is the same
  shape as the recursion-tower grid (zkml-research VERDICTS §9a): the leaf's size decides.
- **Seeds:** each of the `q` seed hashes re-absorbs the whole query prefix (about 7–11 KB at
  these sizes, because lengths are unary). With the prefix's absorbed state cached, seed
  Keccak-f fall from 7,666 to 316 at ell = 14. That is a native-only optimization with
  identical output. **Landed:** the kernel ABI has `mini_cshake256_absorb` /
  `mini_cshake256_finish_32` (`Theory/Sp800185Cshake256Midstate.lean`; `cshake256_cached` proves
  the split equal to the one-shot hash for every input), and `check` finishes every seed from
  the once-absorbed prefix (`seedOfMidstate_eq`). On the ell = 2 honest receipt the framed
  prefix is 1,069 bytes and the two seeds cost 9 Keccak-f instead of 16.

## 3. Unaccounted, stated so it is not mistaken for zero

- **One column.** The controller commits one word per level. A certificate trace has several
  columns (byte, state, position, lookup multiplicity) and needs batching (a random linear
  combination before FRI) or per-column trees. With per-column trees, multiply the Merkle term
  by the column count.
- **No zerocheck or lookup argument.** The DFA relation itself is not yet arithmetized; this is
  the low-degree test only.
- **[A] Path framing:** a 4-byte count per path is assumed; `merklePathStream`'s exact framing
  is not transcribed.

## 4. Lean work this item needs before it can run end to end

1. `SuccinctAccepts` as a `Bool` with `check_iff`. That requires:
   - the basis held as `Coordinate 8` data, with `dom` built by `Coordinate.add` over the
     subspace;
   - the last-level recommitment as a computable Merkle fold over the native cSHAKE extern;
   - the final evaluation by `Tower256FinalPolynomialCheck.evalCoeffs`.
2. The receipt `LawfulCodec` and its pin.
3. The work profile and catalog entry: registered 2026-11-06 (§5), ember's call made
   ("we're allowed to change ALL shapes").

## 5. Registration and the artifact-identity change (2026-11-06)

`Compiler/Tower256FriNativeDeployment.lean` registers the work:

| field | value |
|---|---|
| work | `9104` |
| carrier | `MinidreggV1Artifact.gf2Tower256Carrier` |
| request codec | `9011` / value type `9012`, native ABI, shape `tower256FriProveRequestStream`: `requestStream` (statement bytes, `ell`, `m`, `q`, basis, offset, degree schedule, input word), a `LawfulCodec` (`request_decode_encode`) |
| response codec | `9013` / value type `9014`, native ABI, shape `tower256SuccinctReceiptStream`: `Tower256SuccinctReceiptCodec.receiptStream` at the request's shape |
| kernel tag | `tower256AdditiveFriProve` (Rust entry named `tower256_additive_fri_prove_bytes`; not yet written) |

**Identity.** Two closed enums gained constructors at their ends: `KernelTag` (one) and
`ByteCodecShape` (two). Both derive `Encodable`, so the encodings of existing constructors are
unchanged, but any artifact digest computed over the enum's type, and every exhaustive match
(`NativeGlueGen`, `KernelTag.name`, `ByteCodecShape.name`), changed with them. The new
`Tower256FriNativeDeployment.artifact` is `MinidreggV1Artifact.bundle` extended by the pack:
catalog `[9101, 9104]`, native ABI codecs `[9001, 9011, 9013]`. That is a new artifact identity.
`MinidreggV1Artifact.bundle` and its catalog `[9101]` are unchanged (`v1_lacks_work`); the
Stage-0 artifact (`[9101, 9102, 9103]`) is unchanged and does not contain `9104`. The reply's
only route to authority is `acceptResponse_iff`, which is `checkBytes_iff`.

## 6. The compiled honest prover, and what the umbrella costs to build (2026-11-06)

`lake exe tower256-prover-run` (`Compiler/Tower256SuccinctProverRun.lean`) ran on hbox in 68 s.
- ell = 4, m = 2, three queries: the receipt is 1,140 bytes.
- ell = 8, m = 3, four queries: the receipt is 3,561 bytes.

Both receipts are accepted by `check` and by `checkBytes`. Each shape's mutant fails exactly
the opening parts named in the runner.

**Whole-tree build of this branch (`lake build Minidregg`, 10,420 jobs).**
- Under 12G it is killed for running out of memory when it reaches the umbrella modules, even
  with one Lean worker: those modules load nearly the whole tree.
- Under a one-time 32G grant (one Lean worker, `/tank/dregg-build/fable-tower/md`) it passed in
  2,018 s.
- The peak summed RSS of the `lean` and `lake` processes, sampled every 3 s, was 19.4 GB
  (19,445,332 KB).

Size an umbrella seat at no less than 20 GB plus slack. A 12G lane cap cannot run it.

## 7. The native kernel for work 9104 (2026-11-06)

The kernel is `prover/src/tower256_fri_prove.rs`, reached through
`native_dispatch::tower256_additive_fri_prove_bytes`, the name `NativeGlueGen` already emitted.
Request codec 9011 goes in; receipt stream 9013 comes out.

It is unverified native compute, pinned to Lean byte for byte:
- `lake exe tower256-prover-run --vectors FILE` writes `prover/testdata/tower256_fri_vectors.json`.
  The five request/response pairs are produced by `proveRequest`, the Lean prover, at the unit
  basis:
  - ell 2, m 1, q 2;
  - ell 3, m 0, q 0;
  - ell 4, m 2, q 3 with offset 9;
  - ell 6, m 3, q 3;
  - ell 8, m 3, q 4.
- `tests/tower256_fri_prove_conformance.rs` checks the following:
  - every native response equals Lean's;
  - a trailing byte and a truncated request are refused;
  - changing one statement byte changes the receipt, except at m = 0 with no queries, where the
    transcript draws nothing.

The kernel's limits:
- It takes any basis, but a vector exists only for the unit basis: Lean's reference prover needs
  the independence proof.
- `MAX_ELL` is 24.
- The final degree must not exceed the last level's size.

**The docstring of `Compiler/Tower256FriNativeDeployment.lean` still says "No Rust kernel exists
yet".** It has not been edited in this commit.
