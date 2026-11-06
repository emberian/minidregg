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
`initialRoot`. **Response:** the receipt bytes. A work-profile ID is to be assigned in
`MinidreggV1Artifact.nativeWorkCatalog`. Doing so changes artifact identity, so it is not done
in this step.

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
3. The work profile and catalog entry (an artifact-identity change: ember's call).
