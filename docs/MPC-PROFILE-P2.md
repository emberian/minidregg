# MPC profile P2 - what it hides, from whom, at what cost

**Devnet quality. Private computation not audited.** This card describes the
reference private backend `native/private-backend` (crate `mini-private-backend`):
four holders (n = 4, f = 1) evaluate a public Boolean circuit over GF(2^128)
shares with asynchronous ACSS-Id input sharing, a TripleKing preprocessing
stock, layered Beaver-triple multiplication, and a recipient-only output.
There is no simulator proof; the reduction from the checks below to a privacy
statement is an open composition obligation (`CONSTRUCTION.txt`, "Qualification
limits").

## What it tries to hide

The inputs a holder deals, and every intermediate wire value, from **one
honest-but-curious holder** who follows the protocol and logs everything it
receives. The recipient (holder 1 in the measured runs) learns the result and
nothing else. Inputs are dealt through each dealer's own ACSS-Id instance with
polynomials and dealing seeds drawn from that party's own entropy stream
(`entropy.rs`: OS key, or `MINI_PRIVATE_TEST_ENTROPY=<64 hex>` to replay; never
derived from an input value). King preprocessing draws every dealer's seed and
zero polynomial from a per-dealer stream.

## Who sees what

| Party | Sees |
|---|---|
| Anyone on the network | committee size and roster, generation, the **public circuit** (gates, AND schedule, output wires), triple count, packet counts and sizes, message order and timing. Not share values. |
| One curious holder (say holder 3) | its own shares of every input; every opened value (below); ciphertexts it cannot decrypt. |
| The **King** (holder 0 in the measured runs) | everything a holder sees plus the King's richer preprocessing view. **Not covered by the check.** |
| An input **dealer** | its own inputs in the clear (it chose them). |
| The **recipient** | the result. In the 429 diagnostic: the whole 154-bit final state at holder 1 only. |
| A coalition of 2 or a malicious party | **Not covered.** f = 1 means any 2 holders reconstruct every share. |

Opened values in the layered MPC are `x + a` and `y + b` with `(a, b, c)` a
checked triple whose masks are uniform; they are the same in every execution
the curious holder cannot tell apart (see "Evidence").

## What leaks, said plainly

- Circuit shape, triple count, schedule and traffic pattern: public by construction.
- PrivSend ciphertexts addressed to other holders and dZK column-proof frames
  are **not simulated**; their hiding is the classical-ROM property of those
  components (SHA-256 pad keyed by an ASKS key of which the curious holder has one
  degree-f share; salted Merkle roots). The check lets exactly these classes differ.
- Arithmetic is variable-time GF(2^128): timing side channels are open.
- At rest, every WAL (`transition_journal`) and the `.initial` files hold dealing
  polynomials, seeds and shares **in the clear** under mode 0600. The storage
  premise is an honest crash disk: a checksum detects tears, not tampering or
  rollback. Key and share custody beyond file permissions is not constructed.
- Static corruption only (set fixed for the run); no adaptive corruption, no
  simulator, no QROM/post-quantum AMPC theorem, no guaranteed output delivery.
- Native deployment join is open: the clear v1 native route sees every share body
  (trusted-controller profile); confidential v2 refuses until recipient-only
  sealing is joined. This card says nothing about the native mailbox.

## Evidence (class: executed unless stated; box f4 burst-lane1, release build)

Secrecy check (`private_view.rs`, width-8 private adder, holder 0 deals 255 and
holder 2 deals 1): holder 3 logs 8067 frames across input ACSS, King
preprocessing, King, layer MPC and output. A simulator builds worlds
B = (1,255) and (128,128) from world A = (255,1) honest randomness (each dealing
polynomial moved by delta*L, L(0)=1, L(alpha_3)=0; King extraction, challenge and
mask compensation) and **runs** them. Holder 3's transcripts are byte-identical
except the two ROM-hidden classes above; King, layer-MPC, Sh2t and output frames
are all identical; the recipient decrypts 256 in every world. The statement is:
holder 3's view, apart from ROM-hidden frames, is consistent with at least three
input pairs. It is not a simulator proof.

Instrument goes red (logs under the lane `logs/`):
- the retired public-coefficient dealing (degree-1 coefficient `37+i`) is decoded
  by holder 3 (`retired_public_coefficient_dealing_is_decoded_by_the_curious_holder`);
- a planted leak in the layered MPC (triple masks forced to zero, so every opening
  is the plaintext wire) fails the transcript check at a layer-MPC opening frame (frame 7491, `Opening` gate 0, from holder 0)
  (`m1-leak-zero-masks.log`, diff `m1-mutation.diff`).

## Measured cost

Box burst-lane1 (24 threads, shared; load average 40-49 during the runs, so wall
is inflated by contention: the 429 run used 144 s of CPU in 314 s of wall).
`/usr/bin/time -v`, peak RSS is the largest single process.

| Run | Test wall | Command wall | Peak RSS | Log |
|---|---|---|---|---|
| D1/D2 six filtered tests (3 r31/r40 baselines, 2 private_view, entropy) | 3.0 s | 50.0 s (46.7 s build) | 874 MB | `d1d2.log` |
| Width-8 private adder with transcript check (largest of the six) | 2.7 s | | | `d1d2.log` |
| **429-stock Objective identity** (153 ACSS inputs, 429 checked stocks, 13716 AND tuples, 34696 gates, 13563 anchored rows, 154 outputs), heavy profile | **313.8 s** | **5:14.3** | **266 MB** | `d3-429.log` |
| King composite store: 6 tests incl. kill -9 (all four holders, count 1) | 67.8 s | 82.4 s | 902 MB | `d4-king-store-3.log` |

The 429 run (`--profile heavy`, one process) passed: user 139.9 s, system 4.2 s,
45% CPU, 0 swaps. A laptop run of the same test took 271.7 s (macOS, unmeasured RSS).
It is a correctness-and-recovery diagnostic, not a secrecy check: it has no
transcript tap, and all 153 inputs are dealt by holder 0.

## Crash recovery (King composite store, `king_store.rs`)

One `transition_journal` per holder over the three ACSS-Id instances, the three
Sh2t-Id instances, the preparation burn receipt and the TripleKing. A
`kill -9` of a child process mid-King recovers from disk alone with: one dealer
event per ACSS and per Sh2t instance, no new anchor allocation at any holder
(6 per holder before and after), and complete checked triples that are an
exact degree-f sharing with c = a*b. A crash between the anchor burn and the
journal record is repaired from the retained local receipt by
`PreparedBasis::from_burned`, which verifies the receipt against the exact
manifest and consumer generation and allocates nothing; a receipt for another
generation or with a flipped byte is refused. An identical receive event is
dropped before it reaches the journal.
Mutants that go red: dedupe removed (`m2-no-dedupe.log`), burn that ignores the
retained receipt (`m3-reburn.log`).

## What this profile is not

Not Native Qualified, not privateRecovery, not a source YES. Local anchor/path/MAC
receipts are not common custody qualification. See `CONSTRUCTION.txt`.
