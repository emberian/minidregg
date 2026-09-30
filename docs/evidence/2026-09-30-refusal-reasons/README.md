# Named Host refusals on a fresh Store, 2026-09-30

Every Host refusal now carries a `RefusalReason` from the closed Lean
inductive in `Compiler/RefusalReason.lean`. The reason is produced by the
admission branch that decided the refusal and travels in the
`DREGG/NATIVE-HOST/OUTCOME/v2` frame. `mini` and `mini shell` read it from the
Host's own decoding of that frame and print `refused: <reason>: <text>`, exit 3.

Run 3 (`run-3/`) was run on persvati from branch `mr-refusals` at d4b5ef9
(Lean 4207584 + client d4b5ef9). There were 71 rows and 0 failed. Each refusal
row checks the exit code (3) and the reason named on the first `refused:`
stderr line, or for RAW rows the `reason` field in the Host's own decoding.

| Reason | Who / how | Step | Result |
| --- | --- | --- | --- |
| `no-grant` | an enrolled third key reads with the newcomer's capability (stolen: holder is the newcomer) | 28-N-third (`read stolen`, shell) | refused, no-grant |
| `no-grant` | the same key proposes a write with it | 30-N-third (`invoke …`, shell) | refused, no-grant |
| `no-grant` | the same read through the plain client (`mini query`), no shell | 32-N-cli | exit 3, `refused: no-grant: …` |
| `no-grant` | the third key presents the sponsor's owner capability | 34-N-third (`read owner`, shell) | refused, no-grant |
| `unknown-key` | an unenrolled subject (4242424242) reads | 39-U-stranger (shell; refused at `challenge`) | refused, unknown-key |
| `malformed` | 64 random bytes as a signed query / as a signed preparation | 41-M-raw (op 5), 42-M-raw (op 1) | refused, malformed |
| `bad-signature` | the newcomer's own current signed observation with the last signature byte flipped | 45-B-raw | refused, bad-signature |
| (admitted pole) | the same observation, unmodified, same image | 46-B-raw | answered (op 5) |
| `stale-root` | that unmodified observation replayed after the newcomer's own write moved the image | 49-R-raw | refused, stale-root |
| `revoked` | the sponsor revokes the newcomer's child grant; the newcomer reads, then proposes a write | 54-V-newcomer, 56-V-newcomer (shell) | refused, revoked |
| `law-denied` | the sponsor installs deny-all `any[]`, then reads, then proposes a repair law | 63-L-sponsor, 65-L-sponsor (shell) | refused, law-denied |
| `no-grant` under deny-all | the third key (not a holder) reads under deny-all: it is told `no-grant`, never `law-denied` | 67-L-third (shell) | refused, no-grant |

Controls (exit 0) in the same run: the grant holder reads field 2 = 1 before
any refusal (20); the sponsor still reads field 2 = 5 after revoking the child
(58–59). Row 69 checks that every refusal frame the shell kept under
`homes/*/refusals/` decodes, through the Host, to type `refused` with a
string `reason` (copies in `run-3/refusals/`).

## What is glue

- RAW rows use `raw-host-op.py`, which is evidence glue and not a client verb.
  It frames exactly as `transport::invoke_pinned`, sends one byte payload to the
  same `mini serve` socket, and asks the Host to decode any refusal (op 8). The
  bad-signature and stale-root rows are fault injection. The flipped byte stands
  in for a corrupted or forged signature. The replay stands in for the race
  where a write lands between a participant's challenge and query. The normal
  client re-observes every time, so it does not hit this race on its own.
- The revocation (51–52) is an OPERATOR row. The workspace has no revoke verb.
  The intent is hand-built with jq from the sponsor's own signed read (page root,
  authority root) and submitted by the sponsor through the generic
  `mini submit`. The refusals it causes (54, 56) are ordinary shell verbs.
- `outside-validity` and `stale-grant` were not produced at runtime. Grants live
  10,000 heights and no verb bumps an issuer or policy epoch. They are covered
  by the classifier's `decide` instances (`sample_outsideValidity`,
  `sample_staleGrant`) and the equivalence theorem, not by this run.

## Binaries

| Item | SHA-256 |
| --- | --- |
| Host `bin/minidregg-host-mr-r1` (incremental suffix from qualified e22d16b/build-r3; 242 of 364 modules compiled, 1 inserted, 780 s) | `f171bfb0d11f67002080149169046796637313028f659d1260e004ac0aebc568` |
| Host build manifest `build-r1/manifest.txt` | `f7eebe13ff451f73a670b8216d5dcdc0bdd3bac9cf5ce0a5fcd77730dae83239` |
| `mini` (and `mini shell`) `bin/mini-mr-r1`, `cargo build --release --locked` at d4b5ef9 | `f33998ef4368f3408c6cc97748eae785b6abd70c14e04746704e5446d93ca09c` |
| Store and verifier helpers | as listed in `run-3/binaries.sha256` (bake-off durable copies) |

Reproduce: `refusal-reasons.sh HOST MINI MINI STORE VERIFIER NEW_RUN_DIR [PORT]`.
It stops its sshd and `mini serve` on exit. `run-3/cleanup.txt` lists the
processes still naming the run directory after cleanup: only the harness itself
while it exits.
