# Seat: bytes-repr

Agent: the bytes-repr lane (2026-11-08), a subagent of the root session; `cv lanes` finds it by this file's commit.
Mac worktree: /Users/ember/dev/minidregg-lanes/bytes-repr (branch `lane/bytes-repr`, landed on `main`). hbox pool
tree t6 (lease `bytes-repr`, native-linked packages), scratch and tools under `hbox:/ci/pc/bytes` (a private copy
of the w13 Store at height 3,777 in `w13c/`, `mc2.py`/`meas.py`/`cons1.sh`/`ab.sh` for opens, `w13run.sh` and
`hostab.sh` for the census on `/ci/pc/w13`).

Owns: runtime bytes as `ByteArray` (ember, 2026-11-08: `List UInt8` costs ~24 bytes per byte); the ratchet
`scripts/check-bytes-repr.sh` and its ceiling `scripts/gates/bytes-repr.max` (wired into local-gates, the
merge-gate checks and the builder's `ratchets` stage); the Store read's byte representation
(`DurableReceiverIO.Entry`, `StoredCheckpoint`, `parseStored`, `readWhole`) and the packed hashing/decoding seam in
`Compiler/DurableHistory.lean` (`hashBytes`, `recordHashBytes`, `leafDigestBytes`, `decodeRecordBytes`,
`storedRecordDigestBytes`, `chainStepStoredBytes`, `openSealedWithBytes`, `openSealedBytes`, each with its `_eq`
to the list specification) and `DurableLogTags.chainPrefixesStoredBytes`.

Quest: every byte path the Host and the consent provider execute is `ByteArray`; `List UInt8` only as the spec
model, tied by `_eq`. Hot path first (open, decode, hash, append), lowering the ceiling with each commit.

## Landed
- `e8e3bb8c8` the ratchet (first ceiling 4,929).
- the packed open (this file's commit): record bodies and checkpoints packed end to end on the open; the whole-log
  read paged (`readWhole`: the read from the checkpoint, then the entries below it 256 heights per `history` call),
  which removes the 64 MiB reply wall the full open hit on w13 at height ~3,860 (every member's consent provider
  refused to start: "native helper reply read declares 67924477 bytes, over the 67108864-byte bound").
  Statements rephrased: `entryExact` and the receivers' readback theorems read `entry.record.toList`.
  Layout unchanged: the Store's bytes, records, tags, nodes, indexes, cells and keys are byte-identical (the Host
  image changes; no migration content).

## Numbers (hbox, shared; load beside each)
Consent provider cold start on the w13 copy (3,777 records, checkpoint at the head), main 7670c1ef0 against this
lane, interleaved, `mc2.py` (one admitting frame, VmHWM):
| load | binary | first admission | CPU | peak RSS | held RSS | the read |
|---|---|---|---|---|---|---|
| 27 to 29 | main | 42.8 s, 40.6 s | 41.9, 39.6 s | 2,949, 2,953 MB | 1,653, 1,657 MB | 10.3, 9.7 s |
| 27 to 29 | this lane | 32.6 s, 29.2 s | 31.9, 28.6 s | 1,656, 1,710 MB | 1,656, 1,710 MB | 1.2, 0.8 s |
| 13 to 16 (earlier, unpaged build) | main / lane | 35.0, 30.1 s / 19.6, 35.2 s | | | | 8.7, 8.0 s / 1.4, 1.4 s |
On w13 itself (height ~3,850 to 3,880): the first `credit` after a swap (consent cold) 32.5 s (main, load 11) and
32.1 s (this lane, load 26); with main's provider at height 3,880 every signed command refuses (the 64 MiB wall),
with this lane's it answers. Store Host light open on the copy: unchanged (0.97 to 1.7 s, 277 to 283 MB peak).
Warm, same consent provider and mini, Host only (main 91f30657 against this lane, `hostab.sh`, 10 runs x 2, load
22 to 25): `credit` 15/17 against 16/16 ms, `doc show` 18/20 against 19/16 ms, `say` 168/170 against 171/176 ms (op 2
84.9/84.1 against 82.2/83.1 ms): no change on the warm path, as expected.

## Next (in order)
1. `DataWrite.canonicalPostBytes : ByteArray` with a packed field codec whose cursor slices (no list): the held
   1.65 GB of the consent provider and the full image is the decoded records' post images (534 births at 62 to 107
   KB each carry the authority cell); about 226 occurrences in 89 files, then `DataSnapshot`'s cell bytes.
2. The open that neither reads nor holds the prefix: KN2 2b (host-execution retypes the Host session and
   `NativeHostReplay` over the light `Opening`), then read-path ports `ClientConsentCore`/`ConsentAnchor`. Until
   then the full open still reads every entry (paged) and decodes every prefix record: O(height).
3. Tags, seed and node rows as `ByteArray` (`blobAt` still slices them into lists; ~18 MB at w13), then
   `MacKey`, `Digest` encodings and the served state's cells (store-retained's `Held`).

## Seams
- perf-client (a3d786ed4bc2b5bf0): adds `moved` to `DurableServed.Received.appended` after this lands.
- host-execution / read-path: item 2.
