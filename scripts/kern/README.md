# Objective charged-refusal OOM regression

The failing pipeline `call` row completes `c6-direct`, plans `c6-no-grant`
successfully, then grows inside the native Host during its actual charged
submission. The refusal is an extraction-account wrapper around
`lawDenied(vault, "deposit", LawLeaf)`. The exact leaf has path `[2]`, clause
`any [eq "request/subject" 7]`, and absent before/after values. Its existing
lawful byte stream is 46 bytes.

## Mechanism

`417e8438` introduced `encodableOfLawful`, which passed a lawful codec's bytes
through the generic `Encodable (List UInt8)` instance. `rejectStream` then
encoded the derived `Reject` natural with `StreamCodec.nat`.
`a6c865f9` normalized recursive call accounts but retained this leaf encoding.

Mathlib's `Logic/Equiv/List.lean` defines each list cons as
`N' = 1 + Nat.pair(byte, N)`. `Data/Nat/Pairing.lean` defines the pair as
`N*N + byte` when `byte < N`, otherwise `byte*byte + byte + N`.
Once the tail exceeds 255, every preceding byte squares that tail. Its bit
length therefore grows as Θ(2^n) in the serialized byte length `n`.
Even an all-zero 46-byte list has an encoded integer requiring over
`9 * 2^41` bits (over 2 TiB): five zero bytes already encode to 677, and
each subsequent cons is at least the previous natural squared plus one.
The Host dies while constructing intermediate integers, before any such
integer can reach the wire.

This path runs in `failedEvent`'s canonical charged-record payload and the
native charged outcome. The prepare-only plan can render the typed refusal
without constructing that payload. This accounts for the observed boundary;
there is no driver `lake env lean` step at `c6-no-grant`.

## Fix and format edition

`Kernel/ObjectiveActivityReceiver.lean` uses typed byte `StreamCodec`s for the
complete refusal tree. Constructor sums are balanced; products concatenate
field streams; lists retain their lengths. It reuses the existing lawful
String, LawLeaf, Capacity, Digest and integer codecs. Recursive upgrade
conflicts retain their depth and terminal, and recursive extraction accounts
retain the ordered list of `(remaining, spent)` pairs. No `Encodable` natural
is used by the refusal codec.

`callRefusalStream_prefix_roundtrip` and `rejectStream_prefix_roundtrip`
prove exact typed reconstruction with any following bytes; their injectivity
theorems exclude two typed causes sharing bytes. The existing
`callRefusal_encode_roundtrip` name now states the live byte-codec roundtrip.
Recorded-disposition, replay/retry, rollback, and current-authority theorems
remain in place.

Changed greenfield payloads have explicit editions:

- `DREGG/OBJECTIVE/ACTIVITY/REJECT/v2` replaces the paired-natural v1 cause.
- `DREGG/OBJECTIVE/ACTIVITY/RECORDED-FAILURE/v2` replaces its v1 charged-record
  envelope. The outer activity event still has `codecVersion = 2` and repeats
  the original successful ingress event/domain/event id.
- Both old payload editions refuse to decode, proved for arbitrary bodies.
  Existing charged records and any retained artifact/digest committing to
  their exact canonical bytes must be re-emitted on fresh worlds. Success
  event bytes and the original signed ingress/receipt identity do not change.
- Rebuild **both Host and native consent**, and every other semantic executable
  that decodes/replays these charged records. An old consent image rejects a
  new charged history at its first new failure envelope; the harness observed
  this fail-closed mismatch before rebuilding consent. The Rust binaries in
  the acceptance below are unchanged. The outer native outcome frame stays v5.

## Runtime evidence

Baseline ticket `j465038904`, e0a8ba21 artifacts, 10 GiB scope:
Host child PID 2662264 grew from approximately 100 MiB to 8,708,404 KiB RSS
in 196 seconds. Its parent was `mini serve --host …/minidregg-host`; the child
command `/proc/PARENT/fd/7 /proc/PARENT/fd/5 stdio` is the immutable Host launch
in `native/resource-client/src/transport.rs`. The scope journal records an
OOM kill at 13:21:14 UTC. Two-second samples precede that final allocation.
Evidence: `/tmp/kern-rss.0T8L11`, retained world `/tmp/kr.k4rkU6`.

Fixed ticket `j467925951`, all unchanged pipeline groups PASS:

| Row | Peak sampled process RSS (KiB) | Peak sampled scope bytes |
| --- | ---: | ---: |
| call | 124600 | 316108800 |
| send | 160400 | 391938048 |
| domain | 131284 | 324763648 |
| objectrecord | 114368 | 287154176 |

Each row has `MemoryMax = 10737418240` and `MemorySwapMax = 0`.
Evidence: `/srv/lanes/kern-oom/kern-fixed.l9tcwz`.
Host SHA256: `c9af2473566adeab754a65532b8b1f6fb80b9c9a42d1eb3e92f92b93c704c129`.
Consent SHA256: `7259320a358043e13c686bac0d6ae1ec995d7cc91c9ce5ad4ca4bb92c45b6b23`.
Receiver source SHA256: `1c60feb11148bc6220824afb146145348142648677dd20f88bc65c36ea373d3e`.

`RejectCodecChecks.lean` verifies the exact c6 refusal (128 bytes; charged
record 149 bytes), 2048-character strings/laws, 64 nested accounts/conflicts,
lists of long field names, a 4096-byte signature footprint, process errors,
typed roundtrips, and charged record reconstruction. Every case passed under
a 10 GiB scope. Byte counts of the long cases range from 4141 to 12343.

The old-encoder plant also went red: ticket `j469005990`, built with both
semantic roles in ticket `b468788548`, retained every named codec/semantic
proof and restored only the baseline encoding instances/Reject stream body.
Host PID 3105377 rose from 97,276 KiB RSS to 8,708,640 KiB at 197 seconds:
378,548 KiB at 68 s, 1,958,484 KiB at 84 s, 3,800,036 KiB at 103 s,
and 8,708,640 KiB at 197 s. The scope journal records an OOM kill at
14:28:45 UTC under the same 10 GiB cap; the last completed row step was
`c6-direct`, with `c6-no-grant`'s prepare-only plan completed and its actual
submission unfinished. Sampled scope peak was 9,098,670,080 bytes before
the failing allocation; this is not a claim that RSS exceeded the enforced cap.
Evidence: `/srv/lanes/kern-oom/kern-plant-run.flH54E/call`.
The restored Receiver hash exactly matches the four-row passing hash above.

## Reproduction

Only run builds/runtimes through the lane's request tools. The scripts require
Linux `/proc`, cgroup v2 and user systemd. Every evidence/artifact directory is
unique. The sampler stays outside the capped scope and preserves scratch
worlds, including unfinished steps. `KERN_RSS_CAP_GIB` accepts only 1–12
(default 10); sampling is every two seconds.

- `baseline-rss.sh TIP ROW` fetches the named published artifacts into a unique
  lane directory and runs the unchanged pipeline row.
- `fixed-rss.sh BASE_BIN HOST CONSENT [ROW ...]` runs the long codec checks,
  then the requested rows (default all four), with source-built semantic roles
  and published Rust roles.
- `plant-old-reject-codec.py apply` backs up the exact fixed source, restores
  baseline encoding instances, and changes only the Reject stream back to the
  old encoder. It keeps the named stream proofs, demonstrating that functional
  roundtrip laws alone cannot establish bounded execution. Build both semantic
  executables, then run `plant-rss.sh BASE_BIN PLANTED_HOST PLANTED_CONSENT`.
- `plant-old-reject-codec.py restore BACKUP` restores the exact fixed source.
  Run the exact-tree umbrella after restoring, before submission.
