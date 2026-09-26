# Exact readback reuse contract (persistent receiving path)

The persistent native session already holds `NativeHostReplay.Verified config oldTarget`.
`Session.refresh` rereads the complete physical image before each request and reuses this
verified object only when those bytes are identical. Host startup pins the signature
helper to a private executable snapshot for the session lifetime. These are operational
preconditions: the Lean type `Config` alone cannot prove that the OS kept the helper
executable immutable or available.

For a newly admitted invocation, the fast confirmation must carry all of the
following from the **same** receiving call:

1. The old `Verified` object and its exact `Opened` tip, after session refresh.
2. The controller's `PreparedInvocation`, `SignedCommand`, `PhysicalShape`, and
   `AcceptedInvocation`, constructing `NativeAdmission.invoke` and its exact
   canonical `DataIntent`. No caller-provided Boolean or decoded candidate can
   replace this object.
3. `DurableReceiver.prepare`'s `Ready` for that old image, restored snapshot, and
   admitted intent. The sole CAS candidate is the canonical encoding of
   `oldTarget.image.append intent`.
4. The complete bytes returned by a physical post-CAS read, with proved equality
   to that exact candidate. `ByteArray` comparison is only an efficient way to
   discharge equality of the full byte lists; a digest/height/mtime is insufficient.
5. `validateLoaded config` of the prepared successor, and a complete canonical
   intent-record comparison. These establish one `AdmittedStep` at the old height.

The pure extension composes the old admitted replay and this one step. Its new
receipt uses the **original appended prefix**: transaction ID, event ID, old
accepted count plus one, and `imageBoundary config (oldTarget.image.append intent)`.
The receipt is not derived from a potentially later current tip. Its verified
target is the complete physical readback, not the proposed image alone.

The exact-readback witness is constructed only inside the receiver's
post-CAS equal-bytes branch and returned as a distinct typed result. The legacy
`Result.confirmed kind snapshot` loses the branch provenance: it also denotes
a replayed prior transaction or a changed readback with a concurrent append.
Those cases must retain the current canonical load and semantic suffix
verification, original historical receipt lookup, contention, or uncertainty.
A missing/error readback after CAS remains uncertain. Rewritten prefixes and
rollback remain refusal. A lost CAS response followed by exact candidate
readback may keep the existing `recoveredAfterUncertainResponse` confirmation.

The implemented fast path is the persistent session, which retains the
old `Verified` object and a pinned verifier for its lifetime. The one-shot
entrypoint currently discards `Verified` in `openExisting`, so its full semantic
reopen remains the baseline until it is given an equally strong verifier and
old-tip contract. The optimization changes the number of verifier launches;
therefore it does **not** claim unconditional IO observational equivalence if a
second verifier launch would have failed. Both paths require the original
admission, full physical readback, and exact source-derived receipt, conditional
on stable pinned verifier semantics.

Measurement compares the persistent-session path on private accepted-one
Store copies with the same signed call and physical bytes. The previous
189.68-second Linux large-call measurement used a one-shot submit, so it is
not a baseline for this proposed session optimization.

The matched before measurement was made on Persvati with certified combined
Linux host SHA-256 `4bb72e1e984de413ee0065d7d229dbe0217bf980b4563ba26dc85ee38ed59c65`.
A private accepted-one SQLite copy had SHA-256
`8eff8dd1c0a424ff75456da1adcc22c06774eab29238af001916b0a398404893`;
the retained 734,222-byte call had SHA-256
`59b6a3ac9a12a8552547833e1922ac7d3d9086ab1c26b404e10af3a9d60b952f`.
The host ran as one persistent stdio session through the local socket client;
`describe` warmed/validated that session before opcode-2 `retry` of the exact
call. The retry elapsed in **172.92 seconds**. It returned installed,
accepted count two, with 132-byte outcome SHA-256
`caf4009a43d3cd6f6773f971574a0b4c5597e716f4d04640b1f6b3c54d7c42ee`
and final SQLite SHA-256
`0066f07fcfd6d92fd95717c809fbab173b74d45be604841bb8fc3899884d82a5`.
Both bytes match the retained source run and prior one-shot comparisons.
The session client used essentially no CPU; the host accumulated about 2:57
CPU and held about 1.30 GiB RSS near completion. The fixture is private at
`/tmp/minidregg-large-b-profile-20260926/session-baseline-v1`; its service
process was stopped after the measurement. This is one run under shared host
load, not a general latency bound.

The exact-session Linux host SHA-256
`5c6bf412b2e77675874dc820ac6bd2f6d0b20c3f6752e5e4728228649d63daab`
was built from the committed detailed receiver, typed replay extension, and
persistent Host routing with the pre-UInt64 cSHAKE core. On a fresh copy of the
same accepted-one SQLite image and the same retained signed call, the warmed
persistent submit took **96.55 seconds** of client wall time. Its retained
132-byte Outcome is byte-identical (`caf4009a…`) to the before run, and its
post-submit SQLite image is byte-identical (`0066f07f…`). The case evidence is
`/tmp/minidregg-large-b-profile-20260926/session-exact-v2/` on Persvati;
`input-sha256.txt`, `output-sha256.txt`, `retry.time`, and the retained JSON
record the full identities. These are two single runs under shared load, so
the measured reduction is specific to this call and environment.
The bounded copies here are `exact-session-linux-before.time`,
`exact-session-linux-retry.time`, `exact-session-linux-input-sha256.txt`, and
`exact-session-linux-output-sha256.txt`. The Mac and Linux build manifests and
five changed-source SHA lists are archived alongside them; the changed-source
lists match byte-for-byte across platforms.

The certified Mac host SHA-256
`2ae1f166685e45e4fd1f3aeda49236af2a14e6719602bca89a7fe24d2fd406c0`
passed [`exact-readback-session.sh`](../../../scripts/overnight-tests/exact-readback-session.sh)
(source SHA-256 `8d9728e4e8673a593a334af7362928a1c09c5c42d5ea37b694f818b9a91e9a48`)
on four separate private accepted-one Stores. Normal CAS returned `installed`;
a successfully installed CAS with its response lost returned
`recoveredAfterUncertainResponse`; a failed post-CAS readback returned typed
`uncertain` and a later exact lookup returned the original receipt. When the
wrapper appended an independently accepted next event between CAS and
readback, the response kept the original count-two receipt while the physical
Store matched the valid count-three image byte-for-byte. The complete four
receipt fields were compared with the retained original, and every case made
an exact physical image comparison. Evidence remains at
`/tmp/minidregg-exact-readback-physical-suffix-pass-20260926/`; this directory's
bounded physical SHA list and typed first outcomes are copied here as
`exact-session-physical-sha256.txt` and
`exact-session-physical-results.jsonl`. The first suffix trial used test script
SHA-256 `d12017bd…` and exited because its assertion incorrectly expected
`recoveredAfterUncertainResponse` for an ordinary successful CAS with a later
concurrent append. Its retained result was actually `installed` with the
correct original receipt, and the physical image matched the valid suffix.
The corrected script SHA above passed all four cases on fresh Stores; the
initial trial is not counted as a green gate.

The same Mac host passed the existing
[`replay-poison.sh`](../../../scripts/overnight-tests/replay-poison.sh) on a
fresh private native fixture: rollback to an earlier valid accepted image and
a valid same-height different branch both closed the live session without
accepting a later frame. Logs at
`/tmp/minidregg-exact-session-poison-20260926/rollback.log` and
`same-height-fork.log` have SHA-256 prefixes `2299a1c4` and `7c8e793e`.
Bounded copies of both logs are archived here as `exact-session-rollback.log`
and `exact-session-same-height-fork.log`.
These physical gates complement the pure typed extension and the scripted
receiver probe; they do not turn the public `ExactReadback` structure into an
IO authentication primitive. Production constructs it only after the actual
post-CAS full-byte read.
