# Exact readback reuse contract (design, not an enabled receiving path)

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

The exact-readback witness must be constructed only inside the receiver's
post-CAS equal-bytes branch and returned as a distinct typed result. The current
`Result.confirmed kind snapshot` loses the branch provenance: it also denotes
a replayed prior transaction or a changed readback with a concurrent append.
Those cases must retain the current canonical load and semantic suffix
verification, original historical receipt lookup, contention, or uncertainty.
A missing/error readback after CAS remains uncertain. Rewritten prefixes and
rollback remain refusal. A lost CAS response followed by exact candidate
readback may keep the existing `recoveredAfterUncertainResponse` confirmation.

The first implementation target is the persistent session, which retains the
old `Verified` object and a pinned verifier for its lifetime. The one-shot
entrypoint currently discards `Verified` in `openExisting`, so its full semantic
reopen remains the baseline until it is given an equally strong verifier and
old-tip contract. The optimization changes the number of verifier launches;
therefore it does **not** claim unconditional IO observational equivalence if a
second verifier launch would have failed. Both paths require the original
admission, full physical readback, and exact source-derived receipt, conditional
on stable pinned verifier semantics.

Measurement must compare the persistent-session path on private accepted-one
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
