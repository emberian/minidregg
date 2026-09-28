# Native participant key enrollment probe — 2026-09-28

This is a private, disposable SQLite Store probe of the Mini source receiver.
It is not a deployed service, a client onboarding run, or Gate A. The test uses
public deterministic Ed25519 fixture seeds 7, 8 and 9; no private user key or
Store is retained.

From the Mini repository root:

```sh
lake env lean --run scripts/probe-participant-key-enrollment.lean \
  native/credential-signature-verifier/target/debug/minidregg-credential-signature-verifier \
  native/credential-signature-verifier/target/debug/examples/sign-probe \
  native/hyperdocument-link-sqlite-store/target/release/minidregg-link-sqlite-store
```

The captured [probe.log](probe.log) reports PASS. The probe source builds
genesis with only sponsor subject 7, admits subject 8 through the real factory
control capability and current compiled factory law, and checks an independent
signature by subject 8 over the exact source-authored possession frame. It
checks that an authenticated factory observation releases the exact two-signature
plan on the same opened image, while a mismatched sponsor is refused. It
checks canonical installed authority equality, current key selection, and
that no grant was minted. An explicit all-epochs subject scan also rejects an
orphaned prior subject key if one is present; this is a defensive guard, not a
claimed reachable state in the current runtime. Existing subject, duplicate key ID, stale authority
root and wrong proof-of-possession signer refuse. A second genesis with a
current factory law denying enrollment refuses despite valid sponsor and new
key signatures. The native receiver installs one durable event; exact repeat
replays, and a changed ingress with the same operation identity conflicts.
`NativeHost.openExisting` re-admits the event from the retained original
ingress. The new signer then verifies on that replayed state, while a new
enrollment attempt by it refuses without a delegated control capability.

Source SHA-256 at the run:

| File | SHA-256 |
| --- | --- |
| `Kernel/ParticipantKeyEnrollment.lean` | `a9fb944de91ef3270ff0266383542a214926e94bc65c87ca3c3c9a39b917a4c1` |
| `Kernel/ParticipantKeyEnrollmentReceiver.lean` | `905ff49c93d7e9df65689332efa84e1d4ad27ea53b4ee4f50586d2bc62249bf2` |
| `Kernel/NativeHostReplay.lean` | `ed0f41efa6750b204ce477e116e4a9276ddee350a44dbd572a4798d8e09b8fcc` |
| `Kernel/NativeHost.lean` | `11794e2fd2cb72a19d80e3f3a7790f6f955ad5969e95dad55e069bfc39922e08` |
| `scripts/probe-participant-key-enrollment.lean` | `c2c3411e382d948dd0c5fac7fbf4a830dbd37c493cddc405623bfae2d7f4ca07` |

Execution binary SHA-256:

| Binary | SHA-256 |
| --- | --- |
| `minidregg-credential-signature-verifier` (debug) | `dd5273f30a999dc7594018dd57605aebf2f9f15c43010f31e8674d28f14aafd9` |
| `sign-probe` (debug) | `020f31e6124d4fcdff40fd50bef0c2697d8d92769127dd14225f7b8d8b8c528c` |
| `minidregg-link-sqlite-store` (release) | `6c716da59969563cb9ddbe71a25370bbe9db8de13670fabaac5abe8a2ed42a03` |

The probe does not exercise a post-enrollment resource grant or an authorized
new-subject observation. Those need the ordinary delegation path and the
integrated native client. The native verifier and Store binaries, Lean runtime,
process I/O and cryptographic custody remain execution assumptions, as in the
existing native host.
