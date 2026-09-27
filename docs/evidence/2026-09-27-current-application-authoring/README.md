# Current application/session authoring — source checkpoint

September 27, 2026. This records source checks, **not native acceptance**.

The loaded author derives application/session grants from the verifier-opened
authority and logical height, checks the supplied genesis against the pinned
seed/runtime, and requires the configured metered composite tariff. Legacy
authoring remains unchanged. The canonical intent still goes through ordinary
signed native admission; authoring is not authorization.

Frozen Lean source SHA-256:

| File | SHA-256 |
| --- | --- |
| Kernel/ApplicationGrainBirth.lean | 386a14939fe74305d935662445b9bf998f95e7609289b957cab30198323136a9 |
| Kernel/ApplicationGrainSessionBirth.lean | 8cc7a19c63b041c13164715c22e8ebd9bd94a10553c110b7ae043d526cf0053c |
| Host/Json.lean | 166506a6a6d53e34a895e6fb91c7cf54250ec03aea46a0d6acab185a70704773 |
| Host/ApplicationCurrentBirthAuthoring.lean | 7c7fd3e5451e9bfd090560666deaf8f03006f320386e3b368b7d6fa7631090b4 |

The owning lane reports serialized `LEAN_NUM_THREADS=2 lake env lean -o`
checks of all four modules passed in independent `/tmp/mini-currentbirth-check`.
Logs there are `ApplicationGrainBirth.laws.log`,
`ApplicationGrainSessionBirth.laws.log`, `Json.current.log`, and
`ApplicationCurrentBirthAuthoring.tariff.log`. Those temporary build artifacts
are not a portable full-build qualification. Root reviewed the complete source
diff, including the explicit configured-tariff check.

The Rust client offers `current-application-intent` and
`current-session-intent` through pinned socket operations 30/31. It retains
the source/config and full reply before releasing `intent.bin`; refusal retains
the reply without an intent. Submission remains a separate
`mini submit --intent-kind binary` operation.

Frozen client SHA-256:

| File | SHA-256 |
| --- | --- |
| native/resource-client/src/current_birth.rs | 202a73f773363c813f0ca943ee61b491a5600c326c6e1a55fd6cc4781049c079 |
| native/resource-client/src/main.rs | 1b7c817f2ec56cce36af25ff210942e9f00a56f85d1089b17e8560e9315e91d9 |
| native/resource-client/src/transport.rs | ae59b773669c93031125a3716f38600fff6537c5225c5e8dc683e68e5064f533 |

The client lane reports 3/3 focused Nextest tests passed (run `b273d43d`),
strict all-target Clippy and formatting passed. The socket test uses a fake
Host peer, so it establishes custody/framing behavior, not Lean integration.

```sh
CARGO_BUILD_JOBS=2 cargo nextest run --manifest-path native/resource-client/Cargo.toml -E 'test(/current_birth/) | test(/current_birth_authoring/)'
```

The linked Host routes, real metered current-height birth, stale-draft refusal,
and retained receipt/restart journey remain to be exercised. An issuer-epoch
rotation route was not found in the current native signed receiver inventory;
post-rotation native behavior is untested. A current-height test must not be
reported as an issuer-rotation test.
