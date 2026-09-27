# Verified SPK package identity inputs, 2026-09-27

The physical materializer now retains exact input fields for Mini's proposed bridge-only SPK identity descriptor. It still calls the pinned Bread `Spk::parse` once, then obtains the signing-key-derived App ID and signed archive members from that verified tree. This checkpoint does **not** compute Mini's cSHAKE descriptor root, decode bridge permissions, admit a lifecycle claim, or launch an app.

Source and dependency pins:

| File | SHA-256 |
| --- | --- |
| `native/spk-host/src/materialize.rs` | `1d5a293ef85a9cc11624f8b8b68f4be6fce2d117055d19a41c24e3361ecbeb24` |
| `native/spk-host/src/main.rs` | `591171bd1f5a34ee02b1eb45bfd907502ee335d9bc917d8c879ce539be8a05e8` |
| `native/spk-host/Cargo.lock` | `feecc17aa41d4bb3812084df9397ea4af1e203f65e3a71ae3d06109746166e41` |
| Signed GitWeb SPK | `2bbfe6d3c705dfb0696905ecd9c1d00d6554cc1224e63dc5545152af5f8f2caa` |

The new `InstalledPackage` fields hold raw SHA-256 bytes, exact raw length, SHA-256 of the signed `sandstorm-manifest` member, and an optional SHA-256 of the signed `sandstorm-http-bridge-config` member. The existing `manifest.app_id` remains derived from the verified package signing key. The bridge-only descriptor path must reject `None` for bridge config; it must never substitute a hash of empty bytes. Full ordered interface/role decoding and comparison to a source-owned Mini descriptor are pending.

Linux build and focused checks used a private hbox source copy under `/tmp/mini-spk-http-response-20260927/native`, byte-matched to the source hashes above, with two Cargo jobs and the same pinned Bread revision `5819115352bdfa43c5cbd329727d4f8d8a1b5be9`. The private locked build compiled `spk-host` SHA-256 `e505987f005bfd0f96eb0a4b2828fa8432eeb0d7db1b1bcf31fe2d0c7995b9e4`; focused materializer nextest **1/1 PASS**, strict all-target Clippy **PASS**, `git diff --check` **PASS**. The Cap'n Proto compiler and standard schemas were privately copied to hbox; no system package was installed.

The exact signed GitWeb SPK was copied to an owner-private hbox directory and parsed/materialized under transient user unit `mini-spk-identity-check-20260927-b.service` with `MemoryMax=1G`, `CPUQuota=200%`, `TasksMax=64`, `RuntimeMaxSec=120`. Unit result was `success`, `ExecMainStatus=0`, peak memory reported by `systemd-run --wait` as 179 MiB, and post-run `MainPID=0`, `ActiveState=inactive`, empty `ControlGroup`. No app command or network listener ran. The resulting image and root were operator-owned mode 0555. Extracted values were:

| Input | Observed value |
| --- | --- |
| Raw length | `14045864` bytes |
| Signer-derived App ID | `6va4cjamc21j0znf5h5rrgnv0rpyvh1vaxurkrgknefvj0x63ash` |
| Signed App version | `10` |
| Signed manifest SHA-256 | `3ef23992c6ee79e5b684cec632d4552c5b34889348ae63acaaedb42b9616024f` |
| Signed bridge config SHA-256 | `49d196f64ca2ce672a378581a8376ada53b27614bba522bbaec042237f0e70a2` |

The member hashes match the independent signed-package selection evidence. A first bounded unit, `mini-spk-identity-check-20260927.service`, refused after parsing because its newly created parent directory was mode 0775. That run reported `Result=exit-code`, status 1, and did not publish an image. The parent was corrected to 0700 before the distinct successful unit; no create action or app process was retried.
