# Offline signed SPK launch qualification source checkpoint

The staged `spk-host qualify-launch PRIVATE-CONFIG.json` path parses one
signature-verified Bread SPK, projects its signed create actions and continue
command in order (including duplicate environment names), and asks the pinned
Mini Host to author and inspect the v1 package descriptor and v2 launch
descriptor. It compares the source-inspected command bytes, package canonical
bytes, and roots with the verified parse before returning a result. The command
requires an owner-private config and attempt directory, but no Store or socket.
It does not install, launch, or authorize an application.

The strict private config fields are `protocol` =
`mini-spk-launch-qualification-v1`, `sourceSpk`, `miniHost`,
`miniHostSha256`, `miniConfig`, `miniConfigSha256`, and `attemptDir`.
The strict result protocol is `mini-spk-launch-qualified-v2` with
`rawSha256`, `packageRoot`, `launchRoot`, `launchCanonicalSha256`,
`createCount` (decimal string), `createDigests`, and `continueDigest`.
It retains `package-v1/` source, canonical and inspection files plus
`launch-source.json`, `launch-descriptor.bin`, `launch-inspection.json`, and
`qualification.json`. Direct Host author/inspect has a 600-second deadline,
kill/wait cleanup, private output, and input/Host/config pin rechecks.

Scoped source hashes at this check:

| Path | SHA-256 |
|---|---|
| `native/spk-host/src/launch_descriptor_native.rs` | `83c7466ce0dee0acd7dfc236dac3bb7525f97342d060ef758a5fd95e33d4a0cd` |
| `native/spk-host/src/descriptor_native.rs` | `7b604fea6287303261dd6e77382a6c92912ac839bfe4f58d17c9c239f9c0270e` |
| `native/spk-host/src/lib.rs` (combined with separately owned `volume_custody` registration) | `82b03a9f5d59b555d23444f12a55f7533654b5230b195c1535bf9d6ebce106e9` |
| `native/spk-host/src/main.rs` (combined with separately owned `resident-run` hunk) | `6d5360e5a413adc935a769ea93999cf5f9148a873a6f80bd1ee6988becec4ca4` |

In an isolated hbox snapshot with two Cargo jobs and a 4 GiB memory limit,
focused `cargo nextest run --locked -E 'test(launch_descriptor_native::tests)'`
passed 4/4, including duplicate command ordering, offline no-socket execution,
pin/input drift refusal, and bounded child timeout. The retained log is
`/tank/dregg-build/spk-launch-client-session-20260927/nextest-final.log`
(SHA-256 `d38c6db876eb8071859effdfc2cea2c5a5c69fd68eae97e68b76683c84874bbc`).
Strict `cargo clippy --locked --all-targets -- -D warnings` passed; log
`/tank/dregg-build/spk-launch-client-session-20260927/clippy-final.log`
(SHA-256 `943e485c9717b126332cfcafc93676f33e0c1cfd8d0fe3e5c53e0689603bae58`).
The Linux snapshot included the separately owned volume-custody source.

These are Rust boundary checks. The Lean v2 author/inspect helper has not yet
been source-qualified and linked into the pinned Mini Host, so this checkpoint
does **not** claim a native GitWeb v2 descriptor result or a pre-Store
integrated gate. No v1 canonical output was changed by the typed source-tool
adapter.
