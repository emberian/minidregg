# f461 signed query in a persistent Host session

This read-only measurement used a private copy of the quiet r2 post-reserve Store on hbox. The copied `forward-link.sqlite3` was 688,128 bytes, SHA-256 `4c3685f51196665e95605462e5779b46bc2fff271e2b82609e2021e6f239dbb5`. The owner-retained 583-byte signed observation was SHA-256 `c0a35270625856ca8f62177175bab7926bdb719805500f776559d92458fb6714`; no signing key was read. The copied config changed only `storageRoot` to the private Store and was SHA-256 `77fec6ea08ccd97d012dfac030273823223284a68746de6c7a76dd7de85257d8` (original config `1157c0aa8b8047b6b1e5e3b6d76b4cd99b9c99f094248d07947e6867fe568f94`). The qualified f461 Host ELF was SHA-256 `3bbdc8474cca00a3a080f9120acba39ee551ca47d9506573dc37115dc26df55b`; the exact d752df7 Mini ELF was SHA-256 `08a1605a804cab92fd262bf82e951e9c2b3c1573d2ba8a593ff97888962d7acf`.

The private diagnostic client called the committed d752df7 `transport::invoke_pinned` implementation (`transport.rs` SHA-256 `c86163896fa1f99a7330d46212ab3fcc8be849554abd95fec7842f3b066d652e`) with opcode 5 and the **same signed bytes** on each request. That transport writes a length-framed v2 socket envelope containing the complete pinned config, expected Host SHA-256, and op 5 payload. The persistent `mini serve` process forwarded it to one Host `stdio` child. No new public network listener was created. The diagnostic binary SHA-256 was `df7a01f77f4fe066c04f3da3269fefafe9f483cc9dfbaf63dc043be0e2e08fdd`.

The small diagnostic source is retained as `probe-main.rs`, `probe-Cargo.toml`, and `probe-Cargo.lock`. To reconstruct it in a scratch crate, rename those files to `src/main.rs`, `Cargo.toml`, and `Cargo.lock`, copy `native/resource-client/src/transport.rs` from commit `d752df7` to `src/transport.rs`, then run `cargo build --release --offline --locked`. Its five arguments are the private Unix socket, copied config, pinned Host SHA-256, retained signed observation, and a new output path. It calls the existing transport implementation rather than recreating its envelope format.

The fresh service ran as user unit `mini-warm-query-f461-r3.service` with `CPUQuota=200%`, `MemoryMax=4G`, `CPUAccounting=yes`, and `RuntimeMaxSec=1200`. Socket readiness took **0.314 seconds**; this only measures listener readiness, before the first successful query. `/usr/bin/time -v` measured each query's wall time. The service's `CPUUsageNSec` immediately before and after each query measured combined Mini and Host CPU; subtraction excludes diagnostic-client CPU.

| Same signed query | Wall | Service CPU delta | View SHA-256 |
| --- | ---: | ---: | --- |
| First successful request | 86.62 s | 86.661 s | `dac7842a355077c58af33704f2fcf22bc70a20fb9a4de5ba3c3bf1c2a1f1708d` |
| Repeat 1, same Host child | 0.73 s | 0.736 s | same |
| Repeat 2, same Host child | 0.96 s | 0.966 s | same |

The view bytes match the retained cold result (101 bytes, SHA-256 `dac7842a355077c58af33704f2fcf22bc70a20fb9a4de5ba3c3bf1c2a1f1708d`). The copied Store hash remained `4c3685f5…` after all three queries. The service was stopped, its private socket removed, and the terminal unit state was inactive/success. Timing and CPU snapshots are adjacent; `identity.sha256` retains the output and Store hashes. A prior rejected `mini host-command query` never reached the Host; a subsequent stale-socket readiness attempt likewise sent no query. The reported run is the clean r3 unit with three successful exact requests.

This result measures the existing f461 persistent-session path on one retained post-reserve image. It does not claim that every query or a changed Store has subsecond latency; the first request still pays verification/startup cost.
