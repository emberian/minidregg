# Historical prepared-R export (op18)

The source-matched native Host at `/tmp/minidregg-overnight-20260926/minidregg-host-postbbf`
(SHA-256 `919c3b7b64b7bff11d47a52993c7700b8028aa8596013cf396f41fd4f98c3038`)
served the operator-pinned A catalog at
`/tmp/mini-fn-catalog-r5-20260926/a/catalog-config.json`.
The exact served signed R was retained at
`/tmp/mini-fn-catalog-r5-20260926/r-signed-carrier.eml`.

Op16 returned a fresh prepared decision and an origin receipt in
`a/outbox-prepare-env/decision.json` (SHA-256
`a4bdd2274e197ee4710e2f7a882ec45b2fc6d342fe0f300a8418b880fc6ef67b`).
The ordinary signed Mini submit installed its tag-10 command as transaction
`31711439267763920516915384237772908260402196369118835143522621235802020288484`;
`a/outbox-submit/outcome.json` has SHA-256
`a79185ba432ae54b075f2f901d85f77e7d6d482fd7065440d814f05d526a7b62`.

The isolated gate-open qualification client (SHA-256
`d5b4e65c0beffcc174372250fb8a78f2755d42c57cbfee5f6bb9ae48abe606a3`)
called read-only `origin-outbox-export` into `a/outbox-export-qual`.
The public client built after removing the temporary gate (SHA-256
`4e4beea360b5c0144b49ac6e4a08132e1ab7646d08a8a532bcc9091ba9c0b982`)
repeated it into `a/outbox-export-public`. Both complete reply frames were
byte-identical: 399,015 bytes, SHA-256
`7fb4dfbf3171536e0b94afa52e91c4ce5b28fea09317937a4cd169799f94a604`.

The frame's opcode was 18 and its payload exactly matched `export.json`.
The decoded 198,808-byte carrier matched the retained signed R byte-for-byte
(SHA-256 `17185686c6a17212251d26bb4e68e91b7f131b20a7b08d36e795669dce2b468c`).
`carrierHex` re-encoded those exact bytes. Exported `messageId` and
`sourceIdentity` matched op16. All four `miniOrigin` receipt fields matched
op16, and all four `miniOutbox` receipt fields matched the confirmed tag-10
outcome. The selected transaction ID matched the submit outcome. The export
attempt directory had mode `0700`.

No fn POST occurred in this qualification. A full `origin-publish` journey is
separate. Focused Rust validation after the gate removal: `cargo fmt --check`,
27/27 `cargo nextest` tests, `cargo clippy --all-targets -- -D warnings`, and
`cargo build --locked` all passed for `native/resource-client` with
`CARGO_BUILD_JOBS=2`.
