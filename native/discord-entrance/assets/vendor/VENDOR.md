# Vendored browser assets of the door

The door page loads no third-party script at runtime (the box has no egress). These files are
served by `mini-door` under `/join/assets/`, pinned by version and sha256; update a file and this
table together. `mini-door`'s `vendored_assets_match_their_pins` test re-checks the column.

| file | source | version | tarball sha1 (npm) | file sha256 |
|---|---|---|---|---|
| `wallet.js` | ember's sol-misc `docs/passwap/wallet.js`, reduced to Wallet Standard and bytes in/out (no SDK Transaction object; legacy window injections dropped), `list(sol, { chain })` asks for the quote's cluster (audit INTEGRITY 7) | 2026-10-27 | — | `4d5ec5e3e84c58377e9e72ee2eab0390e89b4d7afc32199b99952e7016a2ca68` |
| `../solpay.js` | the door's own one-shape serializer (replaces `@solana/web3.js`); equality with web3.js 1.99.0 is `tests/pay-serializer.test.mjs` | 2026-10-27 | — | `9f2c701a0eebc9986524e62e456c3bdc97f9f388a418b916734470378263b91c` |

No third-party SDK is served: `@solana/web3.js` 1.99.0 (484,077 bytes, sha256 `ecfdbe556175b8e7598c7b4189c5abd5b37858671bbb115799fa2b7c0b3715f4`) was replaced by `../solpay.js`; its output survives as the golden vectors in `tests/support/pay-golden.json`. The adapter is ember's own.
