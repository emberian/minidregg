# 7d03d5e corrected namespace Mini client

The immutable Linux client is `/home/ember/build/minidregg-7d03d5e-client-evidence/bin/mini-7d03d5e` (SHA-256 `5bca4550a0a5b180ed5c78dc49bcf9f650a94afe2488caac1297911ca5c69974`). It was built from exact commit `7d03d5e00730ee11f283d8e851619cdd65709265` as an independent Git archive (SHA-256 `49949cf2447e7e3c1a9e00622963049aa2dc370e559af41c5b98ec291f534fb2`). The committed transport source was SHA-256 `101e6d71713fcb5253941244a2b544d94e20c6d244d92aaaa25d5e920150ce09`; unrelated live transport work was excluded.

The bounded release build with `CARGO_BUILD_JOBS=2` and `--locked` passed. `cargo nextest run -p minidregg-resource-client` passed 74/74 tests. The [source and artifact manifest](manifest.txt) has SHA-256 `7d4752894168080ca5d9a4d1bbba3f326c9d4cc883aa0eefaead8850d5ad7451`; [build](build.log) and [test](nextest.log) logs are retained.

The separately certified `bf04c29` Host (SHA-256 `cf931aae46102755a97920feed13afa36c83ef4d1bfabd2fb17dee1c8bbfa943`) remains the r3 registration fixture's Host. This record qualifies the corrected client build and focused tests; no native fixture was run in this build lane.
