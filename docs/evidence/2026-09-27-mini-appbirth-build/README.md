# Application-birth native build (2026-09-27 UTC)

The first Mac fixture uses a private source image from committed `2e60a9c`
plus the proof-only `Kernel/GrainResourceBirthTransaction.lean` correction in
`bfb6b8b`. The source image's Pred, Theory, Compiler, Kernel, Host, and Selvage
trees match the `2e60a9c` Git archive except for that one file, SHA-256
`4357ac48894c89937870753607d7f2d7be34657fcfbf13e921bef1a376e249eb`.
The builder manifest's `git_head=2aeaf643` is Git metadata inherited from the
private APFS clone; it is **not** the source revision used for this build. To
qualify the compiled closure, I compared the bytes of each of the 187 files
in the build's source manifest with `git show 2e60a9c:<path>`. All 187 were
present; 186 matched. The sole difference was
`Kernel/GrainResourceBirthTransaction.lean`, whose source SHA-256 matches
`git show bfb6b8b:Kernel/GrainResourceBirthTransaction.lean`. The private
`lakefile.toml`, `lean-toolchain`, and `scripts/build-native-host.sh` also match
`2e60a9c` byte-for-byte; no `lakefile.lean` exists in that image. The
[recorded source hashes](mac-host-source-sha256.txt), rather than the clone's
Git HEAD, identify the code compiled into the Host.
The initial full gate stopped at its `effectsExact` proof after the canonical
request encoding optimization. The correction rewrites through the general
`requestFor_eq_reference` theorem; a narrow check passed before the final run.

The final Host build compiled all 187 source modules and linked 3,120 response
objects in 1,069 seconds. Its source manifest SHA-256 is
`9de1d035d95a44b76a9ba28431cbdf760d48d1964df9ffc757898f080cbc4cc3`;
all recorded output artifact hashes passed
[`shasum -a 256 -c`](mac-host-artifact-verify.log) verification. The no-argument
`usage_exit=1` is expected. The immutable Mac Host is
`/tmp/minidregg-overnight-20260926/minidregg-host-appbirth-2e60a9c-bfb6`,
SHA-256 `6635b3560280c9d9af544feb3fc5e49a446e498082520bfc24fb78241c50267a`.
See the [manifest](mac-host-manifest.txt), [source hashes](mac-host-source-sha256.txt),
[artifact hashes](mac-host-artifact-sha256.txt), and [build log](mac-host-build.log).

The three helper crates were cut from an exact `2e60a9c` Git archive of
`native/resource-client`, `native/hyperdocument-link-sqlite-store`,
`native/credential-signature-verifier`, and the SQLite test fixture directory.
Archive SHA-256:
`93355ce909910218e438bbcf5679f916641ebdd595ca5be2dabd364e8aedfdc6`.
The [source manifest](source-sha256.txt) covers 28 committed files, SHA-256
`a8171e1133f2a74c95852a26fcb9f8c88be5bba84c5fb6c0e1cb37a5e3dcb02f`.
Each crate used its own committed `Cargo.lock`, a private Cargo target, a
release build with two jobs, and focused `cargo nextest`.

The immutable Mac helpers are:

| Program | Path | SHA-256 | Tests |
| --- | --- | --- | --- |
| Mini client | `/tmp/minidregg-appbirth-2e60a9c-helpers/bin/mini` | `5139e1e1d86e508ac5b318a85e1d87db5d24a0a8f13123ed62edfb4adab1fe5e` | 45/45 |
| SQLite store | `/tmp/minidregg-appbirth-2e60a9c-helpers/bin/minidregg-link-sqlite-store` | `7420e41d1cc76ab3d98d4699e392f799e0d3c587a24c1a9c3f3c5b13d480b82a` | 10/10 |
| Credential verifier | `/tmp/minidregg-appbirth-2e60a9c-helpers/bin/minidregg-credential-signature-verifier` | `4f5a9095aa8401e538ac962a37de715b317e443dd35846317e2f068ae9829836` | 10/10 |

The adjacent build and test logs retain actual verdicts. The initial SQLite
test invocation could not find its committed fixture because the first
archive omitted that directory; the complete archive above included it, and
the final 10/10 SQLite test pass used that exact source image. No mutable
`target/debug` helper was used. These binaries have not been installed over
live services. The fresh isolated two-participant application-birth fixture
is a separate runtime verdict.
