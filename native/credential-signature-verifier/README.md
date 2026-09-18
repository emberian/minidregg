# Credential signature verifier

This binary delegates Ed25519 verification to the exact pinned
`ed25519-dalek = 2.2.0` implementation of `VerifyingKey::verify_strict`.
`Cargo.lock` records the transitive versions and registry checksums. Neither
the legacy compatibility feature nor batch/hazmat verification is enabled.

```text
minidregg-credential-signature-verifier verify <public-key-file> <frame-file> <signature-file>
```

The public key is exactly 32 raw bytes and the signature exactly 64 raw bytes.
The frame is an opaque byte string, including an empty or non-UTF-8 string.
This is plain Ed25519 over those exact bytes: no frame parsing, normalization,
additional hash, context, domain prefix, key lookup, or semantic decision is
performed here. Lean must produce the canonical domain-separated frame and
select the key from the committed authority state.

| Result | Exit | Exact stdout | Stderr |
| --- | --- | --- | --- |
| Strict verification succeeds | 0 | `verified\n` | empty |
| Strict verification refuses | 0 | `invalid\n` | empty |
| Input/read/point-decoding error | 1 | empty | diagnostic |
| Wrong operation or argument count | 2 | empty | usage |

Invalid verification includes a different message/key/signature, weak public
keys, small-order signature points, malformed signature point encodings, and
noncanonical scalars, as classified by the pinned library. Public-key point
decoding failures and wrong key/signature lengths are input errors. There is
no separate custom point or scalar parser. Output-write failures also return
nonzero; a pipe may already have received a partial response. The caller must
accept only **exit 0, exact `verified\n`, and empty stderr**. Every other or
ambiguous process result refuses authentication.

The native trust boundary includes this adapter, the pinned library and its
dependencies, the Rust build/runtime, the executable selected by the caller,
and the host process/filesystem carrying the exact inputs and result. The
frame is read into memory; the caller owns its size and private temporary
files. Passing this check establishes a library verification result, not
authorization, revocation freshness, replay prevention, or a Lean proof of
Ed25519. Those obligations stay with the credential/authority receiving path.

For a bounded build and actual CLI checks, from this directory:

```sh
CARGO_BUILD_JOBS=2 cargo build --locked --release --bin minidregg-credential-signature-verifier --example sign-probe
CARGO_BUILD_JOBS=2 cargo nextest run --locked --release --test protocol -E 'test(protocol_)' --test-threads 2
```

The CLI checks include [RFC 8032 section 7.1](https://www.rfc-editor.org/rfc/rfc8032.txt)
vectors, exact binary frames, modified inputs, malformed encodings, I/O and
argument errors, and a weak-key forgery accepted by the library's ordinary
verifier but refused by this binary's strict verifier.

`examples/sign-probe.rs` is a test-only signing helper:

```text
sign-probe <seed-byte 0..255> <frame-file> <public-key-file> <signature-file>
```

It uses `SigningKey::from_bytes(&[seed_byte; 32])`, signs the exact supplied
frame, writes the public key and signature files, and announces the public
test seed on stderr. Every such key is publicly reproducible. This helper
accepts no secret-key file and belongs only in probes; the production binary
has no signing operation or credential/key database.
