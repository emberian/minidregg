# Event20 operator custody checkpoint

`native/resource-client/src/fn_namespace.rs` is a private client for the
source-authored fn consumer namespace route. It obtains op42's zero-position
plan from an owner-private operator socket, retains and inspects the exact
canonical plan, and signs only the Host-selected credential header with an
owner-private gateway key. The private approval must name the exact plan hash,
identity, fn scope, configured gateway, roots, signing-key metadata, and signer
public key. Op43 receives a raw 64-byte signature; Lean constructs the
credential envelope and rechecks the current Mini image before returning the
exact event20 ingress.

The client creates a durable op40 marker **before** sending the ingress. After
an uncertain or lost reply, reentry does not send op40 again; it uses read-only
op41 to select the original four-field Mini receipt. A separate keyless lookup
route can repeat that observation. An absent lookup is held for operator
review, never treated as permission to resubmit. The retained assembly frame,
ingress, submit frame, and markers are checked against the same pinned Host,
config, socket, plan, and signature.

Source SHA-256 at this checkpoint:

| Source | SHA-256 |
| --- | --- |
| `native/resource-client/src/fn_namespace.rs` | `63b530e868bd1c8a6dcb1e7784bcc51208f2d28f690097a9f4cdb048b8a787be` |
| `native/resource-client/src/main.rs` | `9169d22616a19331fd6ab3f7f7273adf2d4f04d38d07f56293a69ad157e29e7a` |
| `native/resource-client/src/transport.rs` | `101e6d71713fcb5253941244a2b544d94e20c6d244d92aaaa25d5e920150ce09` |

`cargo nextest run --manifest-path native/resource-client/Cargo.toml` passed
74/74 after the root comparison correction. The focused lost-reply test uses a private Unix socket: it observes
op43, one op40 whose reply is dropped after the simulated install, then op41
on both initial recovery and same-state reentry (`[43, 40, 41, 41]`). Strict
all-target Clippy and `cargo fmt --check` passed.

This is a **client state-machine** result. The socket test does not prove
native event20 admission or actual fn transport. The qualified Host image and
fresh private recipient fixture must still pass the real registration, ordered
empty-page progress, selected publication, recipient admission, and ACK gates.
The old qualified Host image for commit `24ecf8a` expects an envelope at op43;
this client requires the later source-qualified raw-signature op43 image.

The first real r3 op42 read-only plan was accepted under the qualified
`bf04c29` Host. Its retained `plan.bin` is 730 bytes, SHA-256
`844a6f0a50234439036f953903431bc5b293ff1b2ed52deb32d138db4a55d5ce`.
The plan's durable outer `expectedAuthorityRoot` is `80525600185008188143584759140158074146523251558178312337889358419141795823022`;
its credential header's logical `signingAuthorityRoot` is
`13458004229115573951517042894475137027092070069746651446439353323415333526430`.
The original client incorrectly required these distinct roots to be equal.
The corrected custody check keeps both values independently pinned in the
private approval and rejects a changed signing root. No signature, op43, or
op40 was sent during this diagnostic.

The earlier `f2222d6` custody source SHA was `45ca1f36f10ec063ba09b46882967fabf9213e4cf792827f5b7cd3b5e41ea1cc`;
its 74/74 test used transport SHA `bf67094de08d62b650cd29e44afa5949807b99e5e394127116055e2c2321b80a`.
The 74/74 retest after this correction used the current committed transport
SHA shown in the table.
