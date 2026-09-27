# Operator-pinned fn bridge

`fn_bridge.sh` is the historical two-store test transport. It intentionally
reads `FN_B3_IMAGE` and has fault-injection hooks. A persistent Mini service
using a pin to that file inherits its environment; a restarted service without
`FN_B3_IMAGE` cannot inspect a retained fn cursor or ACK it.

`render-operator-bridge.sh` creates a standalone helper in a **new file under
an owner-private mode-0700 directory**. Its arguments pin, in order, the
qualified hbox `fn-host` path, SHA-256 of the image, `.core`, packaged SBCL
runtime, OpenSSL prefix, OpenSSL executable, `libcrypto.so.3`, and
`libssl.so.3`. The renderer checks those remote bytes and the reviewed
`fn_bridge.sh` source SHA before it writes anything. It transforms that exact
source into the helper: the image and OpenSSL paths become literals, and the
two lost-reply fault branches are removed. The helper has no `FN_B3_IMAGE` or
`FN_E1E2_DROP_*` lookup and never calls the mutable checkout bridge. Every
invocation checks the same remote hashes before the fn command. Rendering
supports Darwin and Linux operator hosts; the generated transport still
targets the explicitly pinned hbox image. It fixes its local command search
path to `/usr/bin:/bin` for the operating system's SSH/SCP tools.

For the qualified `bbf52159` hbox image used in the workroom exchange:

```sh
scripts/fn-e1e2/render-operator-bridge.sh \
  /PRIVATE-0700-DIR/fn-operator.sh \
  /tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d/fn-host \
  432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505 \
  6e569af117ba4afcf52bfd74f2a40ac222ead7701bb0b84bac799c53521bfe9e \
  b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5 \
  /tank/fn/toolchains/openssl-3.5.8 \
  dd70d8ae49ca0c08541c01ced7c74e310b49692e8a312185824e5ce06bdfd115 \
  14d40ec690d4d2e4d49f95d9509ec8b3112c39089f9ad11fa8bde42796b99190 \
  bb2d12bec3c53f997b5edf5e4ac3ed24584412008070eb731830f29896004ed4
```

Point a **fresh copied** `FnPortablePin.fnBinary` at the generated helper and
pin that copied manifest in the new Mini service config. Restart the service
against that exact config and a fresh private socket. Do not change an existing
accepted operation's Mini config, retained call, cursor, ACK, or publisher
state to migrate a helper. Historical test fixtures can keep their original
bridge and fault hooks; this renderer changes neither of them.

The renderer currently accepts only the reviewed bridge source SHA-256
`01eecf764899e659ae140b5d3896883a663bd64d25d97c1ef0d8988645bb976a`.
If that transport changes, review the transformation and deliberately update
the source pin. The generated helper still depends on the operator's hbox SSH
trust and private key custody. Hash pinning detects changed fn/toolchain
bytes; it does not turn a host-path observation into a cryptographic Store
proof.

Private bounded checks for the workroom fixture: renderer and generated
helper passed `sh -n` and `shellcheck`; an incorrect image hash refused before
output creation; a private generated copy with a wrong runtime hash refused
before cursor inspection. The real helper inspected the retained 108-byte fn
cursor with exit 0 and 367 stdout bytes while `FN_B3_IMAGE=/invalid` and both
fault variables were set. Its stdout was byte-identical to the historical
bridge using the explicit qualified image. These are transport checks; no
Mini or fn Store was mutated.
