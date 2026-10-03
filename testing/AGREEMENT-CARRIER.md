# Ordinary source calls through the scheduled carrier

The native socket transport already accepts ordinary opcode 2 inside the complete
pinned version 2 envelope. `public_envelope` checks the exact configuration and
request bound; `allowed_operation` includes opcodes 0–11. The socket checks the
Host image pin, and the actual Host validates the canonical SignedCall. A naked
opcode 2 request, a mix enrollment, and a private evaluator ingress are not an
alternative source authority.

`agreement-carrier-packet.rs` exports the existing physical envelope from the exact
original SignedCall without decoding, signing, submitting, or manufacturing a
receipt. It is Linux-only standalone receiving tooling:

```sh
rustc testing/agreement-carrier-packet.rs -o /private/build/agreement-carrier-packet
/private/build/agreement-carrier-packet PRIVATE-CONFIG HOST-SHA256 EXACT-SIGNED-CALL NEW-PRIVATE-OUTPUT
```

All file inputs and the output directory must be owner-private. The output must
not exist. The exporter retains every original call byte and emits
`2 || LE32(config length) || config || host SHA256 || 2 || original call`.
The result is the mailbox's opaque native body, without the outer socket length.
Use the existing `mini serve` with the pinned agreement operator and configuration;
no second socket controller is needed.

An actual 21,591-byte configuration and 2,674-byte retained call produce a
24,303-byte envelope. That exceeds the 4 KiB carrier profile. A fixed public
32 KiB payload admits it, with request capacity 32,702 and response capacity
32,694 bytes. At width four, 64 epochs and the existing six phases, the largest
per-link wire inventory is 9,633,664 bytes, below the 64 MiB custody bound; total
wire traffic is 79,975,168 bytes per complete pole. Check actual response size
before enrollment. The public profile and provisioning interval must be fixed
before the public origin; failed private work must never move the schedule.

The agreement operator reloads the four independent source stores and looks up
the original canonical event. An installed call returns the retained receipt
through `completedCall` and compares each replica's prefix through that call;
it does not offer the operation again. The carrier's physical ticket and fresh
reply capability do not change source identity. Missing physical reply means
UNKNOWN. A recovery fetch binds the original class, body digest and original
recovery capability and does not dispatch again. If the result was never retained
in carrier custody, use the actual original-call source lookup, rather than
inventing a response or treating absence as rejection.

This transports an ordinary SignedCall. It does not implement confidential
party evaluation or source families 203–205. The useful traffic observer includes
public cohort membership, IPs, enrollment, lifetime, class, scheduled phases and
fixed record sizes. The current carrier assumptions include at least two honest
client contributions, an honest whole-batch shuffle, a noncolluding registrar
that authenticates exact sets, and an honest receiver with private antirollback
custody. Fixed shape alone is not an unlinkability proof. Execution endpoints
still see the ordinary native request and result; adaptive corruption and key
compromise across lifetimes require further construction.
