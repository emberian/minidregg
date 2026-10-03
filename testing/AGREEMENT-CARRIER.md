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

## Qualification cut, 2026-10-03

The real four-store agreement first installed the original signed birth and
recovered its receipt after a lost caller response. The carrier subsequently
transported that **same original SignedCall**, using the existing native socket
and production operator's replay branch. It did not create a second effect.

The 32 KiB, 64-epoch comparison passed both the all-cover and actual source replay
poles: 768 authenticated fixed TCP records per pole, 64 canonical broadcasts at
all four audiences, one native source dispatch, and the exact source-produced
`confirmed.replayed` outcome. Four independent native reader processes returned
the same canonical receipt before and after, with accepted count one. A fresh
scanner process reopened the retained final outcome without network or source
dispatch. Wire lateness in the replay pole was at most 2.109 ms.

Early epochs 0, 1, 3 and 7 returned actual durable transport custody status,
without claiming a native verdict. The fresh-capability fetch at epoch 63 returned
the exact native response. The native operator's observed call-to-output file
interval was approximately 5.5 seconds, in addition to the declared two-second
proxy delay and three-second custody hold. This qualification establishes eventual
retained recovery within the complete public lifetime; it does not establish an
early useful-result bound. Adding a fixed additional repair opportunity is a
possible next latency improvement, while retaining exactly one source execution.

Two preceding orchestration attempts are retained as refusers: the copied
harness's wall and socket-idle horizons still assumed a 60-second startup, while
this profile declared 120 seconds. The qualified harness extends those supervision
horizons without moving the public origin or relaxing processing deadlines.
These runs establish a source-replay/carrier-recovery intersection, not a first
new effect admitted through the carrier, confidential computation, or a full
unlinkability theorem.
