# Prepared R opcode-16 response frame

`scripts/probe-fn-origin-outbox-op16-frame.lean` ran against the coherent
catalog `Host.Main` build. It constructed a selected-maximum synthetic R
carrier of 1,516,384 bytes and a 256-byte Message-ID. It used Host's actual
hex and receipt JSON helpers and mirrored every field returned by
`runFnOriginOutboxSession`, including opcode 16 and the hex-encoded canonical
observation intent.

PASS: intent 1,519,206 bytes; full opcode-plus-JSON response 3,039,281 bytes;
selected host frame cap 6,194,884 bytes; margin 3,155,603 bytes. Bounded output:
[origin-outbox-op16-frame.log](origin-outbox-op16-frame.log).

Probe SHA-256 `b241439d0d519260382c3c2f8817b53fc64d99f0fdbdf1f4c3dde2376425b5a5`;
log SHA-256 `4857cef15aef8e25f68dd4e5fbf4d4fdaad06ab7c13d9f9b811a140fef350eed`.

This is a pure serialized-frame size check. The synthetic carrier has no fn
authorship; native verification, source export, and receiving admission are
separate gates.
