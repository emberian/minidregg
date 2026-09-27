# Standalone operator fn bridge — private dry run

The existing shared `scripts/fn-e1e2/fn_bridge.sh` depends on ambient
`FN_B3_IMAGE`. In the fresh workroom B service migration, omitting it made
`consumer-inspect` fail before fn ACK; the accepted Mini transaction and held
worker state were not rewritten. The new
`scripts/fn-e1e2/render-operator-bridge.sh` renders a standalone private helper
from reviewed bridge source SHA-256
`01eecf764899e659ae140b5d3896883a663bd64d25d97c1ef0d8988645bb976a`.
The operator supplies and verifies the qualified fn image, core, packaged
SBCL runtime, and OpenSSL executable/libraries by SHA-256. The generated
helper repeats those remote hash checks on each invocation, embeds literal
paths and transport code, and omits both fault-injection branches and the
ambient image lookup.

The isolated render under `/tmp/mini-workroom-publisher-20260926/operator-bridge/`
produced a mode-0700 helper, SHA-256
`8e6513335aa9665d5c8c6ee64723f3d86150f0309e6d2732e454ab81caa64480`.
`sh -n` and `shellcheck` passed for both renderer and helper. A wrong render-time
image digest refused with exit 70 and created no helper. A private generated
copy with a wrong runtime digest refused with exit 70 and no cursor output.
With `FN_B3_IMAGE=/invalid` and both `FN_E1E2_DROP_*` variables set, the real
helper ran read-only `consumer-inspect` on the retained 108-byte workroom B
cursor: exit 0, stdout 367 bytes, stderr empty. Stdout was byte-identical to
the historical bridge run with the qualified image explicitly set. No Mini or
fn Store was mutated by these checks.

The generated helper and copied R/Q pins remain private. A new A reply config
references the copied pins; **the held B worker's existing pin, cursor, call,
and ACK state were not migrated**. See
[`scripts/fn-e1e2/OPERATOR-BRIDGE.md`](../../../scripts/fn-e1e2/OPERATOR-BRIDGE.md)
for the operator command and custody boundary. This evidence establishes
transport setup and fail-closed behavior, not a successful B ACK or Q reply.
