# Authored canonical settlement Plan

The `CanonicalSettlementPlan.settle` and `settle_shared` methods invoke the
existing single-seller allocation and settlement sources. They convert the
computed transfer sequence into `WorldPlanMoney.NativePlan`, mark the room's
settled field from 0 to 1, and construct independent recipient return slots.
They do not accept a client-supplied transfer list.

The separate `UniformProRata` / `CanonicalUniformSettlement` DrEX rule remains
a different authored program. This wrapper does not relabel that rule as the
single-seller auction.

## Authenticated input

Native `ResourceMoneySampleTable.prepare` derives bounded account and asset
tokens from the actual `SampledFunding` value. Each namespace uses zero-based
first-occurrence ordinals. Repeated accounts reuse one account token across
assets; repeated account/asset roles reuse one authenticated balance. The table
retains canonical native ID bytes and the balances after the validated funding
prefix. Its book root remains the original durable expected root.

The source `Binding{token,native}` and `Table{accounts,assets}` are projections
of that generated **input** table. Every `Book.Account{account,asset,balance}`
in the source invocation must be assembled from its authenticated rows.
The source rejects duplicate tokens, split aliases, unresolved coordinates,
and a different book token/root. A returned sample table cannot authenticate an
earlier caller-supplied input.

The generic world invocation must bind the source arguments to the same
observation/profile, room reference, schema and encoding metadata. The wrapper's
book token is an ordinal, not a unary encoding of a native 63-bit ID.

## Native output

`WorldPlanMoney.Transfer` carries canonical native account/asset codec byte
lists and a source Nat amount. `BendMoneyPlanAdapter` decodes the complete
emitted Data constructors, checks the full ABI definitions in the checked Book,
and retains the completed source-machine trace. IDs use strict native codecs
with full consumption and canonical re-encoding; there is no truncating cast.

The adapter uses the actual command's unique money carrier and the receiver's
`Prepared deployment durable.snapshot entries` token. Its derived batch must
equal that prepared batch exactly, including operation order. All full account
consents, position coverage, funding, current signatures, capabilities and laws
remain in the native command and receiver. The Plan contains only the agreed
application projection: a single money consent with the derived batch and no
auxiliary positions/funding fields, then the ordered room scalar transition.

Scalar binding reuses `BendScalarPlanBytesAdapter` and the existing current-cell
prefix guards. No account balance is a scalar object write. Returns equal the
source result's independent slots. The actual world receiver must admit the
book write, room phase and return commitments in one durable transaction.

## Return encoding

Slot names are ASCII `r/` followed by `x` repeated by zero-based result position.
Each is unique within the invocation. Recipient, audience and key epoch come
from the actual computed allocation return. Schema, encoding and generation
are bound invocation metadata, never an authority grant.

The single-seller payload is length-framed reservation bytes followed by units,
price, payment and unspent reserved funds. The shared-account payload prefixes
the per-order reserved budget before those fields; the final field is the
remaining per-order budget. Every natural uses base-255 little-endian digits
followed by byte 255; zero has no digits before the terminator. The distinct
source entry/profile must bind the corresponding schema and encoding.

These are source-computed result bytes. No ciphertext, FHE, threshold custody or
proof of hidden allocation is claimed by this adapter. The native return and
audience mechanisms retain their own obligations. Compact arithmetic and
source-charge refinement remain compiler obligations, not a four-order or
machine-width restriction on this domain.

## Qualification and use

`scripts/check-collective-money-source.ts TOOLING OUTPUT [WORKSHOP] [WORLD]`
seals imports by exact source hash and emits the actual BendTT Books. Logical
`./WorldPlanMoney.bend` / `./WorldPlanScalarBytes.bend` import edges resolve to
the canonical files under `examples/objective-bend-world` via that manifest;
the loader does not permit filesystem traversal imports.

Source elaboration/emission currently passes for ScalarBytes, Money,
CanonicalSettlementPlan and its demonstration. General constructor/refusal
laws and source cases cover ordered mapping, missing assets, duplicate tokens,
split native aliases, two orders using one balance, insufficient aggregate
backing, stale book roots, and the actual room transition.
Actual BendTT Book checks and native adapter compilation/receiving are separate
qualification steps. The earlier five canonical allocation/settlement Books
have passed actual no-opaque Book checking. This document does not turn source
elaboration into a native settlement receipt.
