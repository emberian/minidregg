# Native application share-issue acceptance

`native-positive-base.sh` creates a fresh two-subject app/session Store under
an operator-pinned positive initial-payload byte tariff. It copies the reviewed
provision, member, and app scripts to a retained private sibling source stage,
then changes only the two tariff fields, initial payer balances, and the
member's underfunded balance. It hashes inputs before and after execution and
keeps stage logs on failure. Do not point it at an existing Store.

`native-acceptance.sh` uses that base with a source-matched Host and Mini. It
checks private op32 custody, payer/funding/header tamper refusal, a same-Spec
low-balance alternate-payer refusal with unchanged full Store image, exact signed fee
against the payer's Book balance delta, one op28 installation, no second
submit, current ticket content, and op29 historical receipt after reopen.
The `FEE_INSPECTOR` launcher runs `inspect-signed-fee.lean`, which strict-decodes
the retained canonical Plan and signed birth descriptor using the source codec.
The alternate-payer refusal by itself does not isolate balance from that
payer's authority; the accepted payer-8 control and source admission checks
provide the surrounding evidence.

The caller must supply executable `HOST`, `MINI`, `STORE_BINARY`,
`SIGNATURE_BINARY`, `FEE_INSPECTOR`, and reviewed `BASE_SCRIPT`. The positive
base additionally needs `PROVISION_SOURCE`, `MEMBER_SOURCE`, and `APP_SOURCE`.
Set `MINI_LEAN_ROOT` and `FEE_SOURCE` for `inspect-signed-fee.sh`; it claims one
Lean seat and runs from the source-qualified build tree. Pin every executable
and source hash in the resulting evidence before interpreting a verdict.

`PACKAGE_ROOT`, `INTERFACE_ROOT`, and `SCHEMA_ROOT` must come from the exact
signed GitWeb SPK descriptor and installed Mini manifest. The issue test alone
does not establish package installation, runtime launch, or HTTP dispatch.
