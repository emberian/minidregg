# Grain-backed share issue: staged native gate

**Unrun.** The fixture is waiting for a source-qualified event-22 Host and
resource client. The older event-15 r4 admission refusal is retained
separately; this script creates a fresh Store and does not retry or modify it.

`scripts/application-share-issue/native-grain-acceptance.sh` starts from the
reviewed positive-byte-tariff app/session bootstrap, then signs a new reserve
of three units on active tool grain 7902. It checks the same-image parent
witness on grain 7901, prepares the distinct event-22 Request and current
plan, approves the full canonical Request and each ordered birth/app signing
header through operator custody, and sends exactly one op54 issue. It checks
that the direct source preview and the persistent operator's Request/Plan
bytes are identical before submission, then checks the installed ticket atom,
signed descriptor fee against actual payer Book
debit, tool settlement, a second-submit refusal, and op55 exact historical
receipt after reopening without changing the logical image. Wrong funding,
wrong header, public op56 and an underfunded payer are refusal controls.

The source-owned fee inspector decodes the retained event-22 Plan through
`ApplicationShareIssueGrainAuthoring.planCodec` and the finalized grain birth
codec. It was direct-Lean checked against the frozen event-22 OLeans on
Persvati: empty log
`/tmp/mini-share-grain-source-20260927/FeeInspector.log` (SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`),
OLean SHA-256 `8f1579d5bd8736bfc3b7805e18a54665def176dbd17a2c5025b81d931b57dcaa`.

Source SHA-256:

| File | SHA-256 |
| --- | --- |
| `scripts/application-share-issue/native-grain-acceptance.sh` | `b88e3a05b7ec42e9b5d939f98ec44772d06a1e2c5317313ed5232132e3bcfdcc` |
| `scripts/application-share-issue/inspect-grain-signed-fee.lean` | `57102608ad0bf6afd470cd8cc74332edacf10c0cce0013cee74f7383cc1bfd88` |
| `scripts/application-share-issue/inspect-grain-signed-fee.sh` | `0f96728529385159c70107e66462acbec8d5d1605b8cfa81a55d3ec6b1b64bed` |

The launcher requires absolute, immutable paths for `HOST`, `MINI`,
`STORE_BINARY`, `SIGNATURE_BINARY`, `FEE_INSPECTOR`, `BASE_SCRIPT`,
`PROVISION_SOURCE`, `MEMBER_SOURCE`, `APP_SOURCE`, `IDENTITY_ROOTS`,
`FEE_SOURCE`, `MINI_LEAN_ROOT`, and numeric roots `PACKAGE_ROOT`,
`INTERFACE_ROOT`, `SCHEMA_ROOT`. The last three must match the pinned
source-authored `gitweb-roots.json`. The first two positional arguments are
the qualified Host executable and a new private evidence directory. Input
hashes are checked before execution and again at the end. The positive-base
helper retains its private generated source stage on failure.

This gate issues a **version-0** ticket against the freshly born app and the
source-selected GitWeb descriptor roots. It establishes event-22 factory,
fee, custody, receipt and recovery behavior if it passes. An installed
version-1 GitWeb ticket, two-controller sharing, current dispatch admission
and physical app delivery require a separate integrated Store.
