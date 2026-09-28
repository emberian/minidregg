# Current Mini binaries with upstream Hermes on hbox

This is a new, private runtime root at
`/tank/dregg-preview/hermes-upstream-r2/runtime-root` on hbox. It is separate
from the [r1 upstream/no-provider baseline](../2026-09-27-hermes-upstream-hbox/README.md).
Its tracked Nous Hermes Agent 0.21.3 source is the clean archive of commit
`6d8a8bebf70b09554deda5a0fcd95facbbde7b07`, copied from r1. The
`pyproject.toml` SHA-256 is
`eb0b8daac75c0c0e655282a1a836cb4c8a0bdc266e435a4d77e3295544ccf488`;
`uv.lock` SHA-256 is
`811a21647251a3fd024a3e2f49c90ac0600c678e500cc08ed51db38c452a6c65`;
`/agent/hermes-acp` wrapper SHA-256 is
`d9b2b31dcce207f8397a7e1606a6d8586a25e661744b610340d83b2c0c25b7ee`.
The root and runtime-root are hbox-owned mode 0700. Source and venv were
installed anew for this root; the editable Hermes package metadata points to
the r2 source, not r1.

The committed Mini `18166e5` Linux release binaries were copied only after
readback against the builder's protected artifacts:

| Runtime member | SHA-256 |
| --- | --- |
| `/agent/grain-runtime` | `7295fa222c288ad39aa5c6d97ef4f72ce5792e0f41413fb5d4e254eeba219187` |
| `/agent/grain-provider-bridge` | `2877ef2a5293ee0b2a7c22d0c0216dab865d3174dd68b312889661cb4f90cfcb` |

Both are mode 0500. The builder reports an exact-commit crate archive SHA-256
`48e2fbff7d8cbcfc7580462af000e27c01339f77ad11b7e753c1aad247c33d8d`,
37-file source manifest SHA-256
`33d2f59b1973b42dc49241f3dbf08c83dfe99d886bf34b8495472b1eeaacae38`,
offline locked two-job release build, and 37/37 source readback. This lane
did not rebuild those binaries.

The private uv 0.12.17 executable from r1 (SHA-256
`553a67a24d306a803d5c45678b7c54ed0c8b698d9fe3835d54905811348ccf2a`)
ran `uv sync --locked --offline --no-dev --extra acp --python /usr/bin/python3
--no-python-downloads` with a new r2 venv, bounded by a user unit at 4 GiB,
one CPU, and 900 seconds. It resolved 259 and installed 65 packages from the
private cache; the unit finished successfully. The retained
[uv-sync.log](uv-sync.log) SHA-256 is
`5aab97c09e8598010e9c21832c5fd33e123c0b144951ca65fc81d5266b44468e`,
and the 65-entry [venv-freeze.txt](venv-freeze.txt) SHA-256 is
`ff666e3b42c0044590941e220d168ea5b7294f453ac508917c822c8c765d3589`.
No global Python package or `~/.hermes` state changed.

The private launcher SHA-256 is
`efda87a5033fc24bb074cc68bfcca8686a448cd4e10175ca8d74b2c6884961a7`.
It differs from the reviewed launcher only in its fixed executable path to
the root-owned AppArmor-qualified bwrap described in r1. The launch-gate
SHA-256 is `2cf1d29ad7fcbce8e2e476ce803bc0c77785f720ceca02ba77e2530b849e7fb6`.
The first bounded r2 probe used the original 20-second check deadline and
timed out amid hbox I/O contention. Its worker and controller were confirmed
inactive before a new probe. Its
[keyless log](probe-first-timeout.log) SHA-256 is
`a79a8e9fa545739ae5b9b54a88d67685b800f22f64399edf8bf8e92affb0bdc0`.
The successful probe changed **only** the
private probe's check/initialize timeouts to 90 seconds and dummy controller
lifetime to 240 seconds; that probe script SHA-256 is
`2601aed558d888f4e78d702b600f4181994488325059eeec9e1dfacbccc9c2d9`.
Its [keyless log](probe-loadbound.log) SHA-256 is
`4878a708a2f1462a698c2109e4b4bf0cef9bbd228f295a38ce909678542bf9d5`.
It passed real upstream `hermes-acp --check` and ACP protocol-v1 `initialize`
with setup-only authentication in separate **no-network** systemd user
workers. Both workers and the dummy controller were inactive afterward; the
second worker used about 55 MiB peak. The bridge executable was staged and
hash-checked but was **not** activated: no provider socket, model prompt,
MCP tool, Mini Store mutation, or paid request was involved.

Next integrated acceptance must use current Mini Host/profile and a private
controller provider socket, recheck root/binary hashes, then demonstrate the
source-owned Mini MCP route and actual upstream Hermes conversation. This
component probe alone does not qualify the provider bridge or app authority.
