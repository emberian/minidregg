# Actual Hermes grain publication as an fn R source

This bundle captures the first upstream Hermes MCP publication from the r5
Persvati Mini deployment. Parent grain 7101 witnessed tool grain 7102 settling
its delegated allowance in the same accepted invocation that created scalar
object 7003, field 0, value 1. `outcome.json` reports **installed**, accepted
count 10. The separately signed resource read changed from
`publication-before-view.json` to `publication-after-view.json`; the latter
shows field 0 at value 1. These are Mini effects at A, not effects at B.

`call.bin` is the exact accepted signed call. `7003-package.bin` is its native
accepted-prefix export, not a hand-authored envelope. The source-matched
Persvati host exported it with `export-evidence` against the r5 pinned config
and then `verify-evidence` re-admitted its prefix and exact receipt. An
independent Mac host with the same Mini source/profile repeated verification
using `origin-pin-mac.json`; that file changes only physical executable/store
paths from `origin-pin-linux.json`. Both reported the transaction and event IDs
in `R.source.verified.json`, accepted count 10.

`R.source` is a strict seven-header CRLF MIME article with the exact package
as base64, group `fn.test`, and Message-ID derived from that receipt. The
source-owned `scripts/fn-e1e2/render-grain-origin-r.lean` checked the named
tool grain's reserved-to-settled transition, unchanged reserved parent witness,
and nonempty scalar publication to object 7003 before writing it; its
`FnPortableSource.extract` round-trip checked the package and headers. The
renderer source executed for this artifact had SHA-256
`889368250a6571ccf1991f493afce7def3b3eb4e9698f742d1d7aa74e4a6531f`.
The later one-line source tightening also requires nonempty content actions;
it does not change this scalar artifact.

The source is an **input** to fn hybrid signing and Store admission. Neither
this bundle nor Mini verification claims that fn has accepted R or that another
Mini has consumed it. The dynamic fn harness must derive source identity from
fn's native hybrid verification of this exact R; old fixture R claims and
Message-IDs cannot be reused. If B consumes it, B's own content inbox records
the carried A receipt and provenance rather than applying A's scalar field.

`SHA256SUMS` covers every evidence payload here. The native executable paths
in the pins are machine-specific; private keys and live controller state are
not included.
