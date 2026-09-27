# Two-subject application birth gate

Status: **PASS for the native two-subject birth/read slice** on one fresh private
Mac Store, September 27, 2026. The source-matched Host was built from committed
`2e60a9c` plus the proof-only `bfb6b8b` repair. It passed 187/187 Lean modules
and linked 3,120 native objects. The Host SHA-256 is
`6635b3560280c9d9af544feb3fc5e49a446e498082520bfc24fb78241c50267a`;
the Mini, SQLite store and signature helper SHAs are `5139e1e1`, `7420e41d`
and `4f5a9095` respectively. Full source and artifact provenance is in
[`r1/manifests`](r1/manifests/) and [`r1/SHA256SUMS`](r1/SHA256SUMS).

The executable gate is
[`native/resource-client/application-acceptance.sh`](../../../native/resource-client/application-acceptance.sh).
It creates a new private Store, three independent signing keys and Book accounts,
and one pinned Mini Host session. It uses the source-owned typed authors through
the existing `mini submit --intent-kind` path:

1. Subject 7 births one application declared object plus package and snapshot
   manifests. The resulting native receipt and signed resource/policy views must
   show all three targets.
2. Subjects 8 and 9 separately pay for and sign distinct session/descriptor
   births. Both sessions name the same application target; their native owner
   grants, installed policies and signing keys are distinct. Signed views check
   the initial inactive Web/API tags and the shared app field.
3. Subject 7 delegates **observe-only** application grants separately to 8 and
   9. Each subject must read the same signed application root with its own key
   and grant. Cross-subject reads of the other's session must produce a native
   `observation refused` error for a retained signed observation request; the
   refusal text itself is not a signed receipt. The storage helper's exact
   logical image bytes must match before and after both denials.
4. The pinned Host session is stopped and reopened over the same private Store.
   `mini retry --mode lookup` must replay one original session-birth receipt
   byte-for-byte in its four receipt coordinates, without advancing the signed
   image boundary or changing the storage helper's exact logical image bytes.
   Both delegated app reads must still work after reopen.

After a source-matched Host and Mini client are supplied, run on an isolated
machine with no live deployment Store mounted:

```sh
MINI=/absolute/path/to/certified/mini \
STORE_BINARY=/absolute/path/to/certified/minidregg-link-sqlite-store \
SIGNATURE_BINARY=/absolute/path/to/certified/minidregg-credential-signature-verifier \
native/resource-client/application-acceptance.sh \
  /absolute/path/to/certified/minidregg-host \
  /private/new/application-acceptance
```

The actual run is private at `/tmp/mga-appbirth-two-subject-20260927-r1`. The
script refused any pre-existing directory. The keyless bounded package here
retains five exact signed calls and outcomes, the historical replay, signed
challenge/view pairs, both denied observation requests, source manifests and
the result projection. It excludes `*.key`, the full Store and private logs.
The first three installed receipts had accepted counts 1 (app), 2 (subject 8
Web session) and 3 (subject 9 API session); the two delegations were installed
at counts 4 and 5. The historical session-8 receipt replay matched its four
original receipt fields. Both signed participant app reads had the same root.
The storage helper's logical-image SHA-256 was
`8a4c3a28df708b3426e71cacda34419588143ccd3ac6e51cfa2189f0277d97e1`
before/after the denials and before/after Host reopen plus lookup. See
[`r1/image-sha256.txt`](r1/image-sha256.txt) and
[`r1/result.json`](r1/result.json).

A future timeout, missing reply or unclear submit outcome must be held for
exact lookup; do not rerun a birth as a fresh intent.

This gate proves separate native identities, birth/fee admission, a shared
application reference, bounded delegated observation and exact receipt
continuity. It does **not** prove application dispatch, browser/UI or API
transport, participant-selected role authority, an SPK package, or a real
model. Those require a checked enrollment/dispatch receiver and the hosted
typed composite birth path. Current MCP `mini_create_resource` admits only
operator-pinned single-content families; the typed births here use direct Mini
authoring rather than claiming that hosted tool integration already exists.
