# Two-subject application birth gate

Status: **staged, not run**. The source-matched Host image containing the typed
`application-birth[-intent]` and `application-session-birth[-intent]` author
routes is being qualified separately. No result here is native acceptance yet.

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
   and grant. Cross-subject reads of the other's session must return Mini's
   retained, signed `observation refused` result. The storage helper's exact
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

The script refuses an existing evidence directory. Keep its `*.key`, Store and
full attempts private. A successful run writes `application-acceptance.json`,
retains exact `call.bin`/`outcome.bin`, signed challenge/view pairs, refusal
attempts, service logs and the executable SHA-256 list. Publish a bounded,
keyless projection only after reviewing those artifacts and pinning the Host
source/build manifest. A timeout, missing reply or unclear submit outcome is
held for exact lookup; do not rerun the birth as a fresh intent.

This gate proves separate native identities, birth/fee admission, a shared
application reference, bounded delegated observation and exact receipt
continuity. It does **not** prove application dispatch, browser/UI or API
transport, participant-selected role authority, an SPK package, or a real
model. Those require a checked enrollment/dispatch receiver and the hosted
typed composite birth path. Current MCP `mini_create_resource` admits only
operator-pinned single-content families; the typed births here use direct Mini
authoring rather than claiming that hosted tool integration already exists.
