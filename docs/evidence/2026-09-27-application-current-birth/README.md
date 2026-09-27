# Current app and session birth native acceptance

The fresh Linux run at `/tmp/mini-application-current-birth-20260927/run-r3` passed `scripts/application-current-birth/native-acceptance.sh`. It used the source-qualified op30/31 Host at SHA-256 `4661301b549c2703b6910beceb8b32aaaee1e82b450ae9d70c408e10e41050a2` (build manifest SHA-256 `c6ba7446c40d3cdacd91ae10a8f239a0f27b8184996e0c5b55e5aa0737866493`), the Mini client at `29809a46e5cd64d49246ddcbb164012f993d7abd7eb623cafafe654a6ea7e1e7`, and the Store/signature helpers identified in `input-sha256.txt`. `input-recheck.txt` records the end-of-run hash verification, including the invoked base fixture script.

The fixture bootstrapped a metered parent/tool workroom, reserved tool capacity, authored app and session birth intents through current verifier-opened op30/31, submitted signed binary intents, and read back the app, package, snapshot, session, descriptor, and their policies. An explicit stale-height app draft was refused without an `intent.bin`. It restarted Mini after each birth, performed exact lookup of the retained original signed attempt, compared the four receipt fields in the paired JSON files here, and compared the full logical Store image before and after lookup. It also checked unchanged tool metering state and final remaining `38`, reserved `0`.

The app receipt was installed at accepted count `14`; the session receipt at `16`. Both recovered receipts were marked `replayed` and retained their original transaction ID, event ID, count, and image boundary. Full Store image SHA-256 before/after app lookup was `96ba39ba421a07997f04af031fb2b7eac14bddf226d876d6199509f57ca4709d`; before/after session lookup was `455ba7831332ab37d5995619a39c33b2a612071c4701970ed8ac4c0c310709b5`.

Run command (fresh destination required):

```sh
MINI=/tmp/minidregg-bd883d8-resource-client-evidence/bin/mini \
STORE_BINARY=/tmp/minidregg-776ba59-helpers-evidence/bin/minidregg-link-sqlite-store \
SIGNATURE_BINARY=/tmp/minidregg-776ba59-helpers-evidence/bin/minidregg-credential-signature-verifier \
scripts/application-current-birth/native-acceptance.sh \
  /home/ember/build/minidregg-overnight-20260927-currentbirth-native-evidence/minidregg-host-currentbirth-r1 \
  /tmp/mini-application-current-birth-20260927/new-run
```

This is a current-height and current-policy acceptance. It does not exercise issuer rotation; no native signed issuer-rotation route is connected yet. The separate hosted controller journey and share-issue path are outside this fixture.
