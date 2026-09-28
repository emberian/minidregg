# Shared GitWeb file journey (prepared, not yet run)

Run only after the real app 8401 has a confirmed resident START, event22
human tickets and agent lifetime routes are accepted, and the three human
entrances and both agent controllers are physically live. The signed package
exposes Git smart HTTP at `/repo.git/` and read-only GitWeb CGI at
`/gitweb.cgi`; it does not expose a JSON file-edit API. Alice's API session
8410 can write via a bearer-authenticated Unix HTTP entrance. Alice and Bob's
separate Web sessions 8404/8406 can read through their own cookie-authenticated
entrances. Hermes A/B edit through their own `mini_gitweb_edit` MCP tool and
current Mini application dispatch, not through Alice's token.

Choose one small public UTF-8 file, for example `public/research-note.txt`.
The operator must provide the exact private socket/token paths from the
qualified resident config. They are not inferred from the allocation alone.
Keep every attempt in a distinct new 0700 operator directory; never print or
copy token bytes into command arguments or a transcript.

1. Seed the empty Git repository once through Alice's API entrance:

   ```sh
   gitweb-human-journey seed-api \
     ALICE-API-HTTP.sock ALICE-API/api.token EXPECTED-HOST \
     public/research-note.txt PRIVATE-600-initial.txt 'Alice creates research note' \
     NEW-PRIVATE-SEED-DIR
   ```

   The planned Rust CLI keeps a random local proxy credential in a 0600 Git config,
   reads Alice's API token from its 0600 native custodian file, forwards only
   fixed smart-HTTP routes to her Unix entrance, and retains one durable
   `receive-pack-forwarded.marker` **before** forwarding a mutating POST. It
   fsyncs `push-intent.json` with the expected commit, file SHA, path, Host,
   socket and token digest **before** the push. It makes one Git commit/push
   and then read-only `ls-remote`; `result.json` records the exact commit and
   file SHA-256 only after the one-send marker and remote ref both match. If
   push/reply is uncertain, stop and run only the retained read-only check:

   ```sh
   gitweb-human-journey lookup-api \
     ALICE-API-HTTP.sock ALICE-API/api.token EXPECTED-HOST NEW-PRIVATE-SEED-DIR
   ```

   `lookup-api` rechecks the retained local repo, expected commit/file bytes,
   exact entrance and marker, and makes only a Git upload-pack/ref read. It
   records the observed remote master in a new numbered result, including a
   mismatch or absent ref. A matching remote ref is app state readback, **not**
   a Mini historical dispatch receipt; reconcile the exact resident journal
   separately. Never rerun the seed or push as a recovery shortcut. The
   bridge is transport only; each upstream request still needs Mini's current
   dispatch/settlement.

2. Check that Alice and Bob independently see exactly the committed file:

   ```sh
   gitweb-human-journey view-web \
     ALICE-WEB-HTTP.sock ALICE-WEB/browser.token EXPECTED-HOST \
     COMMIT-OID public/research-note.txt FILE-SHA256 NEW-PRIVATE/alice-view.json
   gitweb-human-journey view-web \
     BOB-WEB-HTTP.sock BOB-WEB/browser.token EXPECTED-HOST \
     COMMIT-OID public/research-note.txt FILE-SHA256 NEW-PRIVATE/bob-view.json
   ```

   These are `GET /gitweb.cgi?...a=blob_plain` through distinct authenticated
   Web entrances. A 200 response must have the exact file SHA-256. This is a
   view proof, not a Bob write.

3. In **Hermes A's** own controller/session, use the currently advertised
   `mini_gitweb_read` with
   `{"application":"workroom-app","path":"public/research-note.txt"}`.
   Then invoke `mini_gitweb_edit` with the same application/path, revised
   bounded UTF-8 `content`, and a commit `message`. Retain the MCP result,
   native dispatch attempts, and reported commit/remote ref. Any uncertain
   receive-pack result is a stop: the worker deliberately permits only one
   mutating POST and cannot infer failure from missing delivery.

4. In **Hermes B's separately authorized** controller/session, read the file
   with `mini_gitweb_read` using its listed `coding-app` route, then edit the
   same path with `mini_gitweb_edit`. Confirm both controllers' routes resolve
   to app 8401 and are present in their own current catalogs. The route names
   are operator-pinned selections, not authority. After each edit, re-run
   both human Web views with the new full commit ID and file SHA. A and B
   should each see the same exact bytes from the one resident repository.

5. At the chosen final commit, have the volume custodian freeze a read-only
   snapshot of the **actual** qualified resident `/var/repo.git` (host mount
   `/var/lib/minidregg/spk/vars/8401/repo.git`) with its root volume witness,
   app unit identity and commit/ref evidence. The export script does not
   manufacture that provenance. Explicitly select the public file:

   ```sh
   scripts/gitweb-content-export/prepare.sh \
     READ-ONLY-QUALIFIED-SNAPSHOT/repo.git FULL-COMMIT-OID \
     public/research-note.txt public-demo-file NEW-PRIVATE-EXPORT
   scripts/gitweb-content-export/ingest.sh \
     HOST MINI PINNED-SOURCE-CONFIG.json SOURCE-OWNER.key NEW-PRIVATE-EXPORT \
     CONTENT-RESOURCE MUTATION-CAP ATOM-ID OWNER-SUBJECT \
     FRESH-NONCE-1 FRESH-NONCE-2 FRESH-NONCE-3 FRESH-NONCE-4 \
     NEW-PRIVATE-INGEST [PRIVATE-MINI.sock]
   ```

   `ingest.sh` authors one Mini content atom containing the commit, path,
   blob, file SHA and exact file bytes, then requires a signed readback.
   On uncertainty, use its documented `finalize.sh` lookup path, never a
   second mutation. The selected-release source owner may then pass that
   retained signed observation and atom ID to `selected-release-prepare`;
   source event14, fn POST/poll, recipient event13 and ACK are separate gates.

The `gitweb-human-journey` Rust CLI in steps 1–2 is source-staged but **not yet
linked or qualified**; those commands must not be run until its exact binary
is linked and reviewed. This is a command contract. No real resident
START, human/agent Git action, physical volume snapshot, Mini content ingest
or fn publication is claimed here. The Rust helper needs a source-matched
component probe against the native Unix entrance before the first live write.
