# One selected GitWeb file into a Mini content atom

This is an operator-selected, public-demo export. It does not scan GitWeb
history, export a Mini Store, publish to fn, or send a recipient release. The
operator must first pin a **read-only snapshot of the real GitWeb bare
repository** from the qualified resident volume and explicitly choose one
public file at a full commit object ID. The physical snapshot and its volume
custody remain separate evidence; a caller-supplied Git repository path alone
does not prove which app produced it.

```sh
scripts/gitweb-content-export/prepare.sh \
  /private/volume/repo.git FULL_COMMIT_OID public/demo.txt \
  public-demo-file /private/export-selection
```

`prepare.sh` accepts only an exact regular Git blob at that commit and simple
relative ASCII path. It rejects an absent commit, symlink, submodule, oversized
file, non-UTF-8 bytes, unsafe path, and an existing output directory. It retains
the exact Git blob bytes in `file.bin`. `atom-payload.bin` is a text payload
with a `DREGG/GITWEB-CONTENT-EXPORT/v1` header binding the commit ID, path, Git
blob ID, file SHA-256 and length, followed by the **exact file bytes**. The
64-KiB file bound is intentionally much smaller than the selected-release
carrier ceiling.

After an existing Mini content resource has been born and the owner has a
current mutation/read capability for it, run a single new private ingestion
attempt. Each of the four nonces must be distinct and unused. The optional
last argument is the existing private Mini service socket.

```sh
scripts/gitweb-content-export/ingest.sh \
  HOST MINI PINNED-CONFIG.json OWNER.key /private/export-selection \
  SOURCE-RESOURCE CAPABILITY ATOM-ID OWNER-SUBJECT \
  BEFORE-QUERY-NONCE OBSERVE-NONCE COMMAND-NONCE AFTER-QUERY-NONCE \
  /private/ingestion-attempt [PRIVATE-MINI.sock]
```

The script queries the current content page through the owner's signed Mini
observation, refuses an existing AtomId, then lets the existing Lean Host
author and native receiver validate the singleton `createAtom` mutation. Mini
first prepares and durably retains the exact call without sending it; the
driver pins that call before its one planned `retry --mode submit`. It
requires an `installed` receipt from that submit. On a lost, refused, or
uncertain reply it **stops and retains the exact `create/call.bin`** and its
SHA-256 pin. Finish that attempt with a fresh, unused read nonce:

```sh
scripts/gitweb-content-export/finalize.sh /private/ingestion-attempt FRESH-READ-NONCE
```

If the driver died after preparing the call but before writing its shell-side pin,
`finalize.sh` checks Mini's retained attempt manifest, source intent, config,
plan and signatures, reassembles the call with the pinned Host, and pins it
only if the bytes match. `finalize.sh` then makes only an exact read-only
lookup of the retained call. The
latest lookup must return a confirmed historical receipt; if the original
installed reply exists, all four receipt fields must match. An absent or
uncertain lookup refuses completion. It then makes a fresh owner-signed
resource query in a numbered retained readback attempt. An interrupted read
can use a new nonce and another bounded attempt. A completed `selected/` and
`result.json` are revalidated, never overwritten. No recovery path resubmits
the mutation. The signed current resource query
must show exactly one live text atom with the same payload. The output retains
`selected/signed-observation.bin`, `selected/view.bin`, `result.json`, exact
call/receipt, and SHA-256 pins. `result.json` carries top-level `gitCommit`,
`gitPath`, `gitBlob`, `fileSha256`, `fileBytes`, `payloadSha256`, `sourceResource`,
`atom`, `sourceRoot`, and `selectedFile:"atom-payload.bin"`; `file.bin` is the
raw Git file and `atom-payload.bin` is the complete signed-atom content. The
selected release owner can pass the signed
observation as `signedQueryHex` and the `atom` from `result.json` to
`selected-release-prepare`; that Host rechecks the current page root and bytes
before producing its canonical owner-signature preimage. Source publication
event 14 and fn/recipient event 13 remain separate authorized steps.

`test-prepare.sh` exercises exact Git selection and unsafe-path/approval
refusals with a temporary local repository. It does not claim Mini admission
or physical GitWeb provenance. The operator must compare the retained Git
snapshot/commit to the actual qualified GitWeb volume before invoking either
script against a deployment.
