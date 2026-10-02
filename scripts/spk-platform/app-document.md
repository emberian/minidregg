# Delegated spreadsheet export into a Mini document

A connector is an independently enrolled participant. It holds one document's
`observe,mutate` grant, a task's observation grant, and the app/package
observations admitted for its own session. The app owner issues its session's
share ticket. The connector never uses the owner's signing key to capture or
publish an export.

For the currently qualified EtherCalc package, the signed bridge has no API
interface. Use a dedicated `web` session and the signed read-only role
`{"type":"role","id":"1"}`. Its cookie credential belongs to that session.
The capture custodian is confined to a single `_/SHEET/csv` GET, with a required
capture nonce header, empty body and no query. Other paths and methods are
refused before physical app delivery. Redirect responses are not exports.

`app-document-provision.py INPUT.json` reuses the same-Store fixture's native
birth, ticket, delegation, enrollment and route primitives. Its input names a
pinned existing fixture, fresh evidence root, independently held connector key,
connector workspace, existing `task` and `document` reference names, exact sheet,
signed role basis, and fresh session/ticket/capability coordinates. A started
provision cannot be rerun blindly; every native attempt remains in its own
hooks. The result includes a current-source resident registration request and
credential **path**, never the credential value. The resident and HTTPS route
must use the coherent capture-enabled SPK artifact.

Create a private capture binding with these exact fields:

```json
{
  "type": "mini-app-document-binding-v1",
  "subject": "CONNECTOR_SUBJECT",
  "appReference": "app", "app": "APP", "generation": "GENERATION",
  "packageReference": "package", "packageManifest": "PACKAGE_MANIFEST",
  "sessionKind": "web", "credentialKind": "cookie", "apiPath": null,
  "session": "SESSION", "sessionGeneration": "SESSION_GENERATION",
  "ticket": "TICKET",
  "taskReference": "task", "task": "TASK",
  "document": "document", "documentCapability": "DOCUMENT_GRANT",
  "sheet": "EXACT_RETAINED_SHEET",
  "endpoint": "https://connector.example/",
  "token": "THE_CONNECTOR_SESSION_CREDENTIAL",
  "ca": "/absolute/path/to/route-ca.pem"
}
```

Every numeric field above uses its actual canonical decimal source selector.
`ca` may be null for a publicly trusted certificate. HTTPS certificates are
verified; credentials are supplied to curl through stdin rather than argv.
The app/package/task and destination are read under the connector's own current
authority before capture. Receipt selectors must match the binding and exact
response body. The receipt establishes native admitted-request provenance and
host/TLS response custody; it does not claim the kernel attested spreadsheet
response bytes.

The Mini shell offers:

```
doc app-export capture export-1 @binding.json
doc app-export publish export-1
doc app-export status export-1
doc app-export recover export-1
doc app-export rebase export-1 export-2
```

Capture retains encrypted exact CSV bytes, source observations and receipt in
`WORKSPACE/app-documents/ID`. Publication appends those bytes with app generation,
exporter, body digest and original native operation attribution through ordinary
document authoring. `recover` performs exact lookup of an existing document
call. `rebase` refreshes the destination only after a definite refusal or a
writer failure before any call; it preserves the original export and claims one
unused successor. Unknown source capture or document admission remains retained
and is never replaced by a new physical export. Restore the complete workspace,
including `app-documents/storage.key`, with its writer quiesced.
