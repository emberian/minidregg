# Typed event22 preview consumer

Both `issue-human-ticket.sh` and `issue-agent-ticket.sh` now call the bounded
Mini `grain-share-issue-plan` route over the pinned private operator socket.
They retain its read-only op56 frame, plan, inspection, source request and
pin in `preview-native/`. Before copying its plan into the existing
`preview-plan.bin` and `preview-plan.json` names, each wrapper checks exact
request JSON, config, canonical request, request inspection, binary Host and
config hashes, socket, request hash and plan hash. Existing approval and
op56/57 preparation still compare their exact plan and request against those
reviewed preview filenames. The stage also hashes the retained typed plan
pin and checks it again before approval. Preview does not sign or submit.

The hbox schema-only fixture uses a synthetic Mini preview and Host over
the existing private ticket fixtures. It exercised the complete prepare
branch of both wrappers, compared copied and retained request/plan bytes,
rejected a changed Mini plan pin before stage completion, and rejected a
changed retained pin before approval. See
`schema-only-hbox.log` and the two retained fixture scripts. The actual Mini
route source is frozen by the resource-client owner, but its native linked
binary qualification is still pending; this mock does not establish current
Store admission or a source-certified executable. No r3 Store was touched.

The exact fixture copies are `/home/hbox/mini-ticket-preview-typed-r3.sh`
and `/home/hbox/mini-ticket-preview-test-r3.sh`, using the existing
`/home/hbox/mini-agent-ticket-schema-r1` inputs. The fixture is intentionally
one-use; choose fresh `typed-*` directory names when rerunning.
