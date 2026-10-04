# Mini runtime map

Consumer authority lives here; `_workbench` is mounted infrastructure excluded from ordinary scans. Read `index.spw`, `workspace.spw`, `mount.spw`, then `maps/runtime.spw`. The map separates source-read facts, inference, runtime evidence and unreviewed coverage; it is not whole-system qualification.

Current destination: Objective Bend, private computation, traffic privacy/agreement and the multiuser SPK/Hermes/docuverse worldhost. Executing legacy machinery is mapped as a migration dependency rather than erased from the model.

Run from the consumer root:

```sh
npm --prefix .spw/_workbench run spw -- doctor ../..
npm --prefix .spw/_workbench run spw -- roots
npm --prefix .spw/_workbench run spw -- tree @spw --depth 4
npm --prefix .spw/_workbench run spw -- select .spw/index.spw --selector navigable --summary
npm --prefix .spw/_workbench run spw -- lint .spw
npm --prefix .spw/_workbench run spw -- graph .spw --limit 30
python3 .spw/tools/check-source.py
```

Doctor's positional target resolves from npm's package working directory; `../..` selects this consumer. `doctor .` selects the workbench itself and does not diagnose this mount. CLI activation used `npm ci --ignore-scripts --no-audit --no-fund`. The initializer was read, but only its four portable templates were copied: no Git hooks or review workflows were installed.

The authoritative source scope is recorded in `audits/horse-entries/provenance.json`. Source links resolve into this consumer checkout for navigation; compare content hashes/revisions before treating them as the exact pinned bytes reviewed from the publication snapshot.

`audits/horse-entries/publication.json` records later receiving revisions. A source hash drift after a repair is expected; inspect the changed executable definition and its receiving receipt rather than treating old matching hashes as a claim about the updated source. For scoped lint, use a consumer-relative `.spw/...` path and check that the output actually reports a file examined.
