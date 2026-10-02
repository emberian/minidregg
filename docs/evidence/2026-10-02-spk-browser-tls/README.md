# Browser TLS to actual EtherCalc, 2026-10-02

Source branch `codex/spk-service` on `spk-ws` fe29db5b. Runtime changes:
3a159154 (concurrent streaming proxy), 530c62ec (total HTTP deadline),
a68eb5ea (one host[:port] validator), b106ae15 (half-close final reply).
24e1933c adds verified TLS to the existing J-SPK-10 client. Host and Mini
client are the older, previously qualified spk-ws binaries, not current final.
Exact running binary hashes are adjacent.

A fresh real signed EtherCalc package was installed through Mini on persvati,
with a dedicated broker root, UID pool and Store. The first TLS open was
admitted but failed projection because a duplicate origin validator disallowed
ports. a68eb5ea replaces that duplicate with the custodian's strict validator.
A checked STOP completed, the operator upgraded the Rust binaries and pinned
profile, and a checked continue plus enrollment created generation 4 on the
same persistent volume. No public node was changed.

`ethercalc-coedit.json` is the actual repeatable J-SPK-10 result through
`https://localhost:18443`, verifying the route's test certificate:

- Two WebSocket opens: 13.574 s and 15.824 s.
- A1 edit reaches the other connection in 0.040 s.
- Committed records: 0 before, 2 after opens, still 2 after edit, 3 after CSV.
- Subsequent HTTP CSV GET returns 200 and contains the edited value.

The two connections use the same owner route. This is actual app co-editing
through TLS, not a browser UI test or a test of distinct members' grants.
Both HTTP readback and WebSocket paths use the proxy; no direct app network
port bypasses Mini's custody/admission path.

Reproduction (as the private route owner on the test host):

```
SPK_BROWSER_ORIGIN=https://localhost:18443 python3 scripts/spk-platform/jspk10-ws.py \
  ethercalc ROUTE_DIR GENERATION_JOURNAL overnight
```

The default CA file is `ROUTE_DIR/tls.crt`; `SPK_BROWSER_CA` can name another.
The test credentials remain outside Git.

Narrow new checks: five proxy TLS/TCP/Unix tests and seven dispatch projection
tests pass; scoped proxy clippy with `-D warnings` passes. The half-close test
failed before b106ae15 with upstream BrokenPipe/client UnexpectedEOF, then
passed after the fix. Source tests check malformed origins, both directions
beyond bounded buffers, 101 plus first frame, client final bytes, server final
reply after client half-close, EOF and bounded connection slot reuse.

## Old-kernel latency remains a product defect

Initial boot 59.25 s; birth 14.42 s; install 136.79 s; sharing 106.70 s;
initial START 144.52 s; initial enrollment 18.71 s. After the Rust upgrade,
continue START took 381.59 s and enrollment 41.40 s. These are measured
construction evidence, not acceptable hosting targets.

Checked STOP took 453.57 s. Its command started at 01:34:06; systemd physically
stopped the app at 01:37:06 within one logged second; the command completed at
01:41:41. The command unit used 309.363 CPU seconds, excluding the separate
persistent operator Host. Thus about 180 s preceded physical shutdown and
275 s followed it; process termination itself was quick. Adjacent journal
and artifact timestamps retain this distinction for the common candidate.

No further expensive lifecycle journeys should use this old kernel. Browser
UI and integration/reopen/sharing/revocation/restore qualification remain
separate work. The isolated generation stays available for root's browser
check; its operating coordinates are in the suite's SPK service report.
