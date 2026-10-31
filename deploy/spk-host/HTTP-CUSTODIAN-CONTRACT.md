# Participant HTTP entrance (custodian)

The contract of the HTTP entrance a grain's resident process serves for each
participant route: who may connect, what bytes are accepted, which credentials
authenticate, and what happens to an accepted request. Code:
`native/spk-host/src/http_entrance.rs` (entrance), `grain_route.rs` (route
creation), `resident_service.rs` (the serving process), `dispatch_delivery.rs`
(what an accepted request does next), `bin/spk-browser-proxy.rs` (TLS in front).
The Mini-side dispatch is `MINI-CLAIM-DISPATCH-CONTRACT.md`.

Status words: the entrance, route creation and proxy **exist** (unit tests in
the same files). GET, POST and WebSocket opens through the proxy were
**journeyed** on the 2026-10-01/02 binaries: GET 35.5 s, POST 39.4 s and a
second app's GET 47.0 s end to end
(`docs/evidence/2026-10-01-spk-apps/jspk1/rows.tsv`, rows `s1-get-a`,
`s1-post-a`, `s3-get-b`); WebSocket opens 13.6 to 33.8 s
(`docs/evidence/2026-10-01-spk-ws/jspk10/rows.tsv`,
`docs/evidence/2026-10-02-spk-browser-tls/ethercalc-coedit.json`). Those
binaries predate the per-call fence, op 164 and `edgeGid`; no recorded run
covers them.

## Who calls whom

```
browser --TLS--> spk-browser-proxy --http.sock--> resident (spk-host resident-bootstrap)
                 (loopback TCP)                    --ops 36,37,34|164,35--> Mini Host (operator socket)
                                                   --fd 3--> the app
```

- The resident is one process per grain generation, running as the operator
  uid; it serves every route of its grain, each on its own Unix socket, through
  one dispatch loop (`resident_service.rs:1971`, `http_entrance.rs:974`). No
  entrance code opens a TCP listener.
- `spk-browser-proxy ABS_CUSTODIAN_DIR LOOPBACK_PORT` is the only TCP
  listener: `127.0.0.1` only, TLS 1.3 with the X25519MLKEM768 key exchange only,
  one thread per connection, at most `MAX_CONNECTIONS` at once; a connection
  past the cap is dropped without an answer
  (`bin/spk-browser-proxy.rs:25-30`, `:57-65`, `:495-502`). It requires
  `custodian.json`'s `expectedHost` to end in `:LOOPBACK_PORT`, and the
  `http.sock` it connects to to be mode 0600 owned by its own uid
  (`:463-492`), so it cannot front a route whose `edgeGid` is set (below).
  It forwards one request frame and relays the response; after a
  `101` answer to a WebSocket upgrade it splices both directions with no idle
  deadline (`:395-440`).
- Signing: the resident signs each request with the route's participant seed
  (`dispatch_author.rs:175-252`).

## Creating a route

`spk-host grain route PROFILE APP ROUTE_REQUEST.json`
(`grain.rs:1591`, `grain_route.rs:242`) takes a `mini-spk-grain-route-request-v1`
file naming the route (lowercase letters, digits, `-`, at most 32), the
expected host, display name and handle, the retained session-birth and
ticket-issue evidence, the participant key (id, epoch, public key, seed path),
and an optional export-capture opt-in with its one exact path. The app,
subject, session, kind, ticket and issue index are not request inputs: they are
derived from the retained, Mini-accepted evidence and cross-checked against each
other (`grain_route.rs:138-196`). The key is the request's; Mini checks it
against the plan's signer slots at signing time (`dispatch_author.rs:208-249`).

The route directory `<store>/host/apps/<app>/routes/<name>/` (mode 0700,
written under `.<name>.staging` and renamed) holds:

- `custodian.json` (0600, `mini-spk-custodian-v1`): host, the fixed
  coordinates, session kind (`web` or `api`), export capture, the SHA-256 of
  three random 256-bit tokens, and an optional `edgeGid`
  (`http_entrance.rs:316-388`);
- `bootstrap.token`, `browser.token`, `api.token` (0600; never printed);
- `dispatch-custody.json` (`mini-spk-human-dispatch-custody-v1`): the
  coordinates plus the signer pins for the six signing slots in
  `grain_route.rs:28-35`;
- `route.json` (display name and handle).

An existing route is reused only if its retained custody and policy equal the
request's derived values; otherwise the call refuses
(`grain_route.rs:224-236`, `:283-350`, `:379`). Routes can also be added to a running
resident through its `route-control.sock`, owner-only, after a fresh native
admission (`resident_route_control.rs:1-5`, `:563`).
`grain route` always writes `edgeGid` absent (`http_entrance.rs:379`); the
field is honoured when present in `custodian.json`.

## Transport

`http.sock` is created mode 0600 under an exclusive lock `.http.lock`; a stale
socket is removed only when connecting is refused and its inode is unchanged
(`http_entrance.rs:1221-1296`). A peer is admitted when its SO_PEERCRED uid is
the resident's effective uid (`:1312-1322`). When `custodian.json` has
`"edgeGid": "<decimal, not 0>"` the socket is chowned to that group with mode
0660 and a peer in that group is admitted too (`:263-275`, `:1275-1285`,
`:1325-1331`). Reaching the socket also needs search permission on the 0700 route
directory; no code grants it. The app-market front reaches sockets through an
operator-side connector that passes connected descriptors instead
(`docs/APP-MARKET-2026-10-27.md`, "Route sockets and the front").

One HTTP/1.1 request per connection, `Connection: close`, one absolute frame
deadline, bounds on head, header count, body and path+query
(`http_entrance.rs:21-28`). Refused: duplicate headers, `Transfer-Encoding`,
`Expect`, `Content-Encoding`, pipelining, control bytes, a body on
GET/HEAD/DELETE, any `X-Sandstorm-*` header (`:457-640`). Headers outside the
`allowed_ordinary_header` list are dropped, not forwarded (`:426-445`); Lean
re-checks what remains.

A request that fails parsing or authentication is closed without an HTTP
answer (`:1501-1535`); only the bootstrap endpoint answers 403/404.

## Credentials

`Host` must equal `expectedHost`. A present `Origin` must equal
`https://<expectedHost>`; a browser-cookie request that is not GET or HEAD
(a WebSocket open included) must carry it. `Sec-Fetch-Site`, when present, must
be `same-origin`, or `none` for a GET/HEAD navigation to a document
(`:681-745`).

Exactly one credential: `Authorization: Bearer <api token>` for an `api` route,
or the `__Host-mini_spk_session` cookie for a `web` route; both, neither or the
wrong kind is refused (`:700-745`). The browser first visits
`/__mini/bootstrap` (a form with no prefilled token), POSTs the 64-hex bootstrap
token with same-origin headers and no credentials, and receives the cookie
(Secure, HttpOnly, SameSite=Strict, Path=/) on a 303. `bootstrap.used` is
written before the cookie is sent, and a second bootstrap is refused
(`:1410-1481`). Tokens authenticate use of this route's custodian only; they
grant no Mini permission. The code has no token expiry or rotation.

## Dispatch

Each authenticated request is authored, signed and admitted by Lean (ops 36, 37,
then 34, or 164 for a route with a continuity binding) before one fd 3 delivery;
the sequence and every failure answer are in
`MINI-CLAIM-DISPATCH-CONTRACT.md`. A failure the member can act on is answered
`mini-spk-dispatch-outcome-v1` (`dispatch_fence.rs:146-175`).

Bounds before dispatch, per resident (`http_entrance.rs:752-761`): a queue of
pending requests with a per-subject share, and a longer queue of accepted
connections with a per-subject share, both with a queue deadline. When neither
a reader slot nor a wait slot is free, or the deadline passes, the answer is 503
`mini-spk-admission-v1` status `busy` (`:894-910`). A held physical delivery slot
answers status `uncertain`, retry `exact-recovery-only`
(`dispatch_delivery.rs:107-118`, `http_entrance.rs:945-955`). An accept or
reader-thread failure fails that connection only.
