# Private participant HTTP entrance (staged)

`spk-hostd serve-http-unavailable ABS_PRIVATE_DIR` binds only
`ABS_PRIVATE_DIR/http.sock`, mode 0600, for the same Unix UID. It opens no TCP
listener, does not start an SPK, and returns HTTP 503 after transport
authentication because Mini dispatch authoring and the checked permit route
are not yet present. The protected directory must be owner 0700 beneath
root/operator-controlled, non-task-writable ancestors. A live second instance
is refused. Under the private service flock, only an exact owner/mode/inode
socket whose connect returns `ConnectionRefused` may be removed for restart;
all other stale or unknown paths are refused.

This is intended to become **one custodian per participant**, under a separate
Unix account from the SPK process. Its owner-private `custodian.json` is mode
0600 and names one fixed app, participant subject, session and ticket as
canonical decimal Mini coordinates. The incoming HTTP request cannot choose
those coordinates, a key file, or a signing subject. The current file also
contains an exact lowercase HTTPS host and SHA-256 hashes of three separately
provisioned 256-bit transport tokens:

```json
{
  "protocol": "mini-spk-custodian-v1",
  "expectedHost": "friend.example.test",
  "fixedApp": "6100",
  "fixedSubject": "8",
  "fixedSession": "6208",
  "fixedTicket": "6408",
  "bootstrapTokenSha256": "<64 lowercase hex>",
  "browserTokenSha256": "<64 lowercase hex>",
  "apiTokenSha256": "<64 lowercase hex>"
}
```

`spk-hostd init-custodian` creates a new 0700 directory and writes
`bootstrap.token`, `browser.token` and `api.token` as separate 0600 files;
stdout contains no token. It refuses an existing directory or invalid fixed
coordinate. The browser visits `/__mini/bootstrap` on the configured HTTPS
origin, receives a tokenless form, and POSTs the bootstrap token in the form
body with exact Origin. That endpoint accepts one token use, durably creates
`bootstrap.used` before sending a 303 to the constant `/` path, and sets the
browser cookie. A lost 303 after the marker requires operator review rather
than replay. Invalid or repeated bootstrap returns generic 403. Neither the
form action nor redirect URL contains a token.

The browser token is presented as `__Host-mini_spk_session` cookie. The API
uses a separate `Authorization: Bearer` token; a request with both is refused.
The cookie itself is stripped before any future Mini request, while unrelated
cookies can be included in that signed request. For browser POST/PUT/PATCH/
DELETE, the transport requires exact `Origin: https://<expectedHost>`.
`Sec-Fetch-Site`, when present, must be `same-origin`; safe GET/HEAD direct
navigation may use `none`, with `Sec-Fetch-Mode: navigate` and
`Sec-Fetch-Dest: document` if those fields are present. Cross-site metadata
and `none` on writes are refused. Any supplied Origin must match even on safe
methods and API requests. This allows
unchanged packaged browser forms to work without injected JavaScript. Tokens
only authorize use of this
participant's custodian; they do **not** grant a Mini resource permission.
The cookie carries `Secure`, `HttpOnly`, `SameSite=Strict` and `Path=/`; it has
no Domain attribute. A private rustls proxy binds only `127.0.0.1` at the
operator-selected port, uses owner-private certificate/key files and forwards
one bounded request to the fixed sibling `http.sock`. SSH can forward the
same loopback port to a laptop. Each custodian needs a separate hostname,
certificate and port; the browser must trust the certificate for that exact
hostname through an explicit operator/user action. No certificate trust,
DNS/hosts mapping, account, public listener or key distribution is changed
automatically. The participant signer and native checked delivery remain
unimplemented in this staged slice.

The parser supports one HTTP/1.1 request per connection, with one absolute
10-second frame deadline, at most 64 KiB of headers, 8 MiB of body, 128
headers, and an 8,192-byte relative app path plus query. It rejects duplicate
headers, transfer encoding, pipelining, caller `X-Sandstorm-*` fields, control
bytes in targets/headers, and body/method ambiguity. Zero-length POST/PUT/PATCH
is valid; HEAD responses have no body. It keeps only the ordinary headers named in the
current native `requestSafe` allowlist; proxy/browser metadata is not
forwarded. Those native bounds are still source work, and a frozen projection
must be rechecked before dispatch turns on.
The initial TLS proxy handles one connection at a time with a bounded request
and response; it is a private bootstrap transport, not a multi-tenant
availability or public reverse-proxy claim. Its certificate SAN and trust are
checked by the browser, while the custodian checks the exact HTTP Host and
Origin. A local process on the proxy host can reach its loopback port, but
cannot use either participant credential without the private token.

The missing native workflow is substantial: the custodian must load only its
configured participant credential, derive current request coordinates from
Mini, get the participant-signed DRC command and independently signed current
observations, submit the special dispatch event, and read back Mini's exact
checked projection. The physical fd 3 adapter may then build app-side
`SessionParameters` from the source-derived principal/effective bits and
forward only the checked request. No operator master signer fallback, caller
ticket, HTTP method, or token hash can substitute for that native admission.

For a two-friend GitWeb deployment, each friend gets a different Unix UID,
protected signer, fixed subject/session/ticket, private socket, browser origin
and browser/API tokens. Both custodians may target the same app resource only
through their separate native grants. The SPK host receives a checked principal
and ordered permission bits per request; it cannot choose a friend from an
incoming header or borrow either custodian's signing key. A package restart
preserves the app's `/var`; the current Mini dispatch check still runs on
every request, and the fd 3 cache invalidates when the checked v2 fingerprint
or app-visible parameters change. Native authoring/readback and credential
issuance remain pending.
