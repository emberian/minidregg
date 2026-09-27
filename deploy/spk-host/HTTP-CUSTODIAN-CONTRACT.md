# Private participant HTTP entrance (staged)

`spk-hostd serve-http-unavailable ABS_PRIVATE_DIR` binds only
`ABS_PRIVATE_DIR/http.sock`, mode 0600, for the same Unix UID. It opens no TCP
listener, does not start an SPK, and returns HTTP 503 after transport
authentication because Mini dispatch authoring and the checked permit route
are not yet present. The protected directory must be owner 0700 beneath
root/operator-controlled, non-task-writable ancestors. A second instance or
stale socket path is refused; the service never unlinks an unknown socket.

This is intended to become **one custodian per participant**, under a separate
Unix account from the SPK process. Its owner-private `custodian.json` is mode
0600 and names one fixed app, participant subject, session and ticket as
canonical decimal Mini coordinates. The incoming HTTP request cannot choose
those coordinates, a key file, or a signing subject. The current file also
contains an exact lowercase HTTPS host and SHA-256 hashes of two separately
provisioned high-entropy transport tokens:

```json
{
  "protocol": "mini-spk-custodian-v1",
  "expectedHost": "friend.example.test",
  "fixedApp": "6100",
  "fixedSubject": "8",
  "fixedSession": "6208",
  "fixedTicket": "6408",
  "browserTokenSha256": "<64 lowercase hex>",
  "apiTokenSha256": "<64 lowercase hex>"
}
```

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
Token issuance, `Secure`, `HttpOnly`, `SameSite=Strict` and `Path=/` cookie
setting, TLS termination and
the participant signer are not implemented in this staged slice. In an
initial private deployment, transport would be reached through an owner-
reviewed SSH-forwarded Unix gateway, never a public listener by default.

The parser supports one HTTP/1.1 request per connection, with one absolute
10-second frame deadline, at most 64 KiB of headers, 8 MiB of body, 128
headers, and an 8,192-byte relative app path plus query. It rejects duplicate
headers, transfer encoding, pipelining, caller `X-Sandstorm-*` fields, control
bytes in targets/headers, and body/method ambiguity. Zero-length POST/PUT/PATCH
is valid; HEAD responses have no body. It keeps only the ordinary headers named in the
current native `requestSafe` allowlist; proxy/browser metadata is not
forwarded. Those native bounds are still source work, and a frozen projection
must be rechecked before dispatch turns on.

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
