# Mini-to-SPK-host claim and dispatch contract (staged)

This is the host-side contract for the pending native lifecycle claim and
current dispatch projection. It is a **required interface**, not a claim that
Mini's Host opcodes or a production HTTP route already exist. The public
`spk-hostd` endpoint continues to answer `unavailable` for `begin` and
`dispatch`. A caller-supplied JSON object, decoded BEGIN ingress, generic DRC
receipt, or unsigned observation must never construct the Rust permit types.

## Source-owned launch claim

The operator host invokes a pinned Mini executable against its protected Host
config/socket and receives Mini's canonical verified result. The result must
bind all of these values on one loaded image:

- Original accepted special BEGIN ingress and its original event/nullifier,
  transaction and operation identities; accepted historical prefix.
- The one-shot special CLAIM event/nullifier (event codec v16), transaction,
  app resource, BEGIN kind, process generation, and claimed app phase. The
  only claim phases are install 8, start 9, stop 10, and upgrade 11.
- Exact installed package digest and immutable image identity, process/unit
  identity, current app/package/authority roots, and current world root.
- Fresh current signed mutation authority under the original BEGIN subject
  and capability, the installed v2 app/package management policies, and fresh
  signed app/package observations. The native result must establish these;
  Rust does not reimplement Lean admission from display fields.

The host compares the source-derived image/unit identity to the operator-pinned
package and exact systemd unit, durably records the original and claim
identities, and consumes the generation-specific claim under the same flock as
its launch tombstone. It requests a fresh current native claim check immediately
before `ExecStart` and before exposing a serving session. A mismatch, absent
claim, uncertain Mini response, or physical identity drift retains Fenced; it
does not retry a launch. The native canonical response and its checked
projection must be bounded and versioned. Unknown versions and any integer
that cannot be represented by the selected physical unit naming scheme are
refused, never truncated. Mini resource and subject zero are not rejected by
fixture convention; the exact source-owned claim determines validity.

## Source-owned request admission

Every browser or API request requires its own accepted current Mini dispatch
projection. The native source must select the accepted special share-issue
event and current ticket, check issuer delegation lineage and participant
ticket/app/session grants, enforce effective ordered bits within the immutable
ticket ceiling, and derive the 32-byte app-visible principal. A participant's
enrollment request, HTTP method, display label, raw ticket bytes, or headers
do not grant a permission bit.

The checked projection must include exact app/process and session resource,
generation, subject and kind; ticket/interface/schema/enrollment roots; the
selected issue and pending dispatch event/transaction/operation identities;
the ordered effective bits and source-derived principal; and the exact
projected request method, path plus query, body, cookies and allowlisted
ordinary headers. Mini must synthesize app security headers from checked
identity/bits, ignoring caller-supplied `X-Sandstorm-*` and `generated` flags.
Rust forwards only the projected request to fd 3 once and records uncertainty
on timeout or disconnect. It never retries a possibly delivered write.

The source-only native `requestSafe` check is still evolving; its currently
narrow-compiled shape bounds the relative UTF-8 path plus
query to 8,192 bytes, the body to 8 MiB, and headers to 128 with names at
most 128 and values at most 8,192 bytes. It permits GET, HEAD, POST, PUT,
PATCH and DELETE; GET/HEAD/DELETE have no body. It rejects a leading slash,
fragment, embedded second query separator, NUL/CR/LF, and any received
`generated` header. The received lowercase ordinary-header allowlist is
`cookie`, `accept`, `accept-encoding`, `content-type`, `user-agent`,
`if-match`, `if-none-match`, `x-requested-with`, `x-csrftoken`,
`x-csrf-token`, `oc-total-length`, `oc-chunk-size`, `x-oc-mtime`,
`oc-fileid`, `oc-chunked`, `oc-checksum`, `oc-chunk-offset`, and
`oc-lazyops`. Rust may mirror these as a transport refusal, but that check is
not native authorization. In particular, a client cannot set Sandstorm
permission headers by passing ordinary HTTP headers. The final wire schema and
these exact request bounds must be rechecked against the frozen source before
turning on dispatch.

Mini must supply a stable, source-owned 32-byte session fingerprint that
changes when app-side identity or effective authority changes, but remains
stable across ordinary requests under the same authority. The current
source-only `ApplicationDispatchAdmission.CheckedCurrent.sessionFingerprint`
uses cSHAKE256 under
`DREGG/APPLICATION/DISPATCH-SESSION-FINGERPRINT/v2`. Its narrow-compiled
source is `Kernel/ApplicationDispatchAdmission.lean` SHA-256
`7ca185ef954169da45dcc4b6c09bf6a0022ec60e68a9fe409c5cbb7bd67c878e`.
The
typed preimage includes the current authority root, checked app with snapshot
version set to zero, checked session and identity, ordered effective bits,
ticket resource/root, enrollment resource/root, and exact selected issue
ingress bytes. It excludes the request, session root, app root and durable tip.
This source-only definition still needs an accepted two-request integration
gate and a frozen Host wire; no Rust wire parser assumes the composition. The physical fd 3
driver caches an app-side session
by app, process generation, session resource, subject and Web/API kind, and
reuses it only while this source fingerprint and every app-visible session
parameter match. Any drift drops the old capability before another request.
The cache is bounded to 32 live entries and selects its least recently used
entry for eviction when a 33rd app-side session is created. A private GitWeb
component run created 33 distinct read-only sessions, then revisited the
oldest and observed a new app-side session with the cache still at 32. That
run used synthetic projections and does not qualify Mini dispatch admission.

The pending native wire codec, Host opcode and CLI projection filenames remain
to be frozen by the Mini owners. The Rust parser and endpoint connection are
therefore intentionally unavailable; this document does not define an
independent Rust authorization algorithm or a caller-authored permit format.
