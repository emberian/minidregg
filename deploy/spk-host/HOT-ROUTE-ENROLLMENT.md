# Hot participant enrollment

A running resident can admit a new immutable participant route without restarting
its app, replacing its fd3 RPC owner, or changing any existing stream lease:

```sh
spk-host grain register-route --socket /absolute/generation/journal/route-control.sock --request /absolute/private/register.json
```

The request is a same-operator-owned regular file, mode 0600, in a private 0700
directory. It contains the strict JSON object below (coordinates are canonical
decimal strings, hashes/nonces are lowercase hex):

```json
{
  "protocol": "mini-spk-route-register-v1",
  "registrationNonceHex": "<fresh 32-byte nonce>",
  "expectedApp": "4501",
  "expectedAppGeneration": "4",
  "expectedSessionGeneration": "2",
  "directory": "/absolute/new/route",
  "dispatchCustody": "/absolute/private/new-custody.json",
  "dispatchCustodySha256": "<SHA-256 of exact custody file>",
  "custodianSha256": "<SHA-256 of exact route/custodian.json>",
  "displayName": "Member",
  "preferredHandle": "member"
}
```

Create new custody and token files from the authenticated enrollment outcome;
never rewrite an existing route's files. In particular, take the expected
session generation from the exact source enrollment receipt. The resident
checks custody/policy identity, all private token files, exact file hashes,
expected app/process generation, and the signed package's API availability.
The Unix control socket requires the resident operator's UID on both ends.
Commands and replies use a bounded 4-byte little-endian length frame; input
reads have an absolute two-second deadline. The source admission has its own
bounded budget. An abandoned or refused command does not end the resident.

The native source admission checks a newly signed challenge against current
Mini authority and the exact physical Store tip. The admission includes the
registration nonce, namespace, app and session generations, principal, ticket,
and session fingerprint. It does not open an app session, append a Store record,
or bill a dispatch. Only after its result matches the fixed custody does the
resident append a listener. Same-origin routes are allowed on distinct private
socket paths. Exact duplicate admitted bindings are refused; a later session
generation/fingerprint can create a new route, including with an unchanged
ticket if current authority admits it.

The success JSON reports `protocol`, `registrationNonceHex`, `routeIndex`,
`app`, `appGeneration`, `session`, `sessionGeneration`, `subject`,
`ticketResource`, `sessionFingerprintHex`, `admittedHeight`, and
`admittedWorldRoot`. An identical retry returns that original registration
receipt without adding another listener or renewing any lease. Reusing its nonce
with a different request is refused. This is an acknowledgement of registration,
not a new statement that authority remains current.

The poll registry is append-only, with a maximum of 64 routes in one resident
generation. Existing accepted sockets and stable route indices remain intact.
Registration pins are in memory for that generation. Retained route directories
are enumerated on the next START, with the same 64-route bound and a separately
bounded resident configuration size. Distinct directories may retain the same
origin, session, and ticket after regrant. Initial/restarted routes follow
per-request current admission rather than retaining an old generation pin; old
streams cannot survive generation STOP, and revoked tickets remain refused by
source admission.

Every dispatch through a hot-added route must match its admitted namespace,
app generation, session generation, principal, ticket, and fingerprint. A new
Mini-valid dispatch with a different binding is refused before fd3 delivery.
Currently this comparison occurs after Mini commits the dispatch: it finishes
that physical journal record as undelivered, so another participant is not
blocked by its one-shot marker. Such a mismatch can therefore leave a billed
Mini dispatch record. Moving this route pin into pre-CAS signed authoring would
avoid that record and remains a separate improvement. Initial START routes keep
the existing per-request current-admission path and do not yet have this hot
registration pin.

Stream invalidation is ticket-scoped for every human route, and additionally
bound to the exact admitted identity for hot routes. An old revoked token's
failure cannot cancel a new grant on the same principal/session. A changed
successful projection only attenuates streams of its own ticket. No registration
or retry can revive an ended lease.

Scoped Rust tests cover an actual local poll loop adding B while A's upgraded
socket remains open, exact retry/change refusal over the private socket,
private-file/hash/generation checks, a bounded slow input, current-admission
refusal without registration, dispatch epoch/fingerprint pins, and old-grant
versus new-grant stream isolation. Actual Mini enrollment/revocation, two-user
editing, and restart journeys must also be qualified on the joined candidate.
