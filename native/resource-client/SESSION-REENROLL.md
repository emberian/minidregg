# Session reenrollment after a compatible app upgrade

`mini session-reenroll` carries a participant's authenticated, pre-quiesce
session intent through a checked application generation change. It preserves
the previous event28 enrollment's exact role and ticket/capability selection.
The native Host owns observation, signing challenges, enrollment plans,
admission, and historical receipt lookup.

## Capture before quiescing

Create an owner-private JSON contract in an owner-private directory:

```json
{
  "type": "minidregg-session-reenroll-v1",
  "host": "/root-owned/old/Host",
  "config": "/root-owned/current/config.json",
  "publicSocket": "/run/mini/public.sock",
  "operatorSocket": "/run/mini/operator.sock",
  "priorEnrollment": "/private/accepted-enrollment",
  "participantKey": "/private/participant.key",
  "participantPublicKey": "LOWERCASE_ED25519_PUBLIC_KEY_HEX",
  "inspectorHost": "/root-owned/next/Host",
  "inspectorSha256": "LOWERCASE_SHA256",
  "signers": [
    {
      "keyId": "8008",
      "keyEpoch": "0",
      "publicKey": "LOWERCASE_ED25519_PUBLIC_KEY_HEX",
      "keyPath": "/private/participant.key"
    }
  ],
  "app": "4501",
  "oldGeneration": "4",
  "session": "4601",
  "subject": "8",
  "appObserveCapability": "4701",
  "nonce": "900000"
}
```

All decimal values are canonical strings within the client's unsigned 64-bit
bound. Choose a fresh nonce range of 100,000 values for this intent. Include
all keys required by the source's enrollment signing slots; the client refuses
an unavailable key rather than substituting another signer. Secret files hold
32 raw Ed25519 seed bytes and must be owner-private. Paths are absolute.

```sh
mini session-reenroll --phase capture --contract /private/reenroll.json \
  --dir /private/reenroll-attempt --socket /run/mini/public.sock
```

Capture exact-lookups the retained old enrollment through op85 on the old
pinned Host, then source-decodes its exact canonical ingress through
`inspectorHost`. This inspector must include the additive decoded `enrollment`
object; an old Host without that presentation is insufficient. The inspector
performs only pure codec inspection, never a Store operation. All authenticated
capture reads and historical lookup still use the old pinned Host.

Capture requires signed current observations showing the app serving
`oldGeneration` and the exact previously enrolled session active in that
generation. A closed, revoked, inactive, changed-generation, or changed-kind
session refuses capture. Success returns `status: "pending", phase: "captured"`:
this is the explicit retained pre-quiesce intent, not new authority.

## Resume after checked START

The upgrade coordinator supplies the root-owned compatible admission and the
actual new generation established by checked START. No increment is guessed.

```sh
mini session-reenroll --phase resume --contract /private/reenroll.json \
  --dir /private/reenroll-attempt --socket /run/mini/operator.sock \
  --admission /root-owned/upgrade/compatible-admission.json \
  --new-generation 7
```

The shared `minidregg-compatible-upgrade-custody` validator authenticates the
admission, source image/config pins, exact compatible config transition and
target image/helper pins. Resume immutably binds that admission and new
generation to the capture. It uses the target Host and retained target config
for all subsequent authenticated operations. The original config snapshot is
retained even when the live config pathname has been replaced by the upgrade.
The old image pathname may likewise be replaced or absent: resume binds its
historical digest to the authenticated source admission, while capture still
requires the original live image.

Resume requires explicit `managementSocket` and `publicSocket` fields in that
admission. Its public endpoint must match the captured contract; its distinct
management backend must support the same signed public operations as well as
operator operations. Pass that management path as `--socket` on resume. Both
signed queries/close and event28 operations use it while public ingress remains
stopped. The chosen topology is retained in the immutable execution pin. Legacy
admissions without these fields refuse rather than attempting the stopped public
relay or guessing a private endpoint.

Resume signed-reads the new app generation, then closes only the exact active
session captured before quiesce. A changed session root refuses a fresh close.
The close is a normal participant-authenticated command, prepared and retained
before its durable one-shot submission marker. An exact historical lookup must
confirm it. A subsequent signed read must match that close's expected session
state and generation.

The new event28 request copies the previous source request's ticket, selected
issue, role, and capabilities. Permission bytes are converted losslessly from
source inspection hex to authoring UTF-8 strings; unsupported bytes refuse.
The source plan must select the explicit new app generation, same participant
and session, unchanged role, and immediately subsequent session generation.
Current native authority still decides whether those inputs are admissible.
The client signs only explicitly retained signer identities, seals, submits at
most once, and exact-lookups op85 before its final authenticated app/session
reads.

## Results and crash handling

The command emits one JSON verdict with `type`, `status`, `phase`, `app`,
`oldGeneration`, `newGeneration`, `session`, `subject`, `attempt`, and
`receiptPath`. A completed verdict also contains the source-decoded
`enrollment`, including `appGeneration`, `sessionGeneration`, `capability`,
`descriptorResource`, `kind`, `role`, and `origin`. Use these exact generations
for the separate resident route-registration operation. This command does not
replace dispatch custody, register routes, or restart listeners. Do not treat
process success alone as reenrollment: require `status == "completed"`.

- `pending/captured`: pre-quiesce intent retained, waiting for the upgrade.
- `completed/authenticated-current`: exact event28 historical receipt selected
  and subsequent signed observations match the expected active app/session.
- `uncertain`: a mutation was attempted but the full acceptance/current-state
  chain could not be established. Resume performs only exact lookup for that
  mutation; it never retransmits the close or enrollment submission.
- `refused`: required inputs, authority, identity, or preconditions failed
  before any mutation marker was recorded.

The attempt directory is locked against concurrent consumers. Input identities,
Host/config pins, capture bytes, request bytes and approved signing identities
are checked on resume. Each read, lookup, and verdict uses fresh retained names.
No retained attempt is removed or renamed. A completed rerun rechecks exact
receipt/current state and does not mutate the session again.

Crashes during an incomplete pre-submit close preparation or partial enrollment
seal currently stop with retained evidence; the client does not reconstruct or
replace those partial artifacts automatically. A crash after a durable submit
marker, including before the first syscall, is deliberately uncertain until
exact native lookup selects an accepted original. An absent result never
licenses retransmission. A definite post-close refusal still reports uncertain
for the overall multi-step operation because reenrollment has not completed.

Current-state observations are point-in-time evidence. Future revocation or
lifecycle changes remain effective and must be checked by later dispatch.

## Validation scope

Focused Rust tests cover restrictive role preservation, non-UTF-8 refusal,
exact historical identity/generation, closed/revoked/mismatched capture refusal,
unique exact resource coordinates, and a lost close reply never causing a
second transmission. Existing enrollment tests cover lost op84 responses and
exact source request/receipt matching. This implementation is not yet qualified
by a complete live compatible-upgrade, reenrollment, and hosted-route journey.
