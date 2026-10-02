# Key-only welcome continuity

A key-only join establishes its first continuity baseline from its admitted
enrollment receipt. This requires no account, resource grant, or temporary
entitlement. Receipt counts already use accepted-count coordinates; observation
height normalization does not apply.

The sponsor's `enroll --action welcome` now includes `ingressHex` and
`ingressSha256` from the exact retained sealed enrollment. These contain public
signatures, not either participant's private key. An older welcome can be
regenerated from its existing sealed attempt without resubmitting enrollment.

The participant runs:

```sh
mini join --remote DEST --key KEY --welcome WELCOME.json --dir JOIN-ROOT \
  --verifier /absolute/pinned/local/minidregg-host
```

The portable source verifier is explicit and retained by path and image digest;
there is no PATH fallback. It must support local enrollment/Plan/outcome inspection,
`profile`, and `continuity-verify`. Remote transport still pins the offered Host
image and exact configuration. Native binaries for the participant's platform
remain a packaging responsibility.

Before first trust, join validates the retained offer/config and local public key,
retains the verifier/transport/request pins, and uses the local source Host to
decode the Plan and sealed ingress. It checks the retained possession signature
and exact command bytes, signature bytes, subject, key ID and public key. Rust does
not decode semantic ingress or receipt bytes itself.

Only public operation 89 is used to resolve enrollment. It is a read-only lookup
of the exact ingress; absent, refused and uncertain outcomes do not submit work.
The local source Host decodes the returned outcome. All four receipt fields must
match the welcome: transaction ID, event ID, accepted count and world root.
The confirmed frame and authenticated receipt provenance reach durable storage
before creating the fresh workspace.

`FreshBaseline::AdmittedReceipt` then uses the existing fresh-onboarding state
machine: retain the exact source-verified op151 candidate before installing anchor,
settings and enablement. There is no readable-reference requirement. Before this
proof can enable custody, `join/workspace-created.json` records creation outside
the workspace; loss of the entire workspace therefore cannot become first use. Interrupted
join resumes its retained confirmed frame/candidate; completed join delegates to
current custody without a new lookup or first trust. Lost custody fails closed.
The existing `init_fresh` reference API remains unchanged; key-only join uses
`workspace::init_fresh_receipt` after authenticating admission.

Evidence lives in `join/welcome-pin.json`, `welcome-ingress.bin`, individual lookup
frames, `welcome-confirmed.frame`, and `authenticated-receipt.json`, plus the shared
workspace continuity files. Changed requests require a distinct join attempt;
uncertainty retries the same retained request with lookup only.

`welcome-continuity-journey.sh HOST MINI STORE CREDENTIAL_VERIFIER NEW_RUNROOT`
uses the existing genesis fixture and real source Host/public socket proxy. A local
SSH-process shim records version-2 envelope operation codes; this checks the remote
client/proxy path, not SSH authentication or a WAN deployment. It covers absent
lookup without submission, transport failure, injected refusal, forged receipt, source-assembled
wrong signature/command, explicit verifier selection, a grant-free baseline,
interrupted proof recovery against an already advanced world, repeat recovery,
and individual or whole-workspace custody-loss refusal.
