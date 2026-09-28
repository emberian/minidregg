# Accepted event27 lifetime route renderer

`scripts/spk-platform/prepare-lifetime-route.sh` prepares the two private v3
route files from one verifier-selected accepted event27 grant. It requires an
exact retained `mini agent-lifetime-grant-{plan,seal,submit,lookup}` attempt,
the lookup's `lookup-NNNN.outcome.json`, a protected operator-pins JSON, a
source-qualified successor Host path/SHA, and a new private output directory:

```sh
scripts/spk-platform/prepare-lifetime-route.sh \
  QUALIFIED_HOST CONFIG.json GRANT_ATTEMPT \
  GRANT_ATTEMPT/lookup-NNNN.outcome.json OPERATOR_PINS.json \
  NEW_OUTPUT_DIR EXPECTED_HOST_SHA256
```

The operator pins name `workroom-app` or `coding-app`; they supply the route
socket/UID/unit, fixed `/repo.git/` path, manifest/capability/purse selectors,
and the app, grant, and payer signer pins. The source projection supplies the
app/session/subject/ticket/parent/grant identities, both original event22 and
grant event27 receipts, the grant digest and initialized root, and exact
original descriptor bytes. The renderer hashes those source descriptor bytes
for `originalDescriptorSha256`; it never derives a native grant digest or
receipt. It compares the route name and purse/subject to the fixed A/B resource
allocation before emitting `controller-route-v3.json` and
`resident-custody-v3.json` (0600). A `SHA256SUMS` file pins all source inputs,
both Host images, and the generated files.

The original grant Host image and the successor inspection Host image are
separately SHA-pinned. The script re-inspects retained op73 outcome bytes with
the successor Host, then invokes its new
`inspect-accepted-agent-lifetime-grant` route. That route must replay-verify
the exact event27 under the same protected Store config and return the
verifier-selected original. Shell custody checks, operator pins, and retained
receipts are comparisons only; the qualified Host route is the acceptance
authority. A failed inspection leaves the owner-private output attempt for
review and never creates a replacement route.

The script decodes the source `canonicalIngressHex` to a protected binary
artifact and compares it byte-for-byte with the retained sealed `call.bin`.
No full ingress or descriptor hex is passed as a command-line argument;
real frames can exceed Linux's 128 KiB per-argument limit.

After accepted lineage exists, an operator reviews `controller-route-v3.json`
as an entry in grain-runtime `toolTask.allowedApplicationLifetimeRoutes`, and
uses `resident-custody-v3.json` as the named v3 agent custody input to
`prepare-resident-config.sh`. The controller's `LifetimeRoutePin` validator and
the resident's `LifetimeCustodyV3` validator recheck their exact schemas and
source-derived dispatch plans at use. This script does not modify either live
config, mint an event26 permit, start GitWeb, or send fd3 traffic.

Validation of source SHA
`e5b0d4b8a448043dadefec736043676c574edc481ec91225f781c1c75c7a57cf`:
ShellCheck and `sh -n` PASS. A private hbox Linux schema-only fixture exercised
the actual shell renderer: positive A projection and descriptor-byte SHA,
rejection of a workroom/coding cross-route, and rejection of altered retained
op73 outcome JSON. A separate 98,304-byte ingress fixture passed exact binary
comparison; its 196,608-character hex projection would exceed Linux's
per-argument limit if passed through `jq --arg`. These fixtures used a labeled
stub Host solely to test shell
projection; it supplied no Store, native receipt, key authority or qualified
Host. The r3 Store has no accepted app/ticket/grant lineage, so there has been
no production invocation or same-Store agent request.
