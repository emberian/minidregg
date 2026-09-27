# Lifecycle completion authoring checkpoint

This source-only checkpoint adds the operator-facing authoring path for event 18.
It does not admit a completion, verify a custodian signature, or authorize a
physical launch.

- `Host/ApplicationLifecycleCompletionAuthoring.lean` SHA-256
  `14663715daac255ea59f60236bdefcb94bf4c29ea36192a347dcb3b9cfa6b771`.
- `Host/Json.lean` SHA-256
  `811ea2ad11f4ea64981bd90f648ba77a5435c8f1b6f0c8661e4553ff5ed5612a`.
- `Kernel/ApplicationSpkPackageIdentity.lean` SHA-256
  `f6e00b2cd580e0a48fd9c10601ea1ad88634e72004a4520fda18836448f55d95`
  adds the exact resident image identity from raw signed-SPK SHA-256.
- `Kernel/ApplicationLifecycleResidentProfile.lean` SHA-256
  `6354a3cc0847e902828438951d387da8561be4f3866729494e1d87fc83409d27`
  checks that image identity and the generation-specific systemd unit identity.
- `Host/ApplicationLifecycleClaimInspection.lean` SHA-256
  `1d026e460d1e63498e49a59035c1fdab6d230f2178b5ccbd38a30d00ef26cd34`
  refuses to present a nonresident claim as physically launchable.
- The independent Persvati overlay compiled the new module, then `Host.Json`,
  against the frozen lifecycle completion source and current app dependencies.
  The final serialized five-module pass was descriptor, resident profile, claim
  inspector, completion authoring, then Host.Json; all PASS. Their OLean SHA-256
  values are respectively `9dfeeb2ef82a8dd37f881a9aa7eac1914b1bc847e60997b91c60643f54a20522`,
  `1e4bfcc6a6b40653a3d28ed2a20033b02cb5fe23372a9fed11429975940dbc9c`,
  `495b8325b146f7138ef17816359017ee98dcf5465554abed80d4bbaff51e00fa`,
  `b1a1ce0b452ef0cb46dd0704eae737fe6abc67bd5804592bbbf2bc53a691f59a`,
  and `37a45eceb8cb0317447c66fca83a2bc31184e416741f42e302360fe21449c2c2`.

The seven `application-lifecycle-completion-*` author kinds form a strict sequence:
`report` binds raw BEGIN-v2 and committed claim-v2 bytes to the host's observed
unit, image, process facts, nonce, and source-derived prospective manifest;
`signing-frame` rechecks the BEGIN/profile and emits the exact custodian preimage;
`signed-report` packages a detached 64-byte signature; `source` adds roots,
capabilities, and optional old package atom from native observations; `command`
derives the management command; `signed-command` packages target, observation,
and authority envelopes with the source-required incidence counts; `ingress`
requires its exact command bytes in the signed
command before encoding the event-18 carrier. Fresh native admission must still
verify the configured custodian key, signatures, current law and grants, original
admitted claim, current roots, and one-image CAS. The physical observations are
operator attestations, not Mini-owned measurements.

The `application-lifecycle-resident-begin` author kind validates and echoes an
already signed BEGIN-v2 frame. It and the claim inspector/completion report plan
require `imageIdentity = ASCII DREGG/SPK-IMAGE/v1 ++ descriptor.rawSha256` and
`processIdentity = UTF-8 mini-spk-aAPP-gGEN.service`. Generic BEGIN-v2 admission
and historical replay remain unchanged; these are physical adapter constraints.

`Host.Main` op38/39, a source-matched native binary, and physical signer
integration are separate pending gates. The private resource-client broker now
allows bounded op38/39 and still refuses them on its public socket;
`native/resource-client/src/transport.rs` SHA-256
`11e1828ffbcf3f795ca9142824ceb01409973047ddabeddb66fba7c793304332`.
The focused `cargo nextest` operator-only route test passed 1/1; this is routing
shape validation, not an event18 Host admission result.
