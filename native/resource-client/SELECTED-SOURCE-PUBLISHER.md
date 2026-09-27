# Selected source publication

This path releases one explicitly selected **public-peerable** content atom. It
does not export a Mini Store prefix. The owner signs the canonical Release
preimage with `mini selected-release-sign`; the source Mini then separately
authorizes disclosure of that exact packet under its current `.delegateObject`
law. Recipient admission under its own current law remains a later operation.

With a source-matched Mini Host exposing the selected-source routes, use a new
owner-private directory for the source native signature:

```sh
mini selected-source-sign \
  --host HOST --config SOURCE-CONFIG.json --packet PACKET.bin \
  --delegate-capability CAPABILITY-ID --key OWNER.key --dir NEW-SIGN-DIR
```

The Host selects the current source content version and canonical signing
header. The client signs only those exact bytes and asks the Host to assemble
`NEW-SIGN-DIR/ingress.bin`. The directory also retains the packet, source spec,
header, signature, source root and image/config hashes. A signed query used to
select the content and this source publication signature serve different
purposes; a read alone does not authorize disclosure.

After the Host has authored `ARTICLE.eml` from the same packet, configure a
private protected fn POST endpoint and use a separate new state directory:

```sh
mini selected-source-publish \
  --host HOST --config SOURCE-CONFIG.json \
  --ingress NEW-SIGN-DIR/ingress.bin --article ARTICLE.eml \
  --state-dir NEW-PUBLISH-DIR --post-config PRIVATE-POST.json
```

The publisher pins the exact Host, config, ingress, article, certificate and
POST config. Before a network write, the Host strictly checks that the article
canonically carries the ingress packet, Mini confirms the source authorization
event, and an exact historical lookup agrees on all four receipt fields. The
publisher writes a durable POST attempt marker before contacting fn. It never
automatically posts again after a lost response, explicit uncertainty, conflict
or refusal. Re-entering the same state can finish a retained accepted response
without a second POST; unresolved states require operator reconciliation.

Mini source confirmation authorizes the selected disclosure; it is not an fn
delivery receipt. fn can inspect, reorder or withhold the article. A recipient
must extract the bounded authored source and verify the owner signature and
current recipient policy through its own selected-release admission route.

This workflow requires a source-matched Host image containing
`selected-release-source-plan`, `selected-release-source-assemble`,
`selected-release-source-check`, and source publication submit/lookup. A Host
binary predating any of those routes is unsuitable. No historical fn relay or
Mini receipt is evidence of confidential transport; this profile admits only
public-peerable selected bytes.

The 2026-09-27 client source checkpoint passed 53/53 focused resource-client
`cargo nextest` tests and `cargo clippy --all-targets -- -D warnings` in an
isolated copy. Its filesystem stub tests establish client recovery routing
after a truncated submit result and after an earlier absent lookup; they do
not establish native Mini installation or fn delivery. A native source event,
exact lookup and protected POST fixture still require a Host image containing
the new equality route.
