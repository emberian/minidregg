# Hosted provider custody for an AgentGrain

Status: next implementation contract, not a deployed provider path. This note
was checked against the local Mini and upstream Hermes trees on 2026-09-26. It
does not choose a model, spend a provider key, or claim that provider billing is
already measured by Mini.

## The existing receiving paths

The unmodified Hermes ACP executable is a stdio server. It has `--check` and
setup flags, but no per-session `--base-url` or `--api-key` flag
(`~/pug/hermes-agent/acp_adapter/entry.py`, `_parse_args`). A new ACP session
loads `model.default` and `model.provider` from Hermes config, then calls
`resolve_runtime_provider` and passes its `base_url` and `api_key` into
`AIAgent` (`acp_adapter/session.py`, `SessionManager` agent construction).
The OpenRouter resolver accepts a configured `model.base_url` as a mirror when
`model.provider: openrouter`, and chooses `OPENROUTER_API_KEY` for that context
(`hermes_cli/runtime_provider_backends.py`, `_resolve_openrouter_runtime`).
Its resolver defaults this route to Chat Completions
(`hermes_cli/runtime_provider_backends.py`, `_resolve_openrouter_runtime`). Thus a minimal,
operator-pinned Hermes home can point upstream Hermes at a local compatible
gateway with a **gateway credential**. It must contain no BYO OpenRouter key,
other provider credentials, fallback routes, or model-switch authority. The
worker can read the gateway credential; its scope and expiry are enforced by
the gateway, not by the string's secrecy from Hermes.

Mini's `grain-runtime` already reserves a configured parent allowance through
a signed `grain-intent` before spawning Hermes, records `parent_hold`, and
queries the signed parent AgentGrain state (`native/grain-runtime/src/main.rs`,
`Runtime::hermes`). The Lean transition law in `Kernel/AgentGrain.lean` permits
the reserve from attached state and a settle from reserved state; it does not
provide a second nested reserve on the same already-reserved parent. The
runtime currently settles the operator-configured `charge`, explicitly not a
provider invoice. Its separate `toolTask` shows the reusable pattern: another
AgentGrain reserves and settles an allowlisted publication, with an unchanged
parent witness in the same native transaction. `Host/Json.lean`'s `grainSource`
accepts `parentWitness` on a grain operation and `AgentGrain.Operation.command`
includes that incidence; the currently wired Rust `transition_as` adds the
witness only when publications are present. Hard detach signals the owned
process group first, then fences the tool and parent grains
(`Runtime::disconnect`); an interrupted ACP outcome is retained as uncertain.
The Linux worker launcher
(`deploy/grain-host/bwrap`) keeps controller state and custody keys outside the
sandbox. Its current `--network host` option gives the worker ordinary host
network access, so merely changing Hermes' base URL does **not** establish
that all worker provider traffic passes through the gateway. Keeping the BYO
key outside the worker already protects that key from direct disclosure by
this mount boundary; a network allowlist is needed for the stronger traffic
confinement claim.

## Smallest custody path to build

Run an OpenAI Chat Completions compatible **Rust receiving service owned by
the Mini controller**, not a fork of Hermes. The service holds the user BYO
provider key in controller-only storage, pins the provider origin and the
operator-selected model, and presents a worker-reachable local `/v1` endpoint.
The unmodified `hermes-acp` receives a minimal per-task `HERMES_HOME` with
`model.provider: openrouter`, that endpoint as `model.base_url`, and a scoped
gateway token as `OPENROUTER_API_KEY`. Verify the resolver chooses this route
in an offline upstream Hermes test before any hosted call. Disable credential
pool or fallback paths in that worker home; otherwise a provider resolution
failure could escape the intended gateway. The gateway must refuse model
switches outside the pinned allowlist, unrecognized paths, and request bodies
over its explicit bound. It should preserve the request and upstream response
bytes needed for uncertain-result reconciliation without recording the BYO key.

Give the provider gateway a **separate, pre-funded `providerTask` AgentGrain**
with a controller-held Mini signer, a fixed operator reserve and charge per
request, and a parent witness grant pinned to the current prompt generation.
For each request, the controller attaches that task if necessary, records an
exact pending attempt, and submits a native **joint provider reserve plus
parent no-op witness** before any upstream send. Mini's generic receiver then
checks the provider task's current balance and grant together with the
parent's still-reserved generation. A refused reserve means no provider send.
The gateway also checks the active local prompt lease immediately before
forwarding. After an unambiguous response it settles the provider task with
the fixed operator charge; an ambiguous send or reply keeps the reservation
and exact attempt for reconciliation. The amount and its unit must be pinned
with the model choice. One provider task admits one outstanding request; the
gateway queues or refuses concurrent provider calls until that reservation is
settled. Provider usage is retained evidence, not an invoice
attestation or authority to settle a different charge.

The parent prompt allowance and provider purse are **independent budgets**.
The parent covers its existing prompt lifecycle; the provider task covers
per-request provider dispatch. A parent witness binds lifecycle/generation,
not a transfer of allowance or a proof that the two budgets add to one pool.
Existing Lean `AgentGrain.Operation.command`, `parentWitness` parsing and the
generic joint receiver appear sufficient for this fixed-charge reserve. That
must be demonstrated with a native accept/refuse test before calling it
implemented. A new Lean law/proof would be needed for a shared budget,
automatic transfer, or charge derived from provider usage. No local Rust
counter should substitute for a signed provider-task reserve.

On hard detach, the controller closes the prompt lease and cancels all local
HTTP streams before or with its existing child kill/fence path, then fences
the provider task as a distinct authority. A request
already sent upstream can still incur a charge after local cancellation; its
exact attempt, send boundary, response state, and uncertain outcome stay in
private durable state. Its provider reservation remains held or fenced until
exact lookup and operator reconciliation; reattach must not automatically
replay that request.
The gateway must reject a token after generation change or prompt end, even if
the worker process or a copied token survives. A soft detach may let the
current prompt finish under the held allowance, matching current grain mode.

## Rust interfaces and order of work

Keep signing and journal mutation in the existing controller. A narrow
interface is `ProviderRequest { prompt_operation_id, model, request_digest,
byte_length }` sent from the gateway to the controller, returning a one-use
`ForwardPermit` only after a signed provider reserve with the exact parent
witness. `ProviderAttempt` records that native reserve attempt, permit, exact
outbound bytes or their private retained file, send state, upstream
response/usage bytes when present, fixed settlement attempt, and cancellation
uncertainty. The gateway must recheck cancellation immediately before sending
and serialize that edge with the hard-detach signal. A permit is consumed
once; a repeated body needs a new Mini reserve. Do not let a worker-supplied
generation, estimate, target URL, provider key, or Mini capability become
authority.

This is a new Rust receiving path, not a second semantic engine. Add
`providerTask` config, signer and independent pending/hold journal slots;
`transition_as` currently has only parent/tool pending selection and only
constructs a parent witness for nonempty publications. Generalize it to a
named authority and an explicit witness for the provider **reserve**. The
normal settlement may carry the same witness; recovery after a parent hard
trip must remain possible through the controller's separately governed
provider-task right without pretending the stale parent witness still passes.
The existing tool task and its publication charge must stay independent.

After the actual grain receiving gates, add a private provider listener and
prompt lease to `grain-runtime`, with a fixed worker route from
`deploy/grain-host/bwrap`. An OS network allowlist or dedicated namespace must
allow the gateway and deny direct provider egress before claiming all provider
traffic is mediated; it is distinct from keeping the BYO key outside the
worker. Then add the signed provider-task reserve, bounded request/response
journal, settlement and fence paths. Run a local fake upstream receiver to
prove: no BYO key reaches the worker, an unforked Hermes ACP request reaches
the gateway, an insufficient provider purse or stale parent witness refuses
before upstream delivery, hard detach stops the worker and rejects a late
token, and an ambiguous upstream reply remains reconcilable. Only then use an
operator-selected real provider/model and BYO key for a separately recorded
receiving test.

This path gives every provider request a Mini-authorized fixed allowance. It
does not make Mini the provider biller: exact provider metering and
invoice-based settlement remain separate obligations.
