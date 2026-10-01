# Hermes provider keys: whose key pays for a Hermes call

Hermes never holds a model-provider key. Each Chat Completions request Hermes
makes goes to its controller's gateway. At reserve time, the controller picks
**one row of the operator's provider table** and **one bearer** for that
request. The row's `credential` kind says where the bearer comes from, and it
is also the **route** the purse records and is charged by:

| `credential` (route) | bearer | what gates it | what the purse pays |
|---|---|---|---|
| `user` | the friend's own key (`mini key set`) | the friend's grant naming this Hermes runner: a per-call `max_tokens` ceiling, calls per UTC day, and a last block height | the user route's per-operation fee, nothing else: the provider bills the friend |
| `pool` | the operator's key (`mini key … --pool true`) | the row's `caps` (per-call `max_tokens`, calls per UTC day per runner) and the purse: Mini must admit the provider reserve (PAY.md §2.7) | the pool fee plus the metered tariff |
| `homelab` | no `Authorization` header at all | the purse (a homelab endpoint on the operator's own network) | the homelab fee plus its metered rates |

A call with no payer (a `user` row and no key or grant) is refused before
anything is reserved.

The row is the task's pinned `provider`, or else the first row that lists the
task's model. **Nothing ever falls through from one payer to another.** A
friend whose row needs their own key, and who has none, is refused
`no-credential`; they are never silently moved onto the pool. Hermes, which
is an untrusted worker, cannot choose the row either.

## Custody: what "hosted custody" means here

> **A provider key you give Mini is held by the box.** It is sealed at rest
> (ChaCha20-Poly1305 under `/etc/mini/credentials.key`, bound to your subject,
> your workspace's public key and the provider name). A copy of
> `/var/lib/mini` (a backup, a tarball) therefore does not contain a usable
> key. But root on the box, and the `mini` service user that runs Hermes, can
> unseal it, because Hermes has to use it. This holds for every friend,
> including tier-B friends whose Mini signing key never leaves their laptop:
> *that* key is not on the box, but a provider key you `key set` is, by your
> choice. Give Mini a key you can revoke at the provider, with a spend limit
> set there.

Your credential lives in a directory named by your subject **and the public
key of your workspace's signing key**. A workspace that only *claims* your
subject number has a different key, so it lands in a different directory: it
cannot read, replace, grant or revoke your credential. The controller looks
only under the subject and public key that ember pinned for your Hermes
(`onBehalfOf`).

## What ember does (once per box)

As root on the box:

```sh
install -d -m 0700 -o mini -g mini /var/lib/mini/credentials
head -c 32 /dev/urandom | install -m 0600 -o mini -g mini /dev/stdin /etc/mini/credentials.key
install -m 0644 -o root -g root providers.json /etc/mini/providers.json
```

- **Back up `/etc/mini/credentials.key` separately from `/var/lib/mini`, or
  not at all.** Without it, the store is unreadable. The cost of losing it is
  that every friend runs `key set` again. Nothing else is affected.
- **`/etc/mini/providers.json` must be owned by root and not writable by group
  or world.** The controller refuses any other table. The table decides where
  friends' keys and the operator's money are sent, so the `mini` user must not
  be able to rewrite it.

Example table (`type` and every field are required; `caps` exactly on a
`pool` row):

```json
{"type":"mini-provider-table-v2","providers":[
  {"name":"openrouter","kind":"openai-compatible",
   "endpoint":"https://openrouter.ai/api/v1/chat/completions",
   "models":["anthropic/claude-sonnet-4.5","qwen/qwen3-coder"],
   "credential":"user"},
  {"name":"pool","kind":"openai-compatible",
   "endpoint":"https://openrouter.ai/api/v1/chat/completions",
   "models":["qwen/qwen3-coder"],
   "credential":"pool","caps":{"perCall":"4096","perDay":"200"}},
  {"name":"homelab","kind":"openai-compatible",
   "endpoint":"https://inference.tailnet.example/v1/chat/completions",
   "models":["bonsai2-27b-ptq1"],
   "credential":"homelab"}]}
```

**Rules for the table:**
- **Endpoints.** An endpoint is one exact Chat Completions URL, either
  `https://` or loopback `http://127.0.0.1:PORT`. It has no query string and
  no userinfo.
  - A plain-HTTP tailnet address is refused. Put the homelab behind
    `tailscale serve` (which gives it HTTPS), or use a loopback tunnel.
- **No prices in the table.** The Host profile's per-route tariff (below)
  prices every call; the row only names the route. A v1 table (a row
  `tariff`, or `credential: none`) refuses to load.
- **`caps`** on a `pool` row: `perCall` is the largest `max_tokens` one call
  may ask for (also never above the task's `maxOutputTokens`, which the hold
  covers), `perDay` the calls per UTC day, per runner.

**The pool is optional.** Set it only if you want to fund Hermes for friends
who bring no key:

```sh
sudo -u mini mini key --action set --pool true --provider pool --secret - < pool-key.txt
```

Its spend is bounded by each Hermes grain's purse. A pool request whose
reserve Mini refuses gets `no-credit`. Put a spend limit on the pool key at
OpenRouter too.

**Each Hermes controller** (`/var/lib/mini/hermes/controller.json`) needs these
fields in its `providerTask`:

```json
"providers":"/etc/mini/providers.json",
"credentialsRoot":"/var/lib/mini/credentials",
"credentialsKey":"/etc/mini/credentials.key",
"onBehalfOf":{"subject":"21","publicKey":"<the friend's owner.publicKey from key set>"},
"provider":"openrouter"
```

- **`onBehalfOf`:** the friend this Hermes serves. Omit it for a Hermes that
  only uses `pool` or `homelab` rows.
- **`reserve`, `maxInputTokens`, `maxOutputTokens`:** the hold of a metered
  (pool or homelab) call and the token ceilings it must cover: `reserve` ≥ the
  route's fee + the metered charge at the ceilings, or the call is refused
  before anything is reserved. A user-route call holds exactly the user fee.
  There is no `charge` and no `metering` field any more: every call is charged
  by the Host's route quote.
- **`provider`:** optional. It pins the row, for example `"pool"`.
- **The runner.** The friend's grant names the provider task's `subject` (the
  runner). Tell the friend that number.

Then run `systemctl enable --now mini-hermes`. The unit is
`deploy/hermes/mini-hermes.service`. It has no key and no `EnvironmentFile`.

## What a friend does

These commands run over ssh to the box. They are verbs of the hosted shell, so
they work for tier-B friends too.

```sh
ssh mini@BOX 'key set openrouter -' < my-openrouter-key.txt
ssh mini@BOX key grant openrouter 9 --per-call 4096 --per-day 200 --until 2000000
ssh mini@BOX key ls
ssh mini@BOX key revoke openrouter 9      # stop one runner
ssh mini@BOX key revoke openrouter        # delete the key and every grant
```

- **`key set`.** It reads the key from stdin. Use only the one-verb form shown
  above, never inside an interactive shell session, because the session owns
  stdin there. It prints `owner.publicKey`. Send that value to ember, who pins
  it as your `onBehalfOf`.
- **`key grant`.** It names the runner (Hermes's provider subject, which ember
  tells you) and three limits:
  - `--per-call`: the largest `max_tokens` one call may ask for.
  - `--per-day`: calls per UTC day.
  - `--until`: the last block height at which the grant is usable.
- **`key ls`.** It prints provider names and limits, never key values.

**When a call is refused**, Hermes gets a named refusal (HTTP 403 or 402,
`error.code`), and nothing reaches the provider:

| code | meaning |
|---|---|
| `no-route` | no table row lists this model (or the pinned row does not) |
| `no-credential` | your row needs your key, and there is no key or no grant for this runner |
| `grant-expired` | the signed height is past your `--until` |
| `per-call-cap` | the request's `max_tokens` is absent or above your `--per-call` |
| `per-day-cap` | today's calls reached your `--per-day` |
| `no-credit` | the purse refused the reserve (402) |

## Charges: the Host's per-route tariff

The Host profile pins one tariff per provider task, with a row per route
(`providerMetering.tariff` or each `providerServices[].tariff`; credit units,
one credit per purse micro-unit):

```json
{"version":"1","model":"qwen/qwen3-coder","routes":{
  "user":{"perOp":"EMBER_USER_PER_OP"},
  "pool":{"perOp":"EMBER_POOL_PER_OP","inputMicroPerMillion":"EMBER_POOL_IN","outputMicroPerMillion":"EMBER_POOL_OUT"},
  "homelab":{"perOp":"EMBER_HOMELAB_PER_OP","inputMicroPerMillion":"EMBER_HOMELAB_IN","outputMicroPerMillion":"EMBER_HOMELAB_OUT"}}}
```

- **`user`** (your own key): the purse is charged only `perOp` per call. Your
  provider bills you; Mini's purse never sees a token count.
- **`pool`**: `perOp` plus `ceil((in·inputMicroPerMillion + out·outputMicroPerMillion)/10⁶)`.
- **`homelab`**: the same shape as pool, at its own rates.
- **The route is a kernel fact.** A provider purse born under this tariff
  carries a route field: the reserve records the route the controller chose
  (with the bearer, from the same table row), and the settle is charged by
  that recorded route. A call reserved as pool cannot settle as a user call
  (`Kernel/ProviderRoute.lean`).
- **The reserve is still a real hold**, on every route. It is how an uncertain
  send is never resent.
- **The fees are fixed at the purse's birth.** The purse's law carries the
  per-operation fees the Host pinned when it was born. A Host tariff with
  different fees refuses the user-route reserve (its hold must equal the law's
  fee) and fails a metered settle closed; a fee change means a new purse.
