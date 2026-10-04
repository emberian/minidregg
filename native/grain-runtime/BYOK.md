# Member provider keys and controller choice

Members use one credential interface for OpenRouter, Chutes, and other operator-listed OpenAI-compatible routes. The provider table remains the operator's endpoint/model allowlist. A member key does not grant Mini purse authority: the provider actor still needs its native resource/purse capabilities and credit.

For a member workspace whose socket is `ssh:DEST`, these commands reach sealed custody on the service host through the fixed SSH forced-proxy command. A local-socket workspace reaches the box's key broker on its socket (`--broker CLIENT_CONFIG` names another). The remote client can pin the Host by digest without installing a Host executable.

```sh
mini key --action providers --dir MEMBER_WORKSPACE
mini key --action set --dir MEMBER_WORKSPACE --provider chutes --secret - < PRIVATE_KEY_FILE
mini key --action grant --dir MEMBER_WORKSPACE --provider chutes --runner PROVIDER_SUBJECT --model MODEL --per-call 100 --per-day 20 --until NATIVE_HEIGHT
mini key --action choose --dir MEMBER_WORKSPACE --provider chutes --model MODEL --runner PROVIDER_SUBJECT --task PROVIDER_TASK
mini key --action ls --dir MEMBER_WORKSPACE
mini key --action revoke --dir MEMBER_WORKSPACE --provider chutes --runner PROVIDER_SUBJECT
```

`--secret` accepts a private owned regular file or stdin; it never accepts a bearer argument. Repeating `set` replaces the sealed bearer and retains existing grants. Revoking without `--runner` first durably empties the grant list, then removes custody and counters; an interrupted revoke cannot restore grants when a key is replaced. A request already authorized may finish. Provider requests check current native member identity, exact grant epoch, model scope, expiry and caps before using a user credential. Old grants without a native epoch require an explicit current-member regrant.

Mini's hosted shell also exposes `key providers`, `key grant`, `key choose`, `key revoke`, and `key ls`. For stdin key entry use its one-verb invocation; the interactive shell refuses to consume subsequent shell commands as key input. There is no Unix shell requirement.

## Operator connection

Custody is the key broker's (`native/mini-keys`, account `mini-keys` under split
tenancy). The forced SSH wrapper `mini-socket-proxy MINI SOCKET [KEYS_CLIENT]`
answers exactly `mini-provider-credentials-v1` with `mini-keys relay`, a byte
splice to the broker that the root-owned client config names (default
`/etc/mini/keys-client.json`: `{"type":"mini-keys-client-v1","socket":...,"uid":N}`);
arbitrary SSH commands remain refused. A hosted session's `mini key` connects to
the same broker socket directly. Either way the client refuses an answer from any
uid but the broker's.

The broker config (`/etc/mini/keys/broker.json`, `mini-keys-broker-v1`, root-owned)
names the pinned Host and config, the public socket, the provider table, the
credential root and the seal key, and which uids and gids hold which role
(member, provider, discord, operator). The seal key is the broker account's 0600
file; the broker refuses to start if it, or any other secret it holds, is readable
by another account, or if a peer rule names its own uid. The broker sends a
bounded single-use random challenge; the member signs the exact action and
deployment pins. The broker asks the Store (op 144) whether the key is current
before and after namespace provisioning, under its custody lock, and acts only if
the epoch is the same both times. Errors, results and the audit log carry no
bearer. The Hermes controller never holds one: it gets a single-use ticket at
reserve time and the broker makes the provider call.

## Fresh controller activation

The member's signed choice fixes provider, model, member, provider actor, provider task and exact table digest. Provisioning intersects that choice with an operator policy bound to the exact template bytes:

```json
{
  "type": "mini-member-provider-provision-v1",
  "templateSha256": "SHA256_OF_TEMPLATE_BYTES",
  "routes": [{"provider": "chutes", "models": ["MODEL"]}]
}
```

```sh
grain-runtime provider-provision TEMPLATE OPERATOR_POLICY NEW_CONTROLLER
```

The template comes from the operator's genuinely fresh native source lifecycle, including native member/purse delegation. Provisioning changes only its selected provider/model. It takes the normal controller lock, queries each source task, and requires generation/status/reserved zero; an unused filesystem pathname cannot make a previously attached source fresh. It verifies the native tariff, current member, exact epoch/model grant and usable credential before publishing. An exact completed retry is idempotent; an interrupted query-only attempt resumes its exact intent. It never clones a live controller into an empty journal.

Production registration consumes the resulting exact controller at `/var/lib/mini/controllers/TASK/controller.json` through the canonical operator registration helper; it does not initialize a journal or infer member choice. Existing controllers keep their binding. Owner key rotation requires explicit new-key custody/regrant and the narrowly proven same-subject typed controller migration; editing a public-key field or resetting its journal is not recovery.

## Qualification and remaining integration

`journeys/byok-native.py --ssh` creates a separate native four-resource source, genuine local sshd forced proxy, synthetic provider and real controller/worker. It exercises signed choice, immutable provisioning, actual reserve/send/settle, replacement, revoke/no send, used-source refusal, challenge pin drift and native owner rotation. It uses synthetic secrets and loopback HTTP only. The matched c29 fixture is compatibility evidence, not qualification against a later common Host. Current-core integration, canonical service installation and the owner-migration continuation must be tested on their coherent pinned binaries before calling that deployment complete.
