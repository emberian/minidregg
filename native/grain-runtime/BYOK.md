# Member provider keys and controller choice

Members use one credential interface for OpenRouter, Chutes, and other operator-listed OpenAI-compatible routes. The provider table remains the operator's endpoint/model allowlist. A member key does not grant Mini purse authority: the provider actor still needs its native resource/purse capabilities and credit.

For a member workspace whose socket is `ssh:DEST`, these commands reach sealed custody on the service host through the fixed SSH forced-proxy command. A local-socket workspace uses the local credential store. The remote client can pin the Host by digest without installing a Host executable.

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

The forced SSH wrapper accepts an optional trusted third argument, defaulting to `/etc/mini/provider-service.json`. Only the exact command `mini-provider-credentials-v1` selects credential service; arbitrary SSH commands remain refused. The service config is a canonical absolute root-owned regular file with root-owned, non-group/world-writable ancestors, readable by the service UID:

```json
{
  "type": "mini-member-provider-service-v1",
  "host": "/PINNED/bin/minidregg-host",
  "hostConfig": "/PINNED/deployment/config.json",
  "socket": "/SERVICE/public/mini.sock",
  "providers": "/etc/mini/providers.json",
  "credentials": "/var/lib/mini/credentials",
  "credentialsKey": "/var/lib/mini/custody/credentials.key"
}
```

The credential root is mode0700 and master key mode0600, both owned by the same internal service UID used by the controller. The selected native socket must support current-key status op144. The service sends a bounded single-use random challenge; the member signs the exact action and deployment pins. The server sends captured config/Host pins to native status, then rechecks current service/table/key bindings under its custody lock. Frames use nonblocking descriptors and one deadline. Errors and returned authentication metadata contain no bearer. Current-key status is a source observation, not an atomic native custody mutation; actual controller use independently rechecks current identity and stored grant epoch.

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
