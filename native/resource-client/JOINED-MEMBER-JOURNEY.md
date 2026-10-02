# One deployment, two members, apps and a resident

`joined-member-journey.py` is the reusable orchestration layer for the combined
member journey. It does not create a Store, enroll synthetic users, launch sshd,
start Hermes, or provision an unrelated SPK fixture. It uses two preprovisioned
forced-command **Mini shell** SSH sessions. There is no Unix shell offering.

Run on the deployment host, where the pinned manifest, public service config and
member workspace metadata can be read. `check` reads files only; it launches no
process. `run` performs actual member commands and explicitly configured service
owner hooks. This source was prepared without service launches or provider calls.

```
python3 native/resource-client/joined-member-journey.py check SPEC.json
python3 native/resource-client/joined-member-journey.py run SPEC.json --output /absolute/new-run
```

Output must be new. A failure stops the run and preserves command, stdout, stderr,
exit status, elapsed time, exact manifest and deployment identity. Never rerun a
timed-out mutation under a new identity to make it pass: use the member's retained
operation and exact lookup first. This harness deliberately has no automatic
restart-from-the-beginning option.

## Spec

Example shape (paths and digests must be supplied by the actual deployment):

```json
{
  "type": "mini-joined-member-journey-v1",
  "manifest": "/candidate/manifest.json",
  "manifestSha256": "SHA256",
  "deployment": {
    "config": "/deployment/pinned-config.json",
    "configSha256": "SHA256",
    "socket": "/run/mini/member.sock"
  },
  "prefix": "joined-rehearsal1",
  "timeoutSeconds": 300,
  "members": {
    "alice": {
      "subject": "ACTUAL_SUBJECT",
      "workspace": "/members/alice/workspace",
      "home": "/members/alice/home",
      "ssh": {
        "identityFile": "/operator/ssh/alice",
        "knownHostsFile": "/operator/ssh/known_hosts",
        "destination": "mini@127.0.0.1",
        "port": 2222
      }
    },
    "bob": {
      "subject": "OTHER_ACTUAL_SUBJECT",
      "workspace": "/members/bob/workspace",
      "home": "/members/bob/home",
      "ssh": {
        "identityFile": "/operator/ssh/bob",
        "knownHostsFile": "/operator/ssh/known_hosts",
        "destination": "mini@127.0.0.1",
        "port": 2222
      }
    }
  },
  "hooks": {
    "hermes": {
      "executable": "/candidate/owner-hermes-adapter",
      "sha256": "SHA256",
      "args": ["--resident", "/deployment/resident.json"]
    }
  }
}
```

SSH host keys must already be enrolled. Each authorized key must use the existing
`deploy/shell/mini-shell-ssh MINI HOST CONFIG SOCKET WORKSPACE HOME` forced command.
No remote system-shell command is sent. `whoami` checks the actual session's
subject, workspace, home and socket against the supplied member pins. Local
workspace/config checks and owner adapters assume operator-controlled deployment
metadata; this is not a new remote-attestation protocol. Ordinary signed reads,
admission, capabilities, laws and continuity remain Mini's existing authority.

The source manifest pins every core executable. The identity additionally binds
config hash, domain, genesis seed, canonical Store path and member socket. Each
operation rechecks those files. Owner hooks must preserve this identity and use
the same native deployment, not create a sibling Store with a similar config.
No credential bytes belong in the spec or hook arguments; supply custody paths.

## Connected member rows

The harness creates one fresh workroom from the actual stock template, invites
Bob with observe/mutate, exports/imports that invitation over the member shells,
and proves both shared names open one document. Bob writes and both read it;
Alice transcludes it and inspects its law. Bob's missing local control authority
is explicitly a client refusal, not mislabeled native admission evidence.

Hermes and SPK hooks receive these same member subjects, room identity and
document identity. After a supplied operator restart, Bob performs exact lookup
of the retained write and Alice verifies the unchanged content; SPK must retain
the same app ID and data. A separate sacrificial document receives a deny-all
law. Its owner's attempted write and attempted law repair must each receive a
native `law-denied`, at preparation or submission. Finally Alice revokes Bob's
room grant, and Bob's named document read must receive a native grant refusal.

The actual built-in sequence is not yet qualified against the final joined
deployment. Unit tests cover dangerous false positives and identity mixing;
they are not substituted for the eventual joined run.

## Service owner adapter contract

Configured executable is invoked without a shell:

```
OWNER_ADAPTER [configured args] --request ABS_REQUEST.json --result ABS_RESULT.json
```

Request type `mini-joined-member-hook-request-v1` carries `identity`, `manifest`
(absolute pinned manifest path), `deployment` (config/configSha256/socket), `role`,
`phase`, `members` (subject/workspace/home), room name, `roomTarget`, and later
`documentTarget` and `appId`. The evidence directory is private to this run.
Result must have type `mini-joined-member-hook-result-v1`, unchanged `identity`,
matching `role`/`phase`, `status:"pass"`, and nonempty `artifacts` containing
absolute `path` and `sha256`. Hermes/SPK also return the same `roomTarget` and
ordered `subjects:[alice,bob]`. The adapter owns signed semantic verification;
the harness checks its identity and retained evidence rather than reimplement it.

Required adapters:

| Role / phase | Additional result / obligation |
| --- | --- |
| `paid-entry` / `run` | `rail:"solana-mainnet"`, `creditedSubjects:[alice,bob]`; retain verified payment/enrollment/credit receipts. No fixture may claim this rail. |
| `hermes` / `run` | `providerMode:"real"`, `delivered:true`; actual registered hosted resident, bounded job, current authority and retained paid completion/delivery receipts. |
| `spk` / `before-restart` | `appId`, `writeRead:true`, `shared:true`; actual same-Store app and both members' live sessions, retained browser/traffic evidence. |
| `restart` / `run` | Operator-owned restart of this deployment, preserving Store and member/socket pins; retained stop/reopen evidence. No re-genesis. |
| `spk` / `after-restart` | Same `appId`, `retainedData:true`; verify actual data through an admitted live app session. |
| `growth` / `run` | Actual `acceptedRecords>=1000`, `writeSeconds<=5`, `coldReopenSeconds<=60`, all measured on this deployment. |

Absent adapters create blocked rows; provisioned-member runs may proceed to find
composition bugs. Exit 1 means failure, 2 means required rows remain, and 0 is
reserved for no outstanding rows. The script always retains a pending-human row
and `barComplete:false`: automated SSH is not the two real friends' transcripts.
The result lists every wait over five seconds for investigation.

## Concrete integration seams found while preparing this harness

* **Hermes:** `grain-runtime hermes-room resident RESIDENT_CONFIG` is the real
  source-owned resident driver. It uses the controller's supplied host/config/
  socket and room workspace/home. The historical `j14.sh` and native resident
  completion-cut setup create fixtures; they cannot serve as joined adapters.
  Founder HOME/hermes/node.json must name both the registered recipient `subject`
  and `task`. The supplied operator configuration owns this binding. Deployment
  lacked summon outbox-to-registered-inbox delivery; the controller
  lifetime owner is implementing that receiver. Manual handoff copies cannot
  make this row green.
* **SPK:** `scripts/spk-platform/ws-continuity-launch.py` materialize/run creates
  a fresh Store with fixed owner/member/grant/funding IDs. It is not an attach API.
  `ws-continuity-journey.py CONFIG --output RESULT` can reuse supplied live A/B
  sessions and source-backed snapshot/revoke hooks to exercise real EtherCalc
  traffic, but an owner adapter must first provision arbitrary supplied members
  against this Store. Its traffic report is not a human browser transcript.
* **Payment:** source `mini join --wait --memo-version v2 --host HOST --config
  PUBLIC_CONFIG --dir JOIN --signature TX` can finish retained paid entry; its
  owner must validate resulting workspace/config/profile/continuity/account and
  receipts. Existing jpay fixtures create their own Store and synthetic Solana
  responses. A real mainnet deployment configuration remains necessary.
* **SSH:** the existing shell forced command is used directly. BYOK's alternative
  `mini-socket-proxy` native-frame transport is useful but does not implement the
  Mini-shell command transport expected here; do not silently substitute it.

The overall bar remains cv `01a0f9c0-521b`; first hour `01a0f9c0-55af` is an
intermediate rehearsal. This harness connects their mechanics without lowering
the paid-entry, real-provider, live-app, growth, deployed-node, or human-use rows.
