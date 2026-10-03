# Discord shared-world entrance and durable mirror — 2026-10-03

The entrance now presents the native member projection through `/mini-world`,
retains actor-bound interaction custody across restart, and uses the native
operation record for imported room messages. The mirror drains retained pages
without discarding an overfull batch. An uncertain outbound Discord publication
is retained and blocks reposting until operator reconciliation.

## Executed evidence

The focused Rust suite passed **30 tests**: 19 library, 5 mirror and 6 endpoint
checks. This includes a 115-message channel backlog with restart after every
bounded drain, 45 outbound entries, a lost publication reply that is not reposted,
a crash after retained publication success before cursor advancement, exact
interaction binding, accepted-job recovery, UNKNOWN execution, roster revocation
and status isolation between two users mapped to the same hosted session.

The composed scenario used fake signed Discord requests and a loopback fake API,
but the actual forced shell wrapper, Mini client, native Host, Store and signature
verifier. It created a new domain, keys and Store, enrolled a separate bridge,
created a room/document and admitted 23 source messages. It then checked:

- `/mini-world` shows that user's held room/document; selecting the room reports a
  signed source-checked observation.
- `/mini doc show notes` reads the same admitted document. An unrostered user gets
  no discovery result. Restarting the entrance returns the retained answer for the
  same interaction without rerunning its line.
- All 23 source room messages cross into fake Discord over bounded source pages.
- One fake Discord user's message is admitted under the **bridge's** Mini subject,
  preserving the external author in `via`.
- Rewinding only the inbound cursor and delivering that source message again
  produces **one** native stream append. Its retained operation bytes are unchanged.

This is the historical **ordinary** receiving profile pinned below, not
qualification of the newer Objective Bend/private/consent native profiles, a real
Discord deployment, or exactly-once external publication. An initial failed run
found native chat's whitespace-separated path grammar: shell quotes were literal
path bytes. The corrected mirror sends constrained absolute request paths and
rejects whitespace in its configured home. The passing run resumed only its own
fresh fixture, with the same source-world and artifact pins. Original worlds and
foreign grants were not copied or modified.

## Artifact pins and custody

| Artifact | SHA-256 |
| --- | --- |
| `mini-discord` | `5451125ca7b6179362258e193f1fe5c87cb10b2f53308ffa17cfb4e933b0ff58` |
| `mini-discord-mirror` | `182485733a79508ab23b5131356ed111e34840e2541bec5a47e9890e42d2c7ec` |
| Native Mini client `mini-ui-joined` | `1ad2ebe3688bcc602be8350a5877a0bc2f951cc1b75dc26253941d0ccefbbb24` |
| Native Host | `740545eee8f59199e953c4053d8df24054bb6b54db4a9ee6c8da1873f1a42f50` |
| Store | `176c4cfe236e73854d68b0c965e61e3fcc5a46f0e42d3c5a1d1d9838da682aca` |
| Signature verifier | `a1e604a4576aab2b2f1422e9a14f9171472235fcf1b5910d3f545bfa1b5b2fd7` |

Retained development artifacts on hbox are rooted at
`/home/hbox/workbox/discord-world-20261003/`: `tests-r2.log`,
`native-run-2/result.json`, `native-resume-3.log`, and the private fresh fixture
`native-run-2/`. Source capsule r1 and its canonical inbox row preserve the earlier
reviewable checkpoint; r2 carries the native grammar fix and this evidence.
Do not publish the fixture: it contains test custody keys and configs.

The successful resumed native transport run took 96.3 seconds, peaked at
163.4 MiB and used no swap under an 8 GiB / zero-swap / 180-second guardian.
The original fresh setup and first navigation checks are retained in the same
result ledger. Final source additionally releases connection slots with an RAII
guard on worker panic and improves scenario resume/pin bookkeeping; these do not
change the native request protocol. The focused Rust suite was rerun for the
RAII change; the native composed run was not repeated. The standalone test/build target is isolated from common outputs.

Run instructions and exact residuals are in [the deployment/developer guide](../../../deploy/discord/README.md).
The reusable scenario is [tests/native-world.py](../../../native/discord-entrance/tests/native-world.py);
its later resume/pin bookkeeping preserves earlier result rows rather than
replacing the failed attempts. No real Discord messages, command registration or
deployment were performed.

## Remaining boundaries

Arbitrary shell jobs interrupted after `started` need native history/lookup;
the entrance cannot infer whether their multiple effects happened. Discord
publication UNKNOWN has no automatic unsent retry. An operator may attest a
confirmed destination message with `--resolve-up`; the runner does not verify
that attestation with Discord. Large room pages fail closed at the capture bound.
Webhook/read-channel correspondence is still an operator-configured mapping.
There is no automatic custody garbage collector, attachment mirror, message-edit
feed or independently held user key supplied by this service-custodied entrance.
