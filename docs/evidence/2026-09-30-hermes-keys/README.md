# Hermes provider keys: each call carries its caller's credential

Run `e2` on persvati, 2026-09-30, `run.sh bin run/e2`. It passed, with
`HERMES_KEYS_EVIDENCE_PASS`: 13 of 13 rows, and 0 fake tokens found anywhere.

**Source.** The run used commit `9e706986`, branch `hermes-keys`. The binaries
were built from that tree with `nightly-2026-06-21`, `--release`, and copied
into `bin/`:

| binary | sha256 |
|---|---|
| grain-runtime | `86c84e886d9ffbdb221bb93a1be96c3d206e4051b3bab979b19a41f21a0acbbf` |
| mini | `60dfd8e9fe7ba8fc3ca12ce18ceb84be210da22868a44a35665091fed473b4a8` |
| mini-hermes-test-provider | `117c49d3095705c8bcb433df4ab5c41fbae7d45e9421046e893fa7d57bfddf24` |
| minidregg-host-p2 (the product Host, unchanged) | `f4208429d482aa3bae0772b962ddf8641ec48fc5b9d5fddcd395fb62643374f2` |
| Store / verifier (unchanged) | `599bc4e6…` / `71b8d734…` |

## What ran

**The Stores.** There were three fresh Stores, each from `acceptance.sh
BOOTSTRAP_ONLY=1 PROVIDER_BOOTSTRAP=1`. Each held one grain, tasks
74601..74604, with the provider purse at task 74604 (subject 9, budget 50). The
Stores ran one after another.

**The controller.** Each Store ran the real `grain-runtime serve` controller as
the transient user unit `mini-grain-controller@74601`. Its worker was the bwrap
hold fixture (`fixture/hermes-acp`, `--network host`,
`localFixtureHostNetwork`), which kept one Hermes prompt and its gateway lease
open. The script then sent Chat Completions requests to the gateway with that
prompt's own token, exactly as Hermes would.

**What each request went through.** Every request took the real path:
1. route resolution at reserve;
2. the signed provider reserve with its parent witness;
3. `mini continuity` at the send boundary;
4. curl to the upstream;
5. the retained outcome;
6. delivery;
7. the signed settle.

**The upstreams.** Both upstreams were `mini-hermes-test-provider
--route-probe`: one stands in for OpenRouter (the `openrouter` and `pool`
rows, port 18931) and one for the homelab (the `none` row, port 18932). Each
logs `auth=sha256(Authorization value)` or `auth=none`, never the value.

**Friends.** Friends A (subject 21), B (22) and C (23) are workspaces with
fresh keys (`friends.tsv`). They are not enrolled in these Stores. The
credential layer does not consult enrollment; the operator's `onBehalfOf` pin
does. The fake tokens `sk-or-v1-FAKE-…` were generated per run, stored with
`mini key set … --secret -`, and the input files were then shredded.

**How to read the table.**
- `expected_auth` is the SHA-256 of `Bearer TOKEN` for the credential that
  must have been used (`expected-auth.tsv`).
- `purse_after` is a signed query of the provider purse after the call:
  `remaining/reserved`.
- Every row debits the purse by the task's fixed charge, whatever the route:
  1 in Stores A and B, 20 in Store C.

| store | step | caller → row | HTTP | code | upstream saw | purse after | verdict |
|---|---|---|---|---|---|---|---|
| B | b1 | B → openrouter (user) | 200 | – | **B's** bearer `05518a73…` | 49/0 | PASS |
| B | b2 after `key revoke openrouter` | B → openrouter | 403 | `no-credential` | nothing | 49/0 | PASS |
| A | a1 | A → openrouter | 200 | – | **A's** bearer `35c1782b…` | 49/0 | PASS |
| A | a2 | A → openrouter | 200 | – | A's | 48/0 | PASS |
| A | a3 `max_tokens` 128 > per-call 64 | A | 403 | `per-call-cap` | nothing | 48/0 | PASS |
| A | a4 (3rd call today) | A | 200 | – | A's | 47/0 | PASS |
| A | a5 (4th call, per-day 3) | A | 403 | `per-day-cap` | nothing | 47/0 | PASS |
| A | a6 after re-grant per-day 10 | A | 200 | – | A's | 46/0 | PASS |
| A | a7 after re-grant `--until 1` | A | 403 | `grant-expired` | nothing | 46/0 | PASS |
| C | c1, C has no key, first row is `user` | C → openrouter | 403 | `no-credential` (no fallthrough to the pool) | nothing | 50/0 | PASS |
| C | c2, operator puts `pool` first | C → pool | 200 | – | **the pool's** bearer `8d08b75c…` | 30/0 (reserve 20, settle 20) | PASS |
| C | c3, operator puts `homelab` first | C → homelab (none) | 200 | – | **no Authorization header** | 10/0 | PASS |
| C | c4, pool again, reserve 20 > remaining 10 | C → pool | 402 | `no-credit` (Mini refused the reserve) | nothing | 10/0 | PASS |

**Readings of the table:**
- **A's calls never carried B's or the pool's bearer.** Both B's and the
  pool's credentials were stored, and B's grant named the same runner (9),
  while every A call was made.
- **B's revocation did not affect A.** Store A ran after B revoked.
- **A refused route reached no one.** Every refusal left the upstream log
  unchanged and the purse unchanged.
- **The c4 refusal is Mini's decision.** The controller log shows
  `provider reserve refused by Mini: {…"phase":"admission"…}`. The controller
  keeps that refused attempt in its journal (`reserveRefused: true`) for its
  own reconciliation, which is the existing M5 behaviour.

**No secret anywhere.** `token-grep.tsv` shows that every file under the run
directory has 0 hits for any fake token. That covers:
- the three Stores;
- the controller journals and state directories;
- the sealed credential store;
- the `mini key` outputs;
- the connector and controller logs;
- the upstream logs.

The user systemd journal for the run also has 0 lines with a fake token.

**Namespace isolation.** A workspace that claims B's subject (22) with its own
key ran `key revoke openrouter`. The result was `removed: false`, and B's key
was untouched (b1 later used it). See `key-revoke-mallory-claims-b.json`.

**What is here** (under `e2/`).
- `table.tsv`: the table above, as the script checked it.
- `key-*.json`: every `mini key` output (names, limits, public keys, never
  values).
- `store-*-controller.log`: the controller's audit lines, `provider attempt N:
  permitted provider=… credential=user:21|pool|none endpoint=…` and `provider
  request refused: …`.
- `store-*-journal-final.json`.
- `upstream-*.log`.
- `providers-*.json`: the three table states (installed root:root 0644).
- `store-*-controller.json`: the controller configs.
- `e2.out`: the run's stdout.

**Not shown:**
- **Real inference.** No real OpenRouter or homelab call was made. Both
  upstreams are the loopback fixture.
- **A metered task.** The rows carry no tariff, and the tasks use a fixed
  charge. The `tariff-mismatch` rule is unit-tested only.
- **The hosted-shell `key` verb end to end.** Its line-to-call mapping is
  unit-tested (`keys::tests`), and the CLI it maps to is what ran here.
