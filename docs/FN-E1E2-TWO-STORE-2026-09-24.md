# Isolated A→B→A exchange, qualification record

Status: **harness prepared; composed owner not yet run**. This record keeps
the exact untimed preflight result separate from any later timed result. It
follows fn `planning/experiments/e1-e2-agent-exchange.md` and
`specs/consumer-progress.md`. The earlier native E2 poll/transaction/ACK and
single-Store B3 sign/post/cold-reopen are separate observations in
[`FN-E2-LIVE-2026-09-24.md`](FN-E2-LIVE-2026-09-24.md) and
[`FN-E2-B3-NATIVE-2026-09-24.md`](FN-E2-B3-NATIVE-2026-09-24.md).

The retained Mini owner of this experiment is
[`scripts/fn-e1e2/`](../scripts/fn-e1e2/README.md) on isolated `fn-evidence`
commit `0be9541f17bb3f6230e6f80ee18befa04bd63e17`. Its driver SHA-256 is
`e5429ebad6565fcfae30404016da5df43f2ca7e53619a9dfd16591418a6b03e3`;
the source-owned A correlation checker SHA-256 is
`04614980748fedd340b1a8e41c978f2217b09061eb1334ddd3c74ed595aebd71`;
the protected observer SHA-256 is
`028b354b5ae72bbda4e57ee597f607a4681d2afdc8c6e959e803c87218874b95`.
Python syntax, shell syntax and `git diff --check` passed. The Lean checker
passed against prior exact B3 prepared/signed/Q/R source artifacts after
`lake build Kernel.FnReplyPublication` rebuilt a stale local `.olean`. A
one-byte altered A source was refused by the checker. Those are checker
tests, not an A-side native two-Store result.

Fn is pinned to the qualified e160 production image at
`/tank/fn/gates/luna-feature-e160442f/build/fn-host` (source
`e160442f2a5401328f5e76c99216f0d11d5755cf`, launcher SHA-256
`2ca6ce83f5d8e9598e0af74f77b49130ed02738d79e828e6498909e6c0081e57`,
core SHA-256
`9a1cd1fb267878b1134166a77aab0081236e783a5d8ff2a3edafb33a38720a4e`).
Its source qualification manifest is
`/tank/fn/gates/luna-feature-e160442f/planning/evidence/manifests/certify-20260924T031327Z-785374.json`,
SHA-256
`0d74ea04d26daf5140ced0e7b2de553f3400b15699c6604e08a0d1833e707fe8`.
The exact-image protected reciprocal STARTTLS+AUTHINFO preflight passed in
4.615 seconds with separate temporary Stores, protected transfer/reconnect,
and unauthenticated transit refusal 502. Its raw log is
`build/freeze/b3-e160-protected-peer-preflight.log` in that gate, SHA-256
`da0ea6e003a417ca4c2cca65c6150383486925374345ad9dfa3905e4c798de89`.
That preflight does not compose Mini or hybrid authoring.

An initial isolated carrier-injection probe attempted to give the previous
rendered R carrier (`live.eml` SHA-256
`7f89c8fe907a8c524508e5c2366ac3e5b2c87fa7ac74c48a340c6b471e9b6440`)
to native `operator post`. It returned exit 1 with `refused operator post
REFUSED`, leaving no article; raw log `preflight.log` under
`build/mini-e1e2-carrier-preflight` has SHA-256
`e9be783db374fbdb1a70f9ff6e9954abd16ad12f81ed00e39f4a00b6e245b695`.
The composed fixture instead uses native `hybrid-sign` and `hybrid-author` on
the unchanged R authored source (SHA-256
`fca9c81e8cd02281b3703df4e931ae82c55a0bda63b3cf3447c8e32e13199000`)
with a fresh A test keyset. It will enroll A's public keyset on B before
protected transit. This is a new fn acceptance of the same synthetic source,
not a replay of the earlier carrier/signatures.

Mini uses the clean B3 functional host from source
`1eb84a9a46e08aa423a99e39ad74a9be538b5385`, executable SHA-256
`11f451f7c14d55efcb16ee16f99bfffc20f551a7ebf173d5090966e1434f68f9`.
The later projection optimization candidate is excluded until it repeats a
full native B3. The `mini` custody client SHA-256 is
`e86dbc95475b309199204fc9a6c3cb94e305c0e756f765149737a3528a39ae60`;
the opaque SQLite and signature-helper executables selected by the pinned
Mini configuration have SHA-256
`452908cb42070c57051fa7ccd65696541ec940f158c17db4f832a6355bc85e03`
and `dd5273f30a999dc7594018dd57605aebf2f9f15c43010f31e8674d28f14aafd9`.
The fresh Mini configuration SHA-256 is
`b50e09caa07002a1e1caeaf9987eab6921c563d7f5a71fed328b4cff63da8e8a`;
it selects `/tmp/mini-fn-e1e2-two-store-20260924/mini-store`. It was
bootstrapped with the pinned E2 genesis and accepted only the retained birth
intent, reporting `confirmed`, accepted count 1 and transaction
`30574338302698088804635708227956052706316029374670952451210790093397252577964`.
The birth outcome JSON SHA-256 is
`dc7290dc62206625a5fa754905ec617d9eecfd7cb1c0c9b5ffd1dfc7fad58171`;
the SQLite root SHA-256 before the composed run is
`370c7adaca831d885830a09adc82eca89fcb7036f8431ef9b64a993bf924e9df`.
An earlier birth command omitted `--intent-kind birth-intent` and was refused
before submission. Its correction and the exact setup commands are in the
retained README.

The first composed trace is planned to settle an advancing fn ACK whose
response is deliberately lost by querying B's durable position, and a Q
post whose response is deliberately lost by protected read-only lookup and
native exact-source verification. Both cases must preserve accepted,
refused and uncertain as distinct outcomes. A's Q consumer cursor remains
unacknowledged without a durable A-side application transaction. No fn ACK
or post claims exactly-once external effects. No `/tank/fn/node` service,
Mini main branch, remote publication or deployment was changed.

## Untimed two-Store composition refusal

An untimed e160 owner preflight did perform fresh native `hybrid-sign` and
`hybrid-author` of that exact R source at A, protected STARTTLS+AUTHINFO
A→B transit, B ARTICLE retrieval, and B native `hybrid-verify-source` on
the received carrier. B's local-owner consumer poll then returned a
30,338-byte legacy `fn-r` Store article record (sequence 3, transaction 3),
not a kind-4 `fn-stxa` composite. The native ACL2 `consumer-project` returned
`fn-consumer-project-refused-v1 codec`. More decisively, protected B
`HDR :fn-verified <R>` returned `0 absent no-field` both at keyring
generation 1 before rotation and generation 2 after. The independent
cryptographic verification of current carrier bytes cannot be recast as an
acceptance-time Store verdict.

The e160 owner fixture was **not** launched for a timed Mini handoff and no
`ready.json` was published. Fn's `fn-owner-consumer-local-poll` emits raw
`fn-r` when the accepted event is not `fn-stxa`; `fn-cpj-project` requires
`fn-stxa-decode-exact`, authenticated authored-source binding and a retained
verified verdict. Mini's `FnPollProjection` and `StorePollInbox.valid` require
that same nonempty historical verdict and the exact observed poll/control
binding. A Python conversion of the legacy record, or a later standalone
`hybrid-verify-source` call, cannot fill the missing Store event. The next
qualified fn image must verify peer ingress under B's acceptance-time
keyring and durably retain a bound kind-4 composite/verdict before this
driver can claim B2. This is a new native behavior/proof/host obligation,
not a test waiver.

Untimed exact e160 artifacts are under
`/tank/fn/gates/luna-feature-e160442f/build/freeze/`:

| Artifact | SHA-256 |
| --- | --- |
| `e160-two-store-preflight-v3.log` | `b311c4e0e68a06551bd4e1c850898add46e56f4cb5051fa4f469587e999eff6f` |
| `e1e2-preflight-artifacts/b-preview.fn-e` (raw `fn-r`) | `11efb2f90173390718192d0efbf7cd5c488592f9425ddf71baf9420c1d0d7d5f` |
| `e1e2-preflight-artifacts/b-preview.fncu` | `b0f4e0b505f48ae7d24395b20af23428d1fe1cc44ad9089bba480b02a706f606` |
| `e1e2-preflight-artifacts/r-at-b.eml` | `cb7042042f52e6e10a4ec4956a691c6fd9cdc342245a2563e0b9c4a30530422f` |
| `e1e2-preflight-artifacts/b-r-header-gen1.txt` | `8e630bb5ac2c0a6f7cb5d970fc946e60b204cd7b6a18a3c9bcdaa943c591d2f3` |
| `e1e2-preflight-artifacts/b-r-header-gen2.txt` | `8e630bb5ac2c0a6f7cb5d970fc946e60b204cd7b6a18a3c9bcdaa943c591d2f3` |
| ACL2 record diagnostic log | `99bce8f282b4dcf37af7dce0bef4ce5979726fa61a25a6fc70b47028ae5c6609` |

The staged test-only owner fixture SHA-256 was
`daf37a1f94f249344f204489210d3715018ae671869377ebf716c0c0bf9d503c`;
it did not change the qualified e160 source/image. Fn's separate gap record
is commit `564d0e6a`. The retained Mini driver is parameterized to require
the future qualified image path and exact launcher/core hashes at invocation,
so it will not silently reuse e160 for the missing capability.

## A-side durable reply consumer prepared after the refusal

Mini now has a strict Lean parser for the fixed synthetic Q profile and a
separate A-side reply-consumption decision. The host calls A's observed local
fn poll, ACL2 consumer projection and native hybrid source verifier; it also
re-admits R's exact original Mini package before constructing the report.
The result command retains the exact Q carrier, fn cursor/report, native
historical verdict, R receipt and parsed Q correlation in one accepted Mini
transaction. A source-independent `(application, operation)` marker permits
one result; a distinct observed Q for that operation is conflict evidence.
The export command cold-reopens the accepted event, and the ACK command
requires its exact retained cursor/report and control binding. The A result
means that Mini durably observed and correlated Q, not that an external effect
ran exactly once.

`lake build Kernel.FnReplyConsumption Host.Main` passed. The retained
`scripts/fn-e1e2/check_reply_consumption.lean` passed against the exact
previous B3 Q source at
`/tmp/mini-fn-reply-plan-20260924/live-b3-retry-1/reply.source`; it checked
canonical inbox codec and fresh operation command, and refused absent local
poll observation, changed R source identity, changed operation and a modified
Date. This is source-level testing only. No A Mini result was submitted and
the previously qualified e160 image still cannot provide a B or A historical
peer-ingress verdict. The current two-Store driver ends with native A
observation; a future source-matched fn owner must keep A control live for a
second atomic `a-ready.json`/`a-mini-finished.json` handoff and a separate
fresh A Mini deployment. The new Mini host source has not repeated the full
B3 native sign/post run and does not replace that qualified baseline.

## Subsequent composed result and reproducibility note (2026-09-26)

Fn's later `planning/evidence/two-store-join-1a9dd747-2026-09-24.md`
supersedes the *status* above while preserving this e160 negative evidence.
The qualified `1a9dd747` production/developer pair added peer-authored
ingress: B and A each kept the receiving Store's acceptance-time bound
signature verdict in a kind-4 composite. Fn's unchanged
`tools/runbooks/two_store_join.py` then completed the signed R→B, Mini B
transaction/ACK, signed Q→A, Mini A transaction/ACK exchange with separate
native fn Stores. All five scoped runs (`none`, `a-accepted`, `b-verdict`,
`ack-response`, `reply-at-b`) reported `EXCHANGE COMPLETE`; a deliberately
lost ACK reply was uncertain until `consumer position` settled it. This is
one-host process-death and transport evidence, not power-loss or arbitrary
topology evidence.

That completed run used Mini `implement/fn-evidence` revision `183cd37` and
binary SHA-256 `0cce4fbd02c5b5156fb061e2d96f2e25e12588c35b59d2fd2efe20acb202f286`.
Its Mini A and B deployments reused one pinned genesis and custody key while
changing only storage roots; the R source also contained a retained earlier
Mini origin package. A new Mini-side `scripts/fn-e1e2/setup-mini.sh` now
authors a fresh private deployment, gateway and ordinary keys, content birth,
policy and origin pin without the vanished historical `/tmp` inputs. An
independent A/B Mini identity run still needs per-side Mini inputs to the fn
harness (or an equivalent composed runner). No claim about independent A/B
Mini administrators transfers from the five completed runs.

The first 2026-09-26 fresh-input attempt used fn's unchanged harness on the
qualified pair and Mini's exact `183cd37` binary. B's protected transfer,
historical receiver verdict after restart, and Mini's observed
`consumer-poll-decide` passed. Its first Mini consumer `submit` was refused by
the source host at observation preparation, before a Mini application
transition or fn ACK. A separate authorized target-600 query with the same
fresh signer passed; recomputed challenge bytes matched the failed attempt.
The fn owners were stopped by harness cleanup. The encoded invocation measured
102,872 bytes, but that first genesis's owner grant allowed only 100,000 cost;
`NativeObservationController.request` sets cost to encoded intent length. This
explains observation refusal without changing the underlying authorization
law. The fresh setup now selects an operator `ownerBudget` of 300,000 before
bootstrap/birth and adds an ordinary key with no content mutation authority.
Distinct A/B subjects (7 and 17) can be authored from the same script, though
the existing fn harness still accepts only one Mini deployment input set.

The rerun with a new `ownerBudget=300000` genesis passed B's accepted Mini
consumer transaction and export, durable fn B ACK, Mini Q preparation and
signature, signed Q→A peer transfer, both fn Store restarts and A's historical
Q verdict. It stopped at A's Mini reply decision before a Mini A transaction:
`minidregg-host: Q source has invalid Message-ID fields`. The exact generated
Q source is retained privately at
`/tmp/mini-fn-setup-probe-parent/gateway-run/q.source`; its Message-ID has 68
hexadecimal digest characters. `FnReplyPublication.messageId` renders a
variable-length `digestStream.encode digest.digest`, whereas
`FnReplySource.parse` requires 66 hexadecimal characters. The mismatch is a
fresh-key source defect in the pinned `183cd37` image, not a fn verdict or
Store restart failure. The run's `summary.json` records the refusal and
cleanup; no A Mini result or A ACK is claimed.
The retained private Q source SHA-256 is
`c29a617ea0eb53860b9fd04d82e670b5614b9515baacdea5d6f3cec2326d5196`;
the A refusal step log SHA-256 is
`b7bee163cffb375198802b7be89ce7dc17f32ee5d89589c64935b96799b81a75`
and the full run summary SHA-256 is
`df1550ba26c2893142e893c336a17e126c92cf367636ad263df7913a94b7d062`.
These are locators for private scratch evidence, not committed custody material.

The setup now additionally confirms a delegated cap 63 for an ordinary signer
while retaining the exact gateway-subject birth law. Its local two-event
probe Store permits a stronger policy-refusal test; the fn exchange's fresh
A/B Stores replay genesis plus birth only. The Mini-owned
`scripts/fn-e1e2/check-ordinary-refusal.sh` used that accepted cap-63
delegation and the ordinary signing key; the public direct submit refused
at observation, with Store height 12 and target root unchanged. That result
does not claim a signed receiver call was tested. A separate source-owned
`probe_gateway_direct_submit.sh` then built and signed an exact subject-8
call under the accepted current cap 63 in the same fresh B probe Store. The
native receiver returned `policyRejected` and accepted history was unchanged;
the public submit remained uniformly refused. Its private log is
`/tmp/fn-gateway-direct-submit.log`, SHA-256
`bf6391ba46450533ef7a2e25dc000f1130604fec8f50f54611e3ac7e38b1be66`.
This receiver negative complements the public observation-gate refusal.
The setup also obtains the
accepted policy source address and writes a separate operator-pinned
`gateway-config.json` for the current source gateway check. The Mini-owned
`scripts/fn-e1e2/two_store_join_per_side.patch` adapts a private copy of fn's
source-hash-pinned Python test harness to accept independent A/B deployment
inputs, while qualified fn binaries and the shared fn checkout remain
unchanged. This is test harness adaptation, not fn platform code. A distinct
A/B coverage for both canonical Q Message-ID lengths awaits a Mini image with
the Q Message-ID parser repaired.

## Distinct Mini A/B exchange on first fresh identities (2026-09-26)

The isolated, source-hash-pinned fn harness copy then ran once with newly
generated, different Mini A and B identities: B gateway subject 7 and A
gateway subject 17, different custody keys and genesis bytes, separate Mini
Stores, and each side's own policy and exact current policy-address pin. The
qualified fn `1a9dd747` image pair and Mini `183cd37` binary remained fixed;
fn's shared checkout was not edited. All 77 harness steps completed, including
B's Mini accepted transaction/export/ACK, signed Q→A peering and restart,
A's Mini accepted result/export/ACK, and final two-article counts. The harness
summary says `cut=none`, `stopped=EXCHANGE COMPLETE`, reached
`final-article-counts` with `ACCEPTED`. B and A outcomes each say confirmed,
installed, accepted count 2 in their own Store.

The private retained run is
`/tmp/mini-fn-setup-probe-parent/distinct-run-1`, with summary SHA-256
`5425858da0674fb0ace6c759a997bd9985af5b922a74877d09c5d264c5f318a6`.
Its adapted harness SHA-256 is
`fa595de896891cf362c8f8af3a8000d6ab8298d59837f0c8634b6807faaf2015`;
the unmodified fn source harness was pinned to
`c88160cf459d3959928f6ae913f455ed9ff49971b89619518ab7b49c884c99e6`.
The actual Q source SHA-256 is
`acca211998b1b501aed50f80c66c5696c329656969db0c37e72203b93d97394e`.
Its Message-ID happened to have the parser's 66 hexadecimal digest characters
on these first distinct inputs. This success does not erase the independent
68-character failure above; the source parser defect remains until repaired
and verified for both lengths. No fresh-key search was performed.

The underlying harness printed `EXCHANGE COMPLETE` and accepted owner cleanup.
The outer shell wrapper process then reported an EOF syntax error because that
wrapper file was edited during the long-running child process. The present
wrapper passes `sh -n`; the documented result rests on the retained harness
summary and per-step logs, not the outer shell exit status.
