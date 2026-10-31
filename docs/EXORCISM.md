# EXORCISM

The waste on the paths members and agents hit, read end to end. A present-state table, rewritten
whole. Owners: hot-path (a8e4317c9e1574ca5) holds `story new`, the CLI's resident Host socket and
the FORMAT batch; private cells (a8da2b953507b402b) holds blinded-cell hiding. Every row below
that is not marked theirs is this lane's.

## Findings

Costs are per operation on hbox unless said otherwise. `H` = history height.

| # | where | what it does | why nobody would do it on purpose | cost and scaling | fix | state |
|---|---|---|---|---|---|---|
| 1 | every durable write: `mini_sdk::durable`, `phase`, ~575 call sites in 164 files (native/, deploy/, scripts/) | fsync of every file and its directory, ancestor chains, seal records, syncfs, SQLite `synchronous=FULL` + `fullfsync`, anchor fsync, on reads as well as writes | no durability design was ever asked for; a read has no effect to keep | hot-path measured 207 fsyncs, 4.0 s of a 3.9 s line (`room bind`); `story new` 62-70 s, of which Host work was 4.5 s | all removed (batch 1; testing/ and extensionless fixtures in e38913cc5) | merged to staging (6ffabc364), measured below |
| 2 | `native/resource-client/src/main.rs` `process` / `local_process` | spawns a fresh `minidregg-host` per Host call unless `--socket` | the resident `mini serve` exists | Host start + Store open O(H) per call | resident socket | hot-path |
| 3 | `native/resource-client/src/web/body.rs` `verb`, `plan_line`, `verb_detached` | every form post and most fragments spawn a whole `mini shell` child, polled every 25 ms; `plan_line` spawned one only to PARSE a line | the shell's parser and planner are in the same binary | a shell child is about 20 ms of start, workspace load and resident connections per action, plus up to 25 ms of poll | plan in process (5f9d41e2b); the child is waited on, not polled (60cd0fbca); the child itself stays: the body serves concurrent requests and a mutating line outlives its page at 100 s, which a single resident cannot | poll done; child open |
| 4 | `web/body.rs` `import_inbox` (public front page) | each GET scans the inbox and spawns `mini workspace --action import` per new file | `workspace::import` is a function in this crate | one child per new inbox file per page load | `workspace::import_delegated` in process | done (5f9d41e2b) |
| 5 | `native/grain-runtime`: the custody gate (`workspace_*`, reserve and lifetime authoring, historical lookups, resource reads), `command_capture` (about 20 Host submissions and lookups), `RoomTools` (room Hermes reads, payments, lookups) | every Hermes typed-tool or room tool call spawned a fresh `mini` and the gate polled it every 10 ms | a JSON round trip through a child between our own components | `workspace list` 20 ms as a child, 0.4 ms as a frame; `workspace read` 72 to 51 ms; a room read (`mini shell --line doc show`) 82 to 52 ms | `mini command-resident` (resource-client `capture::serve`), frames with argv and stdin; one resident per gate and per room identity; cancel and deadlines kill its group as they killed the child; residents retire before the quiescence proof; journaled room writes keep their own child (its /proc cmdline is the stopped-submitter proof) | done (8221ced44, 10f52ebde, a6512c115) |
| 6 | `grain-runtime` `inspected_pre_submit_refusal`, `refusal_codec`, reserve codec, lifetime paid ingress and committed inspection; `spk-host` `PrivateOperator::tool_until` | spawn the 180 MB Lean Host one-shot to `author`/`inspect`/`signatures` | the persistent Host answers the same verbs in session (operations 195-197, `runToolSession`, byte-identical) | 0.07-0.24 s bare start each | spk-host: done on staging (`tool_in_session`); grain-runtime: a paid lifetime dispatch's committed-frame inspection is one INSPECT frame to the resident codec (53e2736bb, the same compact bytes); `inspect-agent-lifetime-paid-ingress` has no codec operation (Lean); the refusal and reserve codecs run only in startup recovery and retain pretty-printed evidence | spk-host done; grain-runtime: per-dispatch done, recovery-only open |
| 7 | `spk-host` `run_pinned` | polls the child every 10 ms and fsynced its stderr log | a wait is a wait | up to 10 ms per helper call (the fsync went in batch 1) | blocking wait with deadline | done on staging (`wait_for_exit`) |
| 8 | `Compiler/NativeCoprocess.lean` callers: `CredentialSignatureIO.verify`, every `DurableReceiverCore` Store op | each signature check and Store op makes a temp dir, writes inputs to files, the helper reads them back, writes its output to a file, Lean reads it | the coprocess frame could carry bytes (its stdout field is UTF-8 text today) | measured on hbox's tmpfs: at most 130 us per op with no fsync left, under 1% of a Store op | bytes in the frame (Lean + both helpers' `serve`) | open, low |
| 9 | `native/hyperdocument-link-sqlite-store/src/main.rs` `run` | every helper request re-opens SQLite: mkdir, canonicalize, open, six PRAGMAs, schema check | the helper is a resident process | about a millisecond per Store op | keep the handle per root, reopen on inode change | done (b3b132f19) |
| 10 | `native/resource-client/src/apps.rs` `delegate_lifecycle` | `apps install` spawns `mini workspace --action app-lifecycle` per round, up to 14 rounds plus status | same binary; `chat::client` already runs actions in process | two process starts per round | `capture::command` in process | done (b3b132f19) |
| 11 | `web.rs` `Site::doc` | a document page is three separate signed reads (page, `links`, `backlinks`) | `signed_views` batches reads | two extra challenge/query round trips per page | one `signed_views_mixed` batch | done (b3b132f19) |
| 12 | `web.rs` `Site::targets`, `index`, room children, inspect and resident pages | every page re-listed `refs/` and parsed every reference and birth source | the body is one long-lived process | O(references) per page (not visible at 200 references against box noise) | a kept `RefIndex`, rebuilt when `refs/` or `sources/` changes | done (60cd0fbca) |
| 13 | consent provider (`Host/ClientConsentCore.lean`) | re-admits every record the Store gained since it last looked | independent verification is the design | ~47 ms per foreign record of catch-up | hot-path's option A (rebase at checkpoint) | hot-path |
| 14 | `mini_sdk::consent::serve_resident_kind` (the consent and codec residents) | slept 5 ms between non-blocking accepts; and a resident started by a long-lived process stayed its child | a wait is a wait; a daemon belongs to init | up to 5 ms per connection (two per `mini` command) and 200 wakeups a second per idle resident; a zombie per idle exit under a long-lived starter | poll(2) on the listener; `daemonize` forks once at the resident's entry (parent is init: checked on hbox) | done (53e2736bb) |

## Batch 1: no fsync anywhere (2b206eb7e)

Ember's ruling: no file, directory or Store write is a durability point, the Store's commit at
receipt time included; permanence comes from certification and checkpoints.

Removed, by file (count of removed sync lines; `git show 2b206eb7e` for each site):

| area | removed | files |
|---|---|---|
| `native/resource-client` | 236 | `src/main.rs` 12, `src/grain_share_issue.rs` 10, `src/pay_claim.rs` 9, `src/agent_reserve.rs` 9, `src/session_enrollment.rs` 8, `src/agent_reserve/lifetime_v3/paid.rs` 8, `src/transport.rs` 7, `src/share_issue.rs` 7, `src/fsio.rs` 7, `src/agent_reserve/lifetime_v3.rs` 7, `src/agent_lifetime_grant.rs` 7, `src/receipt_continuity/carry.rs` 6, `journey.d/j14-oracle.py` 6, `src/selected_publisher.rs` 5, `src/provider_continuity.rs` 5, `src/pay.rs` 5, `src/participant_namespace.rs` 5, `src/participant_enrollment.rs` 5, `src/meter.rs` 5, `src/current_birth.rs` 5, `platform-stage-root.py` 5, `src/workspace.rs` 4, `src/selected_release.rs` 4, `src/selected_exchange.rs` 4, `src/fleet.rs` 4, `src/attempt_state.rs` 4, `src/append_proof.rs` 4, `src/world_export.rs` 3, `src/share_issue_receipt.rs` 3, `src/receipt_continuity.rs` 3, `src/participant_provisioning.rs` 3, `src/key_rotation_custody.rs` 3, `src/historical_call_receipt.rs` 3, `src/hermes_handoff.rs` 3, `src/consent_proxy.rs` 3, `src/agent_payer.rs` 3, `src/shell/session_fs.rs` 2, `src/join_solana.rs` 2, `src/fresh_onboarding.rs` 2, `src/cohort_tcp.rs` 2, `src/clock.rs` 2, `src/app_document.rs` 2, `platform-task-readiness.py` 2, `platform-service-cut.py` 2, `platform-provision.py` 2, `paid-entry-adapter.py` 2, `journey-key-adoption.py` 2, `src/well.rs` 1, `src/signing_wire_tests.rs` 1, `src/roomkey.rs` 1, `src/replan.rs` 1, `src/receipt_continuity/carry/verifier.rs` 1, `src/query_refusal.rs` 1, `src/protected_object/object_cli.rs` 1, `src/prepare_refusal.rs` 1, `src/paid_onboarding.rs` 1, `src/paid_context.rs` 1, `src/objective_invoke.rs` 1, `src/key_rotation.rs` 1, `src/fleet_sign.rs` 1, `src/credit.rs` 1, `src/apps_worker.rs` 1, `src/app_lifecycle.rs` 1, `src/app_interface.rs` 1, `selected-release-drop-reply.rs` 1, `platform-stage.py` 1, `composed-scenario.py` 1 |
| `native/spk-host` | 108 | `src/hostd.rs` 18, `src/broker_volume_custody.rs` 8, `src/shared_data.rs` 7, `src/materialize.rs` 7, `src/grain.rs` 6, `src/operation_ledger.rs` 4, `src/install_v3.rs` 4, `src/grain_export.rs` 4, `src/broker.rs` 4, `src/agent_api_native.rs` 4, `src/agent_api_lifetime_dispatch_native_v3.rs` 4, `src/resident_service.rs` 3, `src/resident_route_control.rs` 3, `src/lifecycle_v3_stop_service.rs` 3, `src/launch_descriptor_native.rs` 3, `src/http_entrance.rs` 3, `src/grain_route.rs` 3, `src/dispatch_native.rs` 3, `src/dispatch_fence.rs` 3, `src/checkpoint_control.rs` 3, `src/lifecycle_v3_stop_recovery.rs` 2, `src/identity_custody.rs` 2, `src/grain_profile_upgrade.rs` 2, `src/volume_helper.rs` 1, `src/sandbox.rs` 1, `src/fixture_os.rs` 1, `src/agent_api_server.rs` 1, `src/agent_api_lifetime_custody_v3.rs` 1 |
| `native/mini-sdk` | 42 | `src/durable.rs` 32, `src/flow.rs` 5, `src/fsread.rs` 2, `src/store.rs` 1, `src/profile.rs` 1, `src/lib.rs` 1 |
| `scripts` | 40 | `scripts/spk-platform/adopt-first-birth-receipt.sh` 10, `scripts/spk-platform/ws-continuity-supervision.py` 7, `scripts/spk-platform/checkpoint-app.py` 5, `scripts/spk-platform/ws-continuity-launch.py` 3, `scripts/spk-platform/native-input-successor.py` 3, `scripts/spk-platform/ws-continuity-regressions.py` 2, `scripts/spk-platform/sandbox-launcher-stage.py` 2, `scripts/application-payer-successor.py` 2, `scripts/application-attachment.py` 2, `scripts/spk-platform/tests/test_ws_continuity_launch.py` 1, `scripts/spk-platform/connector-authority.py` 1, `scripts/spk-platform/app-interface/test_sessions.py` 1, `scripts/spk-platform/app-interface/row.py` 1 |
| `deploy` | 36 | `deploy/spk-host/controller-world.py` 14, `deploy/oracle/acceptance/continue_controller.py` 12, `deploy/grain-host/launch-gate.rs` 5, `deploy/oracle/pack/src/main.rs` 2, `deploy/oracle/acceptance/recover_foreground.py` 2, `deploy/grain-host/materialize-bwrap.py` 1 |
| `native/grain-runtime` | 33 | `src/resident_reconcile.rs` 4, `src/provider.rs` 4, `src/resident_preflight.rs` 3, `src/application_enrollment.rs` 3, `src/room_resident.rs` 2, `src/resident_context.rs` 2, `src/provider_profile.rs` 2, `src/main.rs` 2, `src/journal_io.rs` 2, `src/concierge.rs` 2, `src/resident_requests.rs` 1, `src/resident_delivery.rs` 1, `src/resident_completion.rs` 1, `src/provider_provision.rs` 1, `src/history_compaction.rs` 1, `src/hermes_room.rs` 1, `src/grain_create.rs` 1 |
| `native/private-backend` | 17 | `src/transition_journal.rs` 5, `src/custody.rs` 4, `src/recipient_seal.rs` 2, `src/private_output_store.rs` 2, `src/private_initial.rs` 2, `src/native_worker.rs` 2 |
| `native/pay-watcher` | 11 | `src/main.rs` 11 |
| `native/hyperdocument-link-sqlite-store` | 11 | `src/lib.rs` 6, `src/anchor.rs` 4, `tests/lifecycle.rs` 1 |
| `native/joint-agreement-crypto` | 9 | `src/session.rs` 8, `src/main.rs` 1 |
| `native/portable-archive` | 9 | `src/lib.rs` 5, `src/durable_file.rs` 3, `src/main.rs` 1 |
| `native/mini-keys` | 7 | `src/credentials/store.rs` 3, `src/server/ticket.rs` 2, `src/server/provider.rs` 1, `src/server/mod.rs` 1 |
| `native/inference-scheduler` | 5 | `src/service.rs` 5 |
| `native/discord-entrance` | 5 | `src/door.rs` 2, `src/bin/mini-door-process.rs` 2, `src/bin/mini-discord-mirror.rs` 1 |
| `docs` | 3 | `docs/DURABLE-STORE.md` 3 |
| `native/pinned_execution.rs` | 1 | `pinned_execution.rs` 1 |
| `native/mini-web-spawn` | 1 | `src/store.rs` 1 |
| `native/hermes-test-provider` | 1 | `src/main.rs` 1 |

What stays: atomic publication (stage, then `rename` or `link`), so a concurrent reader still sees
a file complete or absent. Deleted claims: every comment, doc and test name that said a write,
receipt or acknowledgement was fsynced, synced or survived power loss (Rust, Python, Lean doc
strings in `Compiler/{PortableContinuationArchiveIO,GenericSimplexIO,CarriedSegmentIO,GenericSimplexNative,PortableParticipantPinIO}.lean`,
and 22 markdown files including `docs/DURABLE-STORE.md`); tests that only asserted fsyncs
(`sync_ancestors` permission rows, deferred-barrier rows, the materialize syncfs barrier, the
override-request fsync row, the seal repair row).

Measured (hbox, scratch world from candidate a4cb65af, member-1 over the forced-ssh wrapper):

| shell line (member-1) | before: wall, fsyncs (time in fsync) | after: wall, fsyncs |
|---|---|---|
| `doc new X note` (first line; starts both residents) | 3064 ms, 194 client + 14 Store (2.04 s) | 1744 ms, 0 |
| `doc append ID X text` (a proposal) | 746 ms, 50 (0.58 s) | 241 ms, 0 |
| `submit ID` | 605 ms, 20 client + 7 Store (0.32 s) | 439 ms, 0 |
| `doc show X` (a signed read) | 339 ms, 27 (0.21 s) | 170 ms, 0 |
| `doc show X` again | 312 ms, 23 (0.22 s) | 120 ms, 0 |

One run each, `strace -f` over the client, both residents, the private Host and its Store helper
(`/ci/exo/m2.sh`); the box was shared with other lanes. Before: candidate a4cb65af's `mini` and
Store helper. After: lane/exorcism 2b206eb7e's `mini` and Store helper, same Host and consent
provider.

## Batch 2: in process, one batch, a kept handle (5f9d41e2b, b3b132f19)

| path | before | after |
|---|---|---|
| `GET /doc/NAME` through `mini web` (member-1, four loads) | 666, 718, 629, 584 ms; 25 Host exchanges | 102, 106, 108, 84 ms; 17 Host exchanges |

Before is candidate a4cb65af's `mini` (it also carries batch 1's fsyncs); after is b3b132f19's
`mini` and Store helper. The page bytes are identical except the launch's path secret
(`/ci/exo/m3.sh`, traces `/ci/exo/tr-{before,after}.jsonl`). Store crate tests: 38/38.

## Batch 3: resident clients (8221ced44, 60cd0fbca, 10f52ebde, a6512c115)

| path (hbox, /ci/exo/w, member-1, median of 9-15) | child per call | frame to a resident |
|---|---|---|
| `mini workspace --action list` | 20.3 ms | 0.4 ms |
| `mini workspace --action read --name X` | 71.7 ms | 50.8 ms |
| room read `mini shell --line "doc show X"` | 82.2 ms | 51.6 ms |
| `mini shell --line whoami` | 2.6 ms | 0.2 ms |

Same exit code and stdout in every pair (`/ci/exo/m4.py`, `/ci/exo/m5.py`). The custody gate's
10 ms poll is gone from every framed call.

## Open, in order

Row 3's shell child (a resident per body needs concurrent requests and a line that outlives its
page); `inspect-agent-lifetime-paid-ingress` as a codec operation (Lean); row 8 (measured under 1%).
