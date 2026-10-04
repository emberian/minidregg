#!/usr/bin/env bash
# check-rust-tests.sh — the native crates' tests the lanes report, as one gate.
#
# FILTERED lines only (never an unfiltered `cargo test -p` suite): each row is
#   t NAME FLOOR CRATE [cargo args] -- [libtest filters]
# run as `cargo +<pinned> test --release --locked [cargo args] -- [filters]` in
# native/CRATE with CARGO_TARGET_DIR (default <repo>/target-gates). A row is red
# when cargo fails OR fewer than FLOOR tests ran (a filter that stops matching
# runs zero tests and exits 0; the floor is what makes that red).
#   known_red NAME TASK CRATE [cargo args] -- EXACT_TEST
# runs one test that is known to fail and must STILL fail: the day it passes the
# row is red ("delete the known_red row"), so a skip is never silent.
#   exact NAME CRATE [cargo args] -- FULL::TEST::PATH...
# runs exactly the named tests (libtest --exact) and is red unless EVERY named
# test printed `ok` and nothing else ran: a test that was renamed, moved,
# deleted or #[ignore]d is a red naming it, not a smaller count. These rows arm
# the regression tests of landed defect fixes (scouts R2-1 and D, 2026-10-03):
# each row names the defect it guards; a fix whose test sits in no row can
# regress silently.
set -uo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$root" || exit 2
export PATH=$HOME/.cargo/bin:$PATH
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$root/target-gates}
rust=$(sed -n 's/^channel *= *"\(.*\)"$/\1/p' rust-toolchain.toml)
jobs=${LOCAL_GATES_CARGO_JOBS:-6}
logs=$root/build-logs/rust-tests; mkdir -p "$logs"
red=0
passed_of() { grep -Eo 'test result: [a-zA-Z]+\. [0-9]+ passed' "$1" | awk '{s+=$4} END{print s+0}'; }
t() {
  local name=$1 floor=$2 crate=$3; shift 3
  local log=$logs/$name.log rc n
  printf '  %-22s cargo test --release --locked %s\n' "$name" "$*"
  (cd "native/$crate" && cargo "+$rust" test --release --locked -j "$jobs" "$@") >"$log" 2>&1
  rc=$?
  n=$(passed_of "$log")
  if [ "$rc" != 0 ]; then
    echo "rust-tests: RED: $name: cargo exit $rc, $n passed; $(grep -E '^test .* FAILED$|^error' "$log" | head -3 | tr '\n' ';') ($log)"
    red=$((red + 1))
  elif [ "$n" -lt "$floor" ]; then
    echo "rust-tests: RED: $name: $n tests ran, floor $floor (a filter stopped matching?) ($log)"
    red=$((red + 1))
  else
    echo "rust-tests: ok: $name: $n passed (floor $floor)"
  fi
}
known_red() {
  local name=$1 task=$2 crate=$3; shift 3
  local log=$logs/$name.log rc
  (cd "native/$crate" && cargo "+$rust" test --release --locked -j "$jobs" "$@" --exact) >"$log" 2>&1
  rc=$?
  if [ "$rc" = 0 ] && [ "$(passed_of "$log")" -ge 1 ]; then
    echo "rust-tests: RED: $name: known-red test now PASSES; delete its known_red row (cv task $task)"
    red=$((red + 1))
  elif grep -q '^test .* FAILED$' "$log"; then
    echo "rust-tests: known-red: $name still fails, as recorded (cv task $task)"
  else
    echo "rust-tests: RED: $name: known-red row did not run its test (exit $rc) ($log)"
    red=$((red + 1))
  fi
}

exact() {
  local name=$1 crate=$2; shift 2
  local log=$logs/$name.log rc n args=() flags=() tests=() missing=() test
  while [ "$#" -gt 0 ] && [ "$1" != -- ]; do args+=("$1"); shift; done
  [ "${1:-}" = -- ] && shift
  for test in "$@"; do  # libtest flags (--ignored) pass through; the rest are test paths
    case "$test" in --*) flags+=("$test") ;; *) tests+=("$test") ;; esac
  done
  printf '  %-22s cargo test --release --locked %s -- --exact (%s named)\n' "$name" "${args[*]}" "${#tests[@]}"
  if [ "${#tests[@]}" = 0 ]; then
    echo "rust-tests: RED: $name: row names no test"; red=$((red + 1)); return
  fi
  (cd "native/$crate" && cargo "+$rust" test --release --locked -j "$jobs" "${args[@]}" -- --exact "${flags[@]}" "${tests[@]}") >"$log" 2>&1
  rc=$?
  n=$(passed_of "$log")
  for test in "${tests[@]}"; do
    grep -qxF "test $test ... ok" "$log" || missing+=("$test")
  done
  if [ "$rc" != 0 ]; then
    echo "rust-tests: RED: $name: cargo exit $rc, $n passed; $(grep -E '^test .* FAILED$|^error' "$log" | head -3 | tr '\n' ';') ($log)"
    red=$((red + 1))
  elif [ "${#missing[@]}" != 0 ]; then
    echo "rust-tests: RED: $name: ${#missing[@]} named test(s) did not pass (renamed, moved or ignored?): ${missing[*]} ($log)"
    red=$((red + 1))
  elif [ "$n" != "${#tests[@]}" ]; then
    echo "rust-tests: RED: $name: $n tests passed, ${#tests[@]} named ($log)"
    red=$((red + 1))
  else
    echo "rust-tests: ok: $name: ${#tests[@]}/${#tests[@]} named tests passed"
  fi
}

sudo_exact() { # sudo_exact NAME CRATE [cargo args] -- FULL::TEST::PATH... (#[ignore]d two-uid tests)
  local name=$1
  if [ -z "${MINI_TEST_FOREIGN_UID:-}" ]; then
    echo "rust-tests: NOT-ARMED: $name: sudo-only two-uid row (set MINI_TEST_FOREIGN_UID with passwordless sudo setpriv)"
    return
  fi
  if ! sudo -n true 2>/dev/null; then
    echo "rust-tests: RED: $name: MINI_TEST_FOREIGN_UID is set but sudo -n refuses"; red=$((red + 1)); return
  fi
  local crate=$2; shift 2
  local args=(); while [ "$#" -gt 0 ] && [ "$1" != -- ]; do args+=("$1"); shift; done
  [ "${1:-}" = -- ] && shift
  exact "$name" "$crate" "${args[@]}" -- --ignored "$@"
}

t rc-shell-private-enroll 50 resource-client --bin mini -- shell:: private:: participant_enrollment:: key_generation
t grain-provider          42 grain-runtime -- provider credential publication_refusal
t hermes-test-provider    15 hermes-test-provider -- tests::
t verifier-protocol       10 credential-signature-verifier --test protocol -- protocol_

# Landed defect fixes (R2-1 = scouts-20261003/R2-1-security-residuals-at-HEAD.txt,
# D = scouts-20261003/D-deos-efficiency-semantics.txt). One row per defect.
# R2-1 #1: SPK broker export symlink/parent race, fd-relative custody (76757030)
exact spk-volume-custody     spk-host --lib -- \
  broker::volume_custody::tests::volume_custody_symlink_switch_never_chowns_or_writes_victim \
  broker::volume_custody::tests::volume_custody_parent_switch_keeps_fd_relative_creation \
  broker::volume_custody::tests::volume_custody_hardlinks_and_nonprivate_directory_refuse \
  broker::volume_custody::tests::volume_custody_sparse_copy_hashes_retained_exact_bytes \
  broker::volume_custody::tests::volume_custody_failed_thaw_preserves_durable_repair_obligation \
  broker::volume_custody::tests::volume_custody_live_capture_lock_refuses_competing_recovery
# R2-1 #10 / C2 replay quota, C5 VABA view change, #8 private-backend torn tail (76757030)
exact private-backend-recovery private-backend --lib -- \
  authenticated_ingress::tests::byzantine_sender_quota_cannot_starve_honest_party_after_restart \
  vaba::tests::real_view_change_reorders_future_frames_and_faulty_equivocation_without_split \
  transition_journal::tests::replay_preserves_exact_outbox_and_recovers_incomplete_tail \
  transition_journal::tests::every_append_crash_cut_recovers_prior_prefix_and_replays_complete_record \
  transition_journal::tests::partial_initial_header_recovers_but_wrong_identity_refuses
# R2-1 #6: a Store behind its retained anchor head refuses reads and writes (4a34dcb1);
# the anchor's custody is the Store account's alone (W1.8, 1a75b4cc)
exact store-anchor-head      hyperdocument-link-sqlite-store --lib -- \
  anchor_tests::truncation_above_checkpoint_refuses_reads_and_writes \
  anchor_tests::explicit_deployment_identity_changes_refuse_at_genesis_and_head \
  anchor_tests::same_height_record_and_genesis_conflicts_refuse \
  anchor_tests::anchor_loss_refuses_until_explicit_enrollment_and_foreign_anchor_refuses \
  anchor_tests::whole_database_replacement_is_detected_by_sibling_anchor \
  anchor_tests::anchor_custody_refuses_a_foreign_owner_and_a_shared_directory
# D9-D11: Discord durable custody, mirror cursor after custody, paged backfill (bce707b7);
# the custody lease itself moved into mini-sdk (4b2f299d): row sdk-custody
exact discord-custody        discord-entrance --bin mini-discord-mirror --test endpoint -- \
  tests::outbound_pages_restart_and_unknown_never_repost \
  tests::channel_backfill_retains_all_115_across_restart_and_small_drains \
  durable_restart_exact_binding_unknown_and_roster_revocation \
  accepted_before_deferral_is_recoverable_and_status_is_actor_bound
# D9 / D2 as shared by the Mini SDK (5c88af84, 4b2f299d): the custody lease, numeric
# attempt history, and the outcome classification the client copies now share
exact sdk-custody            mini-sdk --lib --features native -- \
  store::tests::leases_survive_reopen_and_corruption_is_not_absence \
  store::tests::attempt_history_is_numeric_and_transport_metadata_is_not_an_outcome \
  store::tests::a_group_readable_directory_refuses \
  custody::tests::recovered_after_uncertain_is_confirmed_by_exact_lookup_never_a_new_nonce \
  custody::tests::refused_permits_one_successor_with_fresh_nonces_only \
  custody::tests::unsent_is_never_sent_but_unsent_after_uncertain_stays_uncertain \
  custody::tests::unknown_confirmation_words_and_malformed_receipts_are_undecided \
  custody::tests::classification_confirmation_wins_then_newest_refusal \
  custody::tests::delivery_unknown_is_resolved_only_by_evidence_never_by_resending
# resource-client (bin mini), one row per defect so a red names it
# D1: sparse board rendering never scans the address space (bce707b7)
exact rc-board-sparse        resource-client --bin mini -- \
  web::tests::board_rendering_visits_sparse_state_fields_without_address_scan
# D2: numeric retry order; metadata is never an outcome (3f81c7db)
exact rc-retry-order         resource-client --bin mini -- \
  workspace::tests::retry_metadata_and_five_digit_order_never_fabricate_a_terminal_refusal \
  workspace::tests::recovered_exact_readback_is_confirmed_despite_a_later_uncertain_lookup \
  publisher::tests::high_numbered_retained_outbox_confirmation_recovers_without_host_or_resubmit \
  retry_evidence::tests::metadata_and_partial_writes_reserve_their_attempt_without_becoming_outcomes \
  retry_evidence::tests::later_outcomes_remain_later_beyond_four_digits_and_legacy_padding_is_preserved \
  retry_evidence::tests::sparse_history_does_not_reuse_old_attempt_numbers \
  retry_evidence::tests::representational_exhaustion_refuses_without_wrapping_to_prior_evidence
# D3: a restarted Host is re-checked against its sealed pin (bce707b7, 3f81c7db)
exact rc-host-pin            resource-client --bin mini -- \
  transport::tests::socket_restart_refuses_replaced_host_under_original_pin \
  transport::tests::sealed_host_snapshot_survives_in_place_and_pathname_replacement \
  transport::tests::sealed_config_survives_mutation_and_restart_refuses_changed_settings
# D4 / R2-1 #7: rotation plan requires local identity, command and frame validation
exact rc-key-rotation        resource-client --bin mini -- \
  key_rotation::key_source_tests::protected_rotation_requires_local_identity_command_and_frame_validation
# D5: replan clears HostDecision between attempts (bce707b7)
exact rc-replan-decision     resource-client --bin mini -- \
  replan::tests::prior_stale_refusal_cannot_classify_the_next_lost_reply \
  replan::tests::earlier_command_refusal_does_not_authorize_this_attempt \
  replan::tests::successful_replan_does_not_leave_a_superseded_refusal \
  replan::tests::exact_readback_after_uncertain_cas_is_never_retired
# D7: a lost op162 settlement reply keeps the original ingress (3f81c7db);
# R2-1 #4b job-name traversal (96a4165f)
exact rc-job-settlement      resource-client --bin mini -- \
  job::path_tests::settlement_lost_reply_and_prior_uncertainty_keep_original_ingress \
  job::path_tests::settlement_lost_send_gap_survives_later_exact_native_refusal \
  job::path_tests::settlement_legacy_unknown_is_not_upgraded_by_later_refused_resend \
  job::path_tests::settlement_canonical_identity_refuses_another_job_subject_or_action \
  job::path_tests::job_record_updates_are_atomic_and_symlinks_never_read_or_written \
  job::path_tests::job_names_refuse_escape_before_any_directory_is_created
# D8: a fresh v2 worker upgrade is checked against the v2 pin (3f81c7db)
exact rc-drain-v2-pin        resource-client --bin mini -- \
  drain::tests::actual_upgrade_accepts_fresh_v2_and_legacy_v1_without_rebinding_call
# R2-1 #3: founder-pinned room-key lineage, epoch monotonicity, two-phase release
# (4564a8fa replaced the 3f81c7db tests); envelope rollback refused (8c67fc66)
exact rc-roomkey-lineage     resource-client --bin mini -- \
  workspace::roomkey::tests::founder_unsigned_or_foreign_wrap_set_is_refused \
  workspace::roomkey::tests::founder_and_member_pins_refuse_silent_replacement \
  workspace::roomkey::tests::older_or_equivocating_lineage_is_refused_and_never_selects_an_old_sealing_key \
  workspace::roomkey::tests::the_chain_starts_at_genesis_skips_burned_epochs_and_never_forks \
  workspace::roomkey::tests::recipient_signature_rejects_operator_substitution_and_unpinned_members \
  workspace::roomkey::tests::release_binds_records_then_reads_back_then_discloses_the_wrap \
  workspace::roomkey::tests::release_commitment_binds_the_complete_wrap_and_its_exact_address \
  workspace::roomkey::tests::a_stale_recipient_never_receives_a_wrap_of_an_already_used_key \
  workspace::roomkey::tests::a_refused_rotation_draft_is_dead_forever_and_its_epoch_is_never_selected \
  workspace::roomkey::tests::first_invite_signed_descriptor_pins_its_key_but_needs_no_prior_wrap_or_record \
  workspace::roomkey::tests::forgotten_epochs_are_not_relearned_and_the_cache_keeps_them_forgotten \
  workspace::protected_document::tests::protected_atom_edit_rollback_to_an_earlier_ciphertext_does_not_open
# R2-1 #10 / C4: the cohort link admits only roster members (d7b2f19b replaced the
# pre-shared-key adapter and its re-accept test from 76757030)
exact rc-cohort-roster       resource-client --bin mini -- \
  cohort_tcp::tests::registrar_enrollment_admits_only_roster_member_signature_under_fresh_challenge \
  cohort_tcp::tests::cohort_sender_refuses_receiver_without_roster_link_secret \
  cohort_tcp::tests::cohort_roster_digest_profile_and_shape_bind_every_link \
  cohort_tcp::tests::registrar_worker_refuses_input_directory_of_another_enrolled_slot
# R2-1 #10 / C4: a stalled stranger cannot tie up the cohort listener (restores the
# property d7b2f19b's re-accept test carried)
exact rc-cohort-stall        resource-client --bin mini -- \
  cohort_tcp::tests::a_stalled_stranger_cannot_tie_up_the_cohort_listener
# R2-1 R4/R5: credit reference stranding and renewal overflow (76757030)
exact rc-credit              resource-client --bin mini -- \
  credit::tests::renewal_overflow_refuses \
  credit::tests::interrupted_window_switch_retains_reference_and_recovers_note
# R2-1 #4b: tail --discover scope (96a4165f); terminal escapes (2b51b040)
exact rc-shell-confinement   resource-client --bin mini -- \
  chat::tests::operation_scope_preserves_resident_records_and_refuses_foreign_paths \
  render::text::terminal_tests::every_unicode_control_is_visible_without_terminal_control_bytes \
  render::text::terminal_tests::decorations_cannot_restore_terminal_sequences_via_link_names \
  render::text::terminal_tests::document_metadata_annotations_and_outline_are_terminal_safe
# R2-1 R6: hex decoders refuse malformed input without panicking (76757030)
exact rc-hex-decoders        resource-client --bin mini -- \
  ascii_hex_regression::refuses_non_ascii_without_panicking \
  relay::unhex_rejects_malformed_unicode_without_panicking \
  render::decode_hex_malformed_payload_retains_empty_fallback \
  render::history::payload_text_malformed_unicode_retains_diagnostic
# W1.8 tenancy (535fea1e, f86e394a): operator peer allowlist, tenant-group public
# socket, owner-private 32-byte signing keys, keycache passphrase kept from
# children, session paths confined to the session home
exact rc-tenancy             resource-client --bin mini -- \
  transport::tests::transport_operator_peers_default_to_owner_and_add_only_configured_uids \
  transport::tests::transport_operator_socket_refuses_a_peer_outside_the_allowlist \
  public_proxy::tests::transport_public_socket_group_directory_admits_only_group_search \
  tests::read_secret_requires_owner_private_regular_32_byte_file \
  workspace::private::tests::keycache_passphrase_leaves_the_environment_before_any_child \
  shell::session_fs::tests::session_fs_confined_refuses_links_and_special_leaves_and_linked_parents
# --- W1.9 ship-the-fixes rows (0191cb8a, re-applied as exact rows beside L0.4's).
# Grain journal publication through journal_io, in-process digests, plain status (6a291924)
exact grain-journal-digest   grain-runtime --bin grain-runtime -- \
  journal_io::tests::journal_actual_process_death_before_rename_recovers_committed_cut \
  journal_io::tests::journal_foreign_symlink_and_hardlink_refuse_without_changes \
  journal_io::tests::journal_orphan_temp_is_preserved_and_never_promoted \
  controller_digest::tests::controller_digest_standard_vectors \
  controller_digest::tests::controller_digest_stream_file_matches_original_bytes \
  public_status::tests::plain_status_projects_without_private_configuration_or_custody \
  tests::birth_ordinal_legacy_temp_does_not_fence_retained_marker_retirement
# A full-length torn final WAL record truncates like a short one (fa84160e)
exact private-transition-wal private-backend --lib -- \
  transition_journal::tests::zeroed_final_record_body_truncates_to_one_less_record \
  transition_journal::tests::invalid_event_has_no_effect_or_outbox
# One hex decoder (c158f9ba); rate budgets per IPv6 /64 with eviction (664ee3c4)
exact rc-hex-rate-limit      resource-client --bin mini -- \
  decode_hex_tests::decode_hex_refuses_non_ascii_sign_and_odd_input_without_panic \
  enrollment_bootstrap::tests::rate_limit_has_burst_minute_and_memory_bounds \
  enrollment_bootstrap::tests::one_ipv6_slash64_is_one_budget_and_cannot_lock_out_a_fresh_ipv4_client \
  enrollment_bootstrap::tests::spoofed_real_ip_cannot_bypass_quote_limit
# Operator `resolve` frees the slot of a dead lease holder (0c148911)
exact scheduler-resolve      inference-scheduler --test core -- \
  dead_lease_holder_frees_its_slot_only_by_operator_resolve
# Signing consent: a remote plan with one changed byte is refused before any key signs (W1.9 b45237d1)
exact consent-remote-plan    resource-client --bin mini -- \
  client_consent::tests::remote_signing_plan_with_one_changed_byte_is_refused_before_signing \
  client_consent::tests::consent_headers_preserve_duplicates_order_and_reject_unframed_values \
  client_consent::tests::consent_pair_preserves_exact_order_and_bounds \
  client_consent::tests::consent_round_trip_refusal_never_returns_header_bytes
# --- end W1.9 rows

# Private rooms (W1.9b 4564a8fa, 8c67fc66, d38116cd): the refusals the room lane
# added beside the lineage tests in rc-roomkey-lineage
exact rc-private-rooms       resource-client --bin mini -- \
  workspace::roomkey::tests::a_sealed_entry_is_bound_to_its_stream_and_position \
  workspace::roomkey::tests::non_member_cannot_open_a_sealed_entry \
  workspace::roomkey::tests::kicked_member_cannot_open_post_rotation_content_and_keeps_the_past \
  workspace::roomkey::tests::a_wrong_epoch_is_refused_by_name \
  workspace::roomkey::tests::a_malformed_wrap_or_release_atom_in_the_keys_cell_is_an_error_not_skipped \
  workspace::roomkey::tests::rotation_leaves_out_members_without_a_grant_and_needs_a_keyed_room \
  workspace::roomkey::tests::a_hosted_invitee_into_a_private_room_needs_i_know \
  workspace::private::tests::legacy_private_content_never_seals_and_only_strikes_retaining_ciphertext
# D15: a queued request whose caller left, or that outwaited its residence bound,
# is answered 254 and never reaches the Host (2a72f8ed)
exact rc-transport-queue     resource-client --bin mini -- \
  transport::tests::serve_a_queued_abandoned_request_never_reaches_the_host \
  transport::tests::serve_a_request_past_queue_residence_is_refused_254_unforwarded \
  transport::tests::serve_refuses_254_only_before_forward
# Mini SDK golden vectors: the offline core, Bread's dregg0 vector, and lowering a
# typed Invoke to the bytes of a real admitted intent (1f3794d4)
exact sdk-golden             mini-sdk --features native --test golden -- \
  golden_vectors_match_the_offline_core \
  bread_dregg0_vector_is_reproduced \
  lowering_reproduces_a_real_admitted_intent
# SUDO-ONLY (W1.8 two-uid tests, #[ignore]d: they run a probe as a second uid via
# `sudo -n setpriv`). Armed by MINI_TEST_FOREIGN_UID=<uid other than ours> on a
# runner with passwordless sudo; then they are ordinary exact rows (red on any
# failure, incl. sudo refusing). Unarmed, each run prints NOT-ARMED by name.
sudo_exact store-anchor-two-uid  hyperdocument-link-sqlite-store --lib -- \
  anchor_tests::anchor_rewritten_by_a_session_uid_refuses
sudo_exact rc-operator-two-uid   resource-client --bin mini -- \
  transport::tests::transport_operator_socket_two_uid_foreign_process_is_refused

if [ "$red" != 0 ]; then echo "rust-tests: FAIL: $red row(s) red"; exit 1; fi
echo "rust-tests: PASS"
