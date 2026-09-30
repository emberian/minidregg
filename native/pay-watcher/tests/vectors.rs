//! The hostile fixture suite (PAY.md §3.1: "the contract is the test vectors"). Each test runs
//! the watcher over `fixtures/<vector>/` with its two endpoints and asserts the observations
//! AND the named reason. Each also checks the vector's `expect.json` (what the J-PAY-1 hook
//! reads) says the same thing, so the hook and this suite cannot drift apart.

use std::path::{Path, PathBuf};
use std::process::Command;

use minidregg_pay_watcher::model::{hex, unbase58};
use minidregg_pay_watcher::transport::{FixtureTransport, Transport};
use minidregg_pay_watcher::{load_receipts, run, Config, Event, Reason, Report};
use serde_json::Value;

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures").join(name)
}

fn run_vector(name: &str) -> Report {
    run_vector_with(name, &["a", "b"])
}

fn run_vector_with(name: &str, endpoints: &[&str]) -> Report {
    let dir = fixture(name);
    let cfg = Config::load(&dir.join("config.json")).expect("config loads");
    let owned: Vec<FixtureTransport> = endpoints
        .iter()
        .map(|e| FixtureTransport::new(dir.join("endpoints").join(e)))
        .collect();
    let transports: Vec<&dyn Transport> = owned.iter().map(|t| t as &dyn Transport).collect();
    let (receipts, receipt_events) = load_receipts(&cfg.receipts_dir).expect("receipts load");
    let mut report = run(&cfg, &transports, &receipts, &Default::default()).expect("a tip is agreed");
    report.events.splice(0..0, receipt_events);
    check_expect(name, &report);
    report
}

/// `run_vector` from a given cursor, without the expect check (for phased vectors).
fn run_vector_from(name: &str, cursor: &minidregg_pay_watcher::Cursor) -> Report {
    let dir = fixture(name);
    let cfg = Config::load(&dir.join("config.json")).expect("config loads");
    let owned: Vec<FixtureTransport> = ["a", "b"]
        .iter()
        .map(|e| FixtureTransport::new(dir.join("endpoints").join(e)))
        .collect();
    let transports: Vec<&dyn Transport> = owned.iter().map(|t| t as &dyn Transport).collect();
    let (receipts, receipt_events) = load_receipts(&cfg.receipts_dir).expect("receipts load");
    let mut report = run(&cfg, &transports, &receipts, cursor).expect("a tip is agreed");
    report.events.splice(0..0, receipt_events);
    check_expect(name, &report);
    report
}

/// `expect.json` = {exit, observations, reasons}: the exit the binary gives, the observation
/// count, and the SET of event reasons.
fn check_expect(name: &str, report: &Report) {
    let expect: Value =
        serde_json::from_slice(&std::fs::read(fixture(name).join("expect.json")).unwrap()).unwrap();
    assert_eq!(
        expect["observations"].as_u64().unwrap() as usize,
        report.observations.len(),
        "{name}: expect.json observation count"
    );
    assert_eq!(
        expect["exit"].as_u64().unwrap(),
        if report.refused() { 3 } else { 0 },
        "{name}: expect.json exit"
    );
    let mut want: Vec<&str> = expect["reasons"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| r.as_str().unwrap())
        .collect();
    want.sort();
    let mut got: Vec<&str> = report.events.iter().map(|e| e.reason.name()).collect();
    got.sort();
    got.dedup();
    assert_eq!(want, got, "{name}: expect.json reasons");
    // `memos`, one per observation in output order: "memo" (memo bytes emitted), "none" (memo
    // and memoError both null), or the memoError.
    let want: Vec<&str> = expect["memos"]
        .as_array()
        .unwrap()
        .iter()
        .map(|m| m.as_str().unwrap())
        .collect();
    let got: Vec<&str> = report
        .observations
        .iter()
        .map(|o| match (&o.memo, o.memo_error) {
            (Some(_), None) => "memo",
            (None, None) => "none",
            (None, Some(e)) => e.name(),
            (Some(_), Some(_)) => panic!("{name}: an observation with a memo AND a memoError"),
        })
        .collect();
    assert_eq!(want, got, "{name}: expect.json memos");
    if let Some(after) = expect.get("cursorAfter") {
        let got = serde_json::from_slice::<Value>(&minidregg_pay_watcher::cursor_json(&report.cursor))
            .unwrap();
        assert_eq!(&got["cursors"], after, "{name}: expect.json cursorAfter");
    }
}

fn only_reason(report: &Report, reason: Reason) -> &Event {
    let hits: Vec<&Event> = report.events.iter().filter(|e| e.reason == reason).collect();
    assert!(!hits.is_empty(), "no `{}` event in {:?}", reason.name(), report.events);
    hits[0]
}

fn sig_b58(text: &str) -> [u8; 64] {
    unbase58::<64>(text).unwrap()
}

#[test]
fn happy_emits_exactly_the_two_payments_with_raw_bytes() {
    let r = run_vector("happy");
    assert_eq!(r.tip.slot, 1000);
    assert_eq!(r.tip.block_time, 1759250000);
    assert_eq!(r.observations.len(), 2);
    let amounts: Vec<(u64, u64)> = r.observations.iter().map(|o| (o.slot, o.amount)).collect();
    assert_eq!(amounts, vec![(900, 1_000_000_000), (950, 250_000_000)]);
    let cfg = Config::load(&fixture("happy").join("config.json")).unwrap();
    for o in &r.observations {
        assert_eq!(o.index, 0);
        assert_eq!(o.address, cfg.book[0].address);
        assert_eq!(o.mint, cfg.asset.mint);
        assert_eq!(o.token_program, cfg.asset.token_program);
        assert_eq!(
            hex(&o.token_program),
            hex(&unbase58::<32>("TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb").unwrap())
        );
        // The JSON carries the 64 raw bytes as 128 hex digits, never base58 text.
        let j = o.to_json();
        assert_eq!(j["signature"].as_str().unwrap().len(), 128);
        assert_eq!(j["signature"].as_str().unwrap(), hex(&o.signature));
    }
    // Block time comes from getTransaction, not the tip.
    assert_eq!(r.observations[0].block_time, 1759250000 - 50);
    assert_eq!(only_reason(&r, Reason::FailedTransaction).kind, minidregg_pay_watcher::EventKind::Skipped);
    only_reason(&r, Reason::ZeroDelta);
    assert_eq!(only_reason(&r, Reason::NoTokenAccount).index, Some(1));
    assert!(!r.refused());
}

#[test]
fn wrong_program_owner_on_the_post_balance_is_refused_not_skipped() {
    let r = run_vector("wrong-program");
    assert!(r.observations.is_empty());
    let e = only_reason(&r, Reason::WrongTokenProgram);
    assert!(e.detail.contains("POST balance programId"), "{}", e.detail);
    assert!(e.detail.contains("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA"), "{}", e.detail);
    assert_eq!(e.index, Some(0));
    assert!(r.refused());
}

#[test]
fn wrong_program_owner_on_the_token_account_is_refused() {
    let r = run_vector("wrong-program-account");
    assert!(r.observations.is_empty());
    let e = only_reason(&r, Reason::WrongTokenProgram);
    assert!(e.detail.contains("token account owner program"), "{}", e.detail);
}

#[test]
fn wrong_mint_is_refused() {
    let r = run_vector("wrong-mint");
    assert!(r.observations.is_empty());
    assert!(only_reason(&r, Reason::WrongMint).detail.contains("POST balance mint"));
}

#[test]
fn token_owner_another_wallet_is_refused() {
    let r = run_vector("other-owner");
    assert!(r.observations.is_empty());
    assert!(only_reason(&r, Reason::WrongTokenOwner).detail.contains("POST balance owner"));
}

#[test]
fn zero_delta_is_skipped() {
    let r = run_vector("zero-delta");
    assert!(r.observations.is_empty());
    let e = only_reason(&r, Reason::ZeroDelta);
    assert!(e.signature.is_some() && e.endpoint.is_none());
    assert!(!r.refused());
}

#[test]
fn failed_transaction_is_skipped() {
    let r = run_vector("failed-tx");
    assert!(r.observations.is_empty());
    assert_eq!(only_reason(&r, Reason::FailedTransaction).detail, "meta.err is non-null");
}

#[test]
fn pruned_transaction_is_refused() {
    let r = run_vector("pruned");
    assert!(r.observations.is_empty());
    let e = only_reason(&r, Reason::PrunedTransaction);
    assert!(e.detail.contains("result is null"));
    assert!(r.refused());
}

#[test]
fn pre_post_disagreement_is_refused() {
    let r = run_vector("pre-post-disagree");
    assert!(r.observations.is_empty());
    assert!(only_reason(&r, Reason::BalanceEntriesDisagree).detail.contains("disagree"));
}

#[test]
fn out_of_range_account_index_is_refused() {
    let r = run_vector("index-out-of-range");
    assert!(r.observations.is_empty());
    assert!(only_reason(&r, Reason::AccountIndexOutOfRange)
        .detail
        .contains("accountIndex 9 out of range for 5 account keys"));
}

#[test]
fn a_retained_signature_is_not_fetched_and_does_not_stop_paging() {
    let r = run_vector("retained");
    // pay-1 is older than the receipt and unreceipted: paging did not stop at the receipt.
    let slots: Vec<u64> = r.observations.iter().map(|o| o.slot).collect();
    assert_eq!(slots, vec![900, 990]);
    let e = only_reason(&r, Reason::AlreadyRetained);
    // The receipt was named in hex; the RPC spelled the signature in base58. Same bytes.
    let receipts: Vec<String> = std::fs::read_dir(fixture("retained").join("receipts"))
        .unwrap()
        .map(|d| d.unwrap().file_name().into_string().unwrap())
        .filter(|n| !n.starts_with('.'))
        .collect();
    assert_eq!(receipts.len(), 1);
    let address = r.observations[0].address;
    assert_eq!(format!("{}.{}", hex(&e.signature.unwrap()), hex(&address)), receipts[0]);
    // Fetching the retained pay-2 would have hit a missing fixture and refused `transport`.
    assert!(!r.refused(), "{:?}", r.events);
}

/// The refuting pole of the receipt key: the same signature retained for ANOTHER address is
/// not a receipt here. One transaction can pay two book rows; a receipt for one must not skip
/// the other, or its credit is never read again (the P1 finding (A) failure, moved to receipts).
#[test]
fn a_receipt_for_the_same_signature_at_another_address_does_not_skip_the_fetch() {
    let dir = scratch("receipt-other-address");
    let vector = dir.join("vector");
    copy_dir(&fixture("retained"), &vector);
    let receipts_dir = vector.join("receipts");
    let original: Vec<String> = std::fs::read_dir(&receipts_dir)
        .unwrap()
        .map(|d| d.unwrap().file_name().into_string().unwrap())
        .filter(|n| !n.starts_with('.'))
        .collect();
    assert_eq!(original.len(), 1);
    let (signature, _) = original[0].split_once('.').unwrap();
    std::fs::remove_file(receipts_dir.join(&original[0])).unwrap();
    std::fs::write(receipts_dir.join(format!("{signature}.{}", hex(&[7u8; 32]))), b"").unwrap();
    let cfg = Config::load(&vector.join("config.json")).unwrap();
    let owned: Vec<FixtureTransport> = ["a", "b"]
        .iter()
        .map(|e| FixtureTransport::new(vector.join("endpoints").join(e)))
        .collect();
    let transports: Vec<&dyn Transport> = owned.iter().map(|t| t as &dyn Transport).collect();
    let (receipts, events) = load_receipts(&cfg.receipts_dir).unwrap();
    assert!(events.is_empty(), "{events:?}");
    assert_eq!(receipts.len(), 1);
    let report = run(&cfg, &transports, &receipts, &Default::default()).unwrap();
    // pay-2 was fetched: the fixture has no answer for it, so the index refuses `transport`.
    assert!(report.events.iter().all(|e| e.reason != Reason::AlreadyRetained));
    assert!(report.events.iter().any(|e| e.reason == Reason::Transport && e.index == Some(0)));
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn a_bare_signature_is_not_a_receipt() {
    let dir = scratch("receipt-bare-signature");
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join(hex(&[1u8; 64])), b"").unwrap();
    std::fs::write(dir.join(format!("{}.{}", hex(&[1u8; 64]), hex(&[2u8; 32]))), b"").unwrap();
    let (receipts, events) = load_receipts(&dir).unwrap();
    assert_eq!(receipts.into_iter().collect::<Vec<_>>(), vec![([1u8; 64], [2u8; 32])]);
    assert_eq!(events.len(), 1);
    assert_eq!(events[0].reason, Reason::IgnoredReceiptName);
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn the_same_signature_twice_is_one_observation() {
    let r = run_vector("same-signature");
    assert_eq!(r.observations.len(), 2, "{:?}", r.events);
    let amounts: Vec<u64> = r.observations.iter().map(|o| o.amount).collect();
    // pay-2 credits both of the owner's token accounts: one observation of the sum.
    assert_eq!(amounts, vec![1_000_000_000, 350_000_000]);
    let sigs: std::collections::BTreeSet<[u8; 64]> =
        r.observations.iter().map(|o| o.signature).collect();
    assert_eq!(sigs.len(), 2);
    let dups: Vec<&Event> = r
        .events
        .iter()
        .filter(|e| e.reason == Reason::DuplicateSignature)
        .collect();
    // Each endpoint lists pay-1 twice (overlapping pages) and pay-2 twice (two accounts).
    assert_eq!(dups.len(), 4);
    assert!(only_reason(&r, Reason::IgnoredReceiptName).detail.contains("not-a-signature"));
}

#[test]
fn a_base58_signature_that_is_not_64_bytes_is_refused_not_truncated() {
    // Base58 is a bijection: the 64 raw bytes have one spelling. An extra leading `1` is an
    // extra zero byte, 65 bytes, and is refused rather than read as an alias of the 64.
    let b58 = minidregg_pay_watcher::model::base58(&[7u8; 64]);
    assert_eq!(sig_b58(&b58), [7u8; 64]);
    assert!(unbase58::<64>(&format!("1{b58}")).is_none());
    let e = minidregg_pay_watcher::model::parse_sig(&format!("1{b58}"), "signature entry").unwrap_err();
    assert_eq!(e.reason, Reason::MalformedResponse);
    assert!(e.detail.contains("not a 64-byte base58 signature"));
}

#[test]
fn two_endpoints_disagreeing_on_amount_emit_nothing_and_log_both() {
    let r = run_vector("disagree");
    assert!(r.observations.is_empty());
    let e = only_reason(&r, Reason::EndpointsDisagree);
    assert!(e.detail.contains("a: credit slot=900 blockTime=1759249950 amount=1000000000"), "{}", e.detail);
    assert!(e.detail.contains("b: credit slot=900 blockTime=1759249950 amount=2000000000"), "{}", e.detail);
    assert!(r.refused());
}

#[test]
fn one_endpoint_is_below_min_endpoints() {
    let dir = fixture("happy");
    let cfg = Config::load(&dir.join("config.json")).unwrap();
    let a = FixtureTransport::new(dir.join("endpoints").join("a"));
    let err = run(&cfg, &[&a as &dyn Transport], &Default::default(), &Default::default()).err().unwrap();
    assert_eq!(err.reason, Reason::Transport);
    assert!(err.detail.contains("minEndpoints is 2"));
}

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("pay-watcher-test-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// A private copy of a vector directory: the binary writes the enrollment cursor beside its
/// config, and a fixture must never be written by the run that reads it.
fn copy_dir(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).unwrap();
    for entry in std::fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let target = to.join(entry.file_name());
        let meta = std::fs::symlink_metadata(entry.path()).unwrap();
        if meta.file_type().is_symlink() {
            std::os::unix::fs::symlink(std::fs::read_link(entry.path()).unwrap(), &target).unwrap();
        } else if meta.is_dir() {
            copy_dir(&entry.path(), &target);
        } else {
            std::fs::copy(entry.path(), &target).unwrap();
        }
    }
}

fn run_binary(vector: &str, out: &Path) -> (i32, String) {
    let copy = out.join("vector");
    let _ = std::fs::remove_dir_all(&copy);
    copy_dir(&fixture(vector), &copy);
    run_binary_in(&copy, out)
}

/// Run the binary on a vector directory in place (the caller owns it).
fn run_binary_in(dir: &Path, out: &Path) -> (i32, String) {
    let dir = dir.to_path_buf();
    let output = Command::new(env!("CARGO_BIN_EXE_pay-watcher"))
        .env_remove("PAY_RPC_ENDPOINTS")
        .arg("--config")
        .arg(dir.join("config.json"))
        .arg("--out")
        .arg(out)
        .arg("--rpc-fixture")
        .arg(dir.join("endpoints/a"))
        .arg("--rpc-fixture")
        .arg(dir.join("endpoints/b"))
        .output()
        .unwrap();
    (
        output.status.code().unwrap(),
        String::from_utf8(output.stdout).unwrap(),
    )
}

#[test]
fn a_restart_on_the_same_answers_and_receipts_is_byte_identical() {
    let first = scratch("restart-1");
    let second = scratch("restart-2");
    assert_eq!(run_binary("happy", &first).0, 0);
    assert_eq!(run_binary("happy", &second).0, 0);
    for file in ["observations.json", "events.json"] {
        let a = std::fs::read(first.join(file)).unwrap();
        let b = std::fs::read(second.join(file)).unwrap();
        assert!(!a.is_empty());
        assert_eq!(a, b, "{file} differs across a restart");
    }
    // And the file is the library's own rendering.
    let report = run_vector("happy");
    assert_eq!(std::fs::read(first.join("observations.json")).unwrap(), report.observations_json());
    let parsed: Value =
        serde_json::from_slice(&std::fs::read(first.join("observations.json")).unwrap()).unwrap();
    assert_eq!(parsed["observations"].as_array().unwrap().len(), 2);
    assert_eq!(parsed["tip"]["slot"], 1000);
    let _ = std::fs::remove_dir_all(first);
    let _ = std::fs::remove_dir_all(second);
}

#[test]
fn every_vector_gives_the_binary_exit_its_expect_json_names() {
    for entry in std::fs::read_dir(fixture("")).unwrap() {
        let path = entry.unwrap().path();
        // Phased vectors (enrol-cursor) keep their phases in subdirectories; tests/enrol.rs.
        if !path.is_dir() || !path.join("expect.json").exists() {
            continue;
        }
        let name = path.file_name().unwrap().to_str().unwrap().to_owned();
        let expect: Value =
            serde_json::from_slice(&std::fs::read(path.join("expect.json")).unwrap()).unwrap();
        let out = scratch(&format!("exit-{name}"));
        let (code, stdout) = run_binary(&name, &out);
        assert_eq!(code as u64, expect["exit"].as_u64().unwrap(), "{name}: {stdout}");
        let obs: Value =
            serde_json::from_slice(&std::fs::read(out.join("observations.json")).unwrap()).unwrap();
        assert_eq!(
            obs["observations"].as_array().unwrap().len() as u64,
            expect["observations"].as_u64().unwrap(),
            "{name}"
        );
        let _ = std::fs::remove_dir_all(out);
    }
}

// Enrollment (PAY.md §11.9, J-PAY-E1) ----------------------------------------------------------

use minidregg_pay_watcher::{cursor_json, load_cursor, Cursor, MemoError};

/// The memo text a fixture transaction carries, read straight from the fixture JSON (top-level
/// and inner instructions), independently of the watcher's extraction.
fn fixture_memos(vector: &str, sig: &[u8; 64]) -> Vec<String> {
    let path = fixture(vector)
        .join("endpoints/a/getTransaction")
        .join(format!("{}.json", minidregg_pay_watcher::model::base58(sig)));
    let tx: Value = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    let r = &tx["result"];
    let mut ixs: Vec<&Value> = r["transaction"]["message"]["instructions"].as_array().unwrap().iter().collect();
    for group in r["meta"]["innerInstructions"].as_array().unwrap() {
        ixs.extend(group["instructions"].as_array().unwrap());
    }
    ixs.iter()
        .filter(|ix| ix["program"] == "spl-memo")
        .map(|ix| ix["parsed"].as_str().unwrap().to_owned())
        .collect()
}

fn memo_text(o: &minidregg_pay_watcher::Observation) -> String {
    String::from_utf8(o.memo.clone().expect("a memo")).unwrap()
}

#[test]
fn enrolment_memos_top_level_inner_and_legacy_are_emitted_byte_exact() {
    let r = run_vector("enrol-happy");
    assert!(!r.refused(), "{:?}", r.events);
    let enrol: Vec<_> = r.observations.iter().filter(|o| o.index == 0).collect();
    assert_eq!(enrol.len(), 5);
    for o in &enrol {
        let text = memo_text(o);
        assert_eq!(fixture_memos("enrol-happy", &o.signature), vec![text.clone()]);
        assert_eq!(text.len(), 400, "the §11.3 grammar's size");
        assert!(text.starts_with("enrol:v1:"));
        assert_eq!(o.to_json()["memo"].as_str().unwrap(), hex(text.as_bytes()));
    }
    // Alice's memo twice: two observations, two signatures; the kernel decides renewal.
    assert_eq!(enrol[0].memo, enrol[4].memo);
    assert_ne!(enrol[0].signature, enrol[4].signature);
    // Exactly the floor is emitted: the watcher does not know the price.
    assert_eq!(enrol[3].amount, 1_000_000);
    // The ordinary row: its memo is never read.
    let plain = r.observations.iter().find(|o| o.index == 1).unwrap();
    assert_eq!(plain.to_json()["memo"], Value::Null);
    assert_eq!(plain.to_json()["memoError"], Value::Null);
}

#[test]
fn a_memo_in_another_transaction_is_not_joined_to_the_transfer() {
    let r = run_vector("enrol-memo-other-tx");
    assert_eq!(r.observations.len(), 1);
    assert_eq!((r.observations[0].memo.as_ref(), r.observations[0].memo_error), (None, None));
    only_reason(&r, Reason::ZeroDelta);
}

#[test]
fn memo_less_payments_are_emitted_with_memo_null_and_a_bounce_is_skipped() {
    let r = run_vector("enrol-no-memo");
    let got: Vec<u64> = r.observations.iter().map(|o| o.amount).collect();
    assert_eq!(got, vec![7_000_000_000, 2_000_000_000]);
    assert!(r.observations.iter().all(|o| o.memo.is_none() && o.memo_error.is_none()));
    assert_eq!(only_reason(&r, Reason::FailedTransaction).detail, "signature list reports err");
}

#[test]
fn the_memo_binds_only_when_it_is_the_one_utf8_memo_within_566_bytes() {
    let r = run_vector("enrol-memo-bind");
    let by_slot: Vec<(u64, Option<usize>, Option<MemoError>)> = r
        .observations
        .iter()
        .map(|o| (o.slot, o.memo.as_ref().map(Vec::len), o.memo_error))
        .collect();
    assert_eq!(
        by_slot,
        vec![
            (900, None, Some(MemoError::Unbound)),
            (910, None, Some(MemoError::Unbound)),
            (920, None, Some(MemoError::Unbound)),
            (930, None, Some(MemoError::Invalid)),
            (940, None, Some(MemoError::Invalid)),
            (950, Some(566), None),
            (960, Some(400), None),
            (970, Some(22), None),
        ]
    );
    // A grammar the kernel will refuse is still the chain's bytes, emitted verbatim.
    assert!(memo_text(&r.observations[6]).starts_with("enrol:v2:"));
    assert_eq!(memo_text(&r.observations[7]), "hello, please enrol me");
    // Every unbound/invalid memo is journaled with the bytes, for ember to comp by hand.
    let notes: Vec<&Event> = r
        .events
        .iter()
        .filter(|e| matches!(e.reason, Reason::MemoUnbound | Reason::MemoInvalid))
        .collect();
    assert_eq!(notes.len(), 5);
    assert!(notes.iter().all(|e| e.kind == minidregg_pay_watcher::EventKind::Noted));
    assert!(notes.iter().any(|e| e.detail.contains("[\"thanks!\", \"enrol:v1:")), "{notes:?}");
    assert!(notes.iter().any(|e| e.detail.contains("hex:656e726f6c3a76313aff")), "{notes:?}");
    assert!(!r.refused());
}

#[test]
fn dust_below_the_journal_floor_is_recorded_and_not_emitted() {
    let r = run_vector("enrol-dust");
    assert_eq!(r.observations.len(), 1);
    assert_eq!(r.observations[0].amount, 1_000_000);
    let mut floors: Vec<&str> = r
        .events
        .iter()
        .filter(|e| e.reason == Reason::BelowJournalFloor)
        .map(|e| e.detail.as_str())
        .collect();
    floors.sort();
    assert_eq!(floors, vec!["amount 1 < journalFloor 1000000", "amount 999999 < journalFloor 1000000"]);
}

#[test]
fn one_transaction_paying_index_0_and_5_is_two_observations_with_the_memo_on_0_only() {
    let r = run_vector("enrol-shared-tx");
    let got: Vec<(u64, u64, bool)> =
        r.observations.iter().map(|o| (o.index, o.amount, o.memo.is_some())).collect();
    assert_eq!(got, vec![(0, 5_000_000_000, true), (5, 2_000_000_000, false)]);
    assert_eq!(r.observations[0].signature, r.observations[1].signature);
}

#[test]
fn endpoints_disagreeing_on_memo_bytes_emit_nothing() {
    let r = run_vector("enrol-disagree");
    assert!(r.observations.is_empty());
    let d: Vec<&Event> = r.events.iter().filter(|e| e.reason == Reason::EndpointsDisagree).collect();
    assert_eq!(d.len(), 2, "{d:?}");
    // enrol-2: the texts differ only in the case of the mini key; the watcher does not parse, so
    // it does not know they "mean" the same key, and it never picks one endpoint's bytes.
    let case = d.iter().find(|e| e.detail.contains("slot=940")).unwrap();
    let mini = |side: &str| -> String {
        let at = case.detail.find(side).unwrap();
        let from = at + case.detail[at..].find("enrol:v1:").unwrap() + "enrol:v1:".len();
        case.detail[from..from + 64].to_owned()
    };
    let (a, b) = (mini("a: "), mini("b: "));
    assert_eq!(a.to_lowercase(), a);
    assert_eq!(b.to_uppercase(), b);
    assert_eq!(a, b.to_lowercase(), "the same key, spelled two ways");
    assert!(r.refused());
}

#[test]
fn the_enrollment_index_pages_past_max_pages_to_an_enrolment_behind_dust() {
    let r = run_vector("enrol-behind-dust");
    assert_eq!(r.observations.len(), 1);
    assert_eq!(r.observations[0].slot, 900);
    assert!(r.events.iter().all(|e| e.reason != Reason::PageBound));
}

#[test]
fn the_cursor_moves_only_over_settled_listings() {
    // Nothing receipted: the oldest listing is an emitted credit, so the cursor stays put.
    let first = run_vector("enrol-happy");
    assert!(first.cursor.is_empty());
    // With the two oldest receipted (the kernel accepted them), it moves to the second.
    let dir = scratch("cursor-receipts");
    let vector = dir.join("vector");
    copy_dir(&fixture("enrol-happy"), &vector);
    let enrol: Vec<([u8; 64], [u8; 32])> = first
        .observations
        .iter()
        .filter(|o| o.index == 0)
        .map(|o| (o.signature, o.address))
        .collect();
    for (s, a) in &enrol[..2] {
        std::fs::write(vector.join("receipts").join(format!("{}.{}", hex(s), hex(a))), b"").unwrap();
    }
    let cfg = Config::load(&vector.join("config.json")).unwrap();
    let owned: Vec<FixtureTransport> = ["a", "b"]
        .iter()
        .map(|e| FixtureTransport::new(vector.join("endpoints").join(e)))
        .collect();
    let transports: Vec<&dyn Transport> = owned.iter().map(|t| t as &dyn Transport).collect();
    let (receipts, _) = load_receipts(&cfg.receipts_dir).unwrap();
    let second = run(&cfg, &transports, &receipts, &Cursor::new()).unwrap();
    assert_eq!(second.cursor.values().collect::<Vec<_>>(), vec![&enrol[1].0]);
    assert_eq!(second.observations.iter().filter(|o| o.index == 0).count(), 3);
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn endpoints_listing_one_slot_in_different_orders_hold_the_cursor() {
    let r = run_vector("enrol-cursor-held");
    assert!(r.cursor.is_empty());
    assert!(only_reason(&r, Reason::CursorHeld).detail.contains("list it differently"));
}

#[test]
fn the_cursor_finds_an_enrolment_after_300_dust_across_two_runs() {
    let p1 = run_vector_from("enrol-cursor/phase1", &Cursor::new());
    check_expect("enrol-cursor/phase1", &p1);
    assert_eq!(p1.events.iter().filter(|e| e.reason == Reason::BelowJournalFloor).count(), 300);
    let p2 = run_vector_from("enrol-cursor/phase2", &p1.cursor);
    check_expect("enrol-cursor/phase2", &p2);
    assert_eq!(p2.observations[0].slot, 1050);
    // Without the cursor phase 2 would list and fetch the dust again, and its fixture holds no
    // such answers: the cursor is what makes this run possible, not an optimisation beside it.
    let dir = fixture("enrol-cursor/phase2");
    let cfg = Config::load(&dir.join("config.json")).unwrap();
    let owned: Vec<FixtureTransport> =
        ["a", "b"].iter().map(|e| FixtureTransport::new(dir.join("endpoints").join(e))).collect();
    let transports: Vec<&dyn Transport> = owned.iter().map(|t| t as &dyn Transport).collect();
    let blind = run(&cfg, &transports, &Default::default(), &Cursor::new()).unwrap();
    assert!(blind.observations.is_empty());
    assert_eq!(only_reason(&blind, Reason::Transport).index, Some(0));
}

#[test]
fn the_binary_writes_the_cursor_and_the_next_run_reads_it() {
    let dir = scratch("cursor-binary");
    let vector = dir.join("enrol-cursor");
    copy_dir(&fixture("enrol-cursor"), &vector);
    let cursor_file = vector.join("cursor.json");
    assert!(!cursor_file.exists());
    let out1 = dir.join("out1");
    std::fs::create_dir_all(&out1).unwrap();
    assert_eq!(run_binary_in(&vector.join("phase1"), &out1).0, 0);
    let cursor = load_cursor(&cursor_file).unwrap();
    assert_eq!(cursor.len(), 1);
    let out2 = dir.join("out2");
    std::fs::create_dir_all(&out2).unwrap();
    assert_eq!(run_binary_in(&vector.join("phase2"), &out2).0, 0);
    let obs: Value =
        serde_json::from_slice(&std::fs::read(out2.join("observations.json")).unwrap()).unwrap();
    assert_eq!(obs["observations"].as_array().unwrap().len(), 1);
    assert_eq!(std::fs::read(&cursor_file).unwrap(), cursor_json(&cursor));
    // A malformed cursor refuses to load (exit 2), never reads as "no cursor".
    std::fs::write(&cursor_file, b"{\"cursors\": {\"zz\": \"00\"}}").unwrap();
    assert_eq!(run_binary_in(&vector.join("phase2"), &dir.join("out3")).0, 2);
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn a_restart_of_the_enrolment_vector_is_byte_identical() {
    let first = scratch("restart-enrol-1");
    let second = scratch("restart-enrol-2");
    assert_eq!(run_binary("enrol-happy", &first).0, 0);
    assert_eq!(run_binary("enrol-happy", &second).0, 0);
    for file in ["observations.json", "events.json", "vector/enrol-cursor.json"] {
        assert_eq!(
            std::fs::read(first.join(file)).unwrap(),
            std::fs::read(second.join(file)).unwrap(),
            "{file} differs across a restart"
        );
    }
    let _ = std::fs::remove_dir_all(first);
    let _ = std::fs::remove_dir_all(second);
}

#[test]
fn the_enrol_config_names_a_book_row_and_has_no_default_floor() {
    let base = json_config();
    let load = |enrol: Value| {
        let mut v = base.clone();
        v["enrol"] = enrol;
        Config::from_json(&v, Path::new("/cfg"))
    };
    let ok = load(serde_json::json!({ "index": 0, "journalFloor": 1000000 })).unwrap();
    let e = ok.enrol.unwrap();
    assert_eq!((e.index, e.journal_floor), (0, 1_000_000));
    assert_eq!(e.cursor_file, Path::new("/cfg/enrol-cursor.json"));
    assert!(load(serde_json::json!({ "index": 7, "journalFloor": 1 })).unwrap_err().contains("names no book row"));
    assert!(load(serde_json::json!({ "index": 0 })).unwrap_err().contains("journalFloor"));
    assert!(load(serde_json::json!({ "index": 0, "journalFloor": 1, "memo": true }))
        .unwrap_err()
        .contains("unknown field `memo`"));
}

fn json_config() -> Value {
    serde_json::from_slice(&std::fs::read(fixture("happy").join("config.json")).unwrap()).unwrap()
}
