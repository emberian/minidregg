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
    let mut report = run(&cfg, &transports, &receipts).expect("a tip is agreed");
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
fn a_retained_signature_is_skipped_and_stops_paging() {
    let r = run_vector("retained");
    assert_eq!(r.observations.len(), 1);
    assert_eq!(r.observations[0].slot, 990);
    let e = only_reason(&r, Reason::AlreadyRetained);
    // The receipt was named in hex; the RPC spelled the signature in base58. Same bytes.
    let receipts: Vec<String> = std::fs::read_dir(fixture("retained").join("receipts"))
        .unwrap()
        .map(|d| d.unwrap().file_name().into_string().unwrap())
        .filter(|n| !n.starts_with('.'))
        .collect();
    assert_eq!(receipts.len(), 1);
    assert_eq!(hex(&e.signature.unwrap()), receipts[0]);
    // Reading past the receipt would have hit a missing fixture and refused `transport`.
    assert!(!r.refused(), "{:?}", r.events);
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
    let err = run(&cfg, &[&a as &dyn Transport], &Default::default()).err().unwrap();
    assert_eq!(err.reason, Reason::Transport);
    assert!(err.detail.contains("minEndpoints is 2"));
}

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("pay-watcher-test-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn run_binary(vector: &str, out: &Path) -> (i32, String) {
    let dir = fixture(vector);
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
        if !path.is_dir() {
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
