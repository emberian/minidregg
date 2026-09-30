//! Refusals that need no fixture directory, the config gate, and the curl transport against a
//! loopback server this test owns (no traffic leaves the host).

use std::io::{Read, Write};
use std::net::TcpListener;
use std::path::Path;
use std::thread;
use std::time::Duration;

use minidregg_pay_watcher::decode::{signatures_of, transaction_credit, TxOutcome};
use minidregg_pay_watcher::model::{base58, Key};
use minidregg_pay_watcher::transport::{fixture_key, validate_endpoint, CurlTransport, Transport};
use minidregg_pay_watcher::{Asset, Config, Reason};
use serde_json::{json, Value};

const T22: &str = "TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb";

fn k(b: u8) -> Key {
    [b; 32]
}

fn asset() -> Asset {
    Asset {
        mint: k(1),
        token_program: minidregg_pay_watcher::model::unbase58::<32>(T22).unwrap(),
    }
}

fn tx(sig: &[u8; 64], slot: u64, post_owner: Option<&str>) -> Value {
    let mut entry = json!({
        "accountIndex": 1, "mint": base58(&k(1)), "programId": T22,
        "uiTokenAmount": { "amount": "5" },
    });
    if let Some(o) = post_owner {
        entry["owner"] = json!(o);
    }
    json!({
        "slot": slot, "blockTime": 42,
        "meta": { "err": null, "preTokenBalances": [], "postTokenBalances": [entry] },
        "transaction": {
            "signatures": [base58(sig)],
            "message": { "accountKeys": [base58(&k(9)), base58(&k(3))] },
        },
    })
}

#[test]
fn a_transaction_for_another_signature_is_refused() {
    let asked = [5u8; 64];
    let answered = tx(&[6u8; 64], 10, Some(&base58(&k(2))));
    let e = transaction_credit(&answered, &asked, 10, &[k(3)], &asset(), &k(2)).unwrap_err();
    assert_eq!(e.reason, Reason::SignatureMismatch);
}

#[test]
fn a_transaction_at_another_slot_is_refused() {
    let sig = [5u8; 64];
    let e = transaction_credit(&tx(&sig, 11, Some(&base58(&k(2)))), &sig, 10, &[k(3)], &asset(), &k(2))
        .unwrap_err();
    assert_eq!(e.reason, Reason::SlotMismatch);
    assert!(e.detail.contains("slot 10, transaction says 11"));
}

#[test]
fn a_balance_without_owner_cannot_be_attributed() {
    let sig = [5u8; 64];
    let e = transaction_credit(&tx(&sig, 10, None), &sig, 10, &[k(3)], &asset(), &k(2)).unwrap_err();
    assert_eq!(e.reason, Reason::MalformedResponse);
    assert!(e.detail.contains("missing `owner`"), "{}", e.detail);
}

#[test]
fn a_well_formed_credit_decodes() {
    let sig = [5u8; 64];
    let got = transaction_credit(&tx(&sig, 10, Some(&base58(&k(2)))), &sig, 10, &[k(3)], &asset(), &k(2))
        .unwrap();
    assert_eq!(
        got,
        TxOutcome::Landed {
            slot: 10,
            block_time: 42,
            delta: 5
        }
    );
}

#[test]
fn a_signature_entry_without_a_slot_is_malformed_not_slot_zero() {
    let e = signatures_of(&json!([{ "signature": base58(&[1u8; 64]), "err": null }])).unwrap_err();
    assert_eq!(e.reason, Reason::MalformedResponse);
    assert!(e.detail.contains("missing `slot`"));
    let e = signatures_of(&json!([{ "signature": base58(&[1u8; 64]), "slot": 3,
        "confirmationStatus": "confirmed" }]))
    .unwrap_err();
    assert!(e.detail.contains("confirmationStatus"));
}

#[test]
fn fixture_requests_must_ask_for_finalized() {
    let e = fixture_key(
        "getTransaction",
        &json!(["x", { "encoding": "jsonParsed", "commitment": "confirmed", "maxSupportedTransactionVersion": 0 }]),
    )
    .unwrap_err();
    assert!(e.contains("not finalized"), "{e}");
    assert_eq!(
        fixture_key("getSignaturesForAddress", &json!(["acct", { "commitment": "finalized", "limit": 25, "before": "s" }]))
            .unwrap(),
        "getSignaturesForAddress/acct.before.s.json"
    );
}

#[test]
fn config_refuses_one_address_at_two_indices() {
    let a = base58(&k(4));
    let v = json!({
        "asset": { "mint": base58(&k(1)), "tokenProgram": T22 },
        "book": [{ "index": 0, "address": a }, { "index": 1, "address": a }],
        "receiptsDir": "r",
    });
    let e = Config::from_json(&v, Path::new("/")).unwrap_err();
    assert!(e.contains("appears twice"), "{e}");
    let mut v2 = v.clone();
    v2["book"] = json!([{ "index": 0, "address": a }]);
    v2["endpoints"] = json!(["https://x/"]);
    assert!(Config::from_json(&v2, Path::new("/")).unwrap_err().contains("unknown field"));
}

#[test]
fn endpoints_must_be_https_or_loopback_http() {
    assert!(validate_endpoint("https://rpc.example/?api-key=abc").is_ok());
    assert!(validate_endpoint("http://127.0.0.1:8899").is_ok());
    assert!(validate_endpoint("http://rpc.example/").is_err());
    assert!(validate_endpoint("https://user@rpc.example/").is_err());
    assert!(validate_endpoint("https://rpc.example/\"x").is_err());
    assert!(validate_endpoint("file:///etc/passwd").is_err());
}

/// One HTTP exchange on a loopback listener: returns what curl sent.
fn serve_once(listener: TcpListener, reply: Vec<u8>) -> thread::JoinHandle<Vec<u8>> {
    thread::spawn(move || {
        let (mut stream, _) = listener.accept().unwrap();
        stream.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
        let mut got = Vec::new();
        let mut buf = [0u8; 4096];
        loop {
            let n = stream.read(&mut buf).unwrap_or(0);
            if n == 0 {
                break;
            }
            got.extend_from_slice(&buf[..n]);
            if let Some(end) = got.windows(4).position(|w| w == b"\r\n\r\n") {
                let head = String::from_utf8_lossy(&got[..end]).to_ascii_lowercase();
                let len: usize = head
                    .lines()
                    .find_map(|l| l.strip_prefix("content-length:").map(|v| v.trim().parse().unwrap()))
                    .unwrap_or(0);
                if got.len() >= end + 4 + len {
                    break;
                }
            }
        }
        let mut response = format!(
            "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
            reply.len()
        )
        .into_bytes();
        response.extend_from_slice(&reply);
        stream.write_all(&response).unwrap();
        got
    })
}

fn spool(name: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!("pay-watcher-spool-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

#[test]
fn curl_transport_posts_one_request_and_returns_the_result() {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let port = listener.local_addr().unwrap().port();
    let server = serve_once(listener, br#"{"jsonrpc":"2.0","id":1,"result":1234}"#.to_vec());
    let dir = spool("ok");
    let t = CurlTransport::new("endpoint0", format!("http://127.0.0.1:{port}/?api-key=secret"), &dir)
        .unwrap();
    let got = t.call("getSlot", json!([{ "commitment": "finalized" }])).unwrap();
    assert_eq!(got, json!(1234));
    let sent = String::from_utf8(server.join().unwrap()).unwrap();
    assert!(sent.starts_with("POST /?api-key=secret HTTP/1.1"), "{sent}");
    assert!(sent.contains(r#""method":"getSlot""#), "{sent}");
    assert!(sent.contains(r#""commitment":"finalized""#), "{sent}");
    // The spool is cleaned up after the call.
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 0);
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn curl_transport_refuses_an_oversized_answer_and_surfaces_rpc_errors() {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let port = listener.local_addr().unwrap().port();
    let server = serve_once(listener, vec![b' '; 4096]);
    let dir = spool("big");
    let t = CurlTransport::new("endpoint0", format!("http://127.0.0.1:{port}/"), &dir)
        .unwrap()
        .with_bounds(Duration::from_secs(5), 1024);
    let e = t.call("getSlot", json!([{ "commitment": "finalized" }])).unwrap_err();
    assert_eq!(e.reason, Reason::Transport, "{e}");
    let _ = server.join();

    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let port = listener.local_addr().unwrap().port();
    let server = serve_once(
        listener,
        br#"{"jsonrpc":"2.0","id":1,"error":{"code":-32009,"message":"slot skipped"}}"#.to_vec(),
    );
    let t = CurlTransport::new("endpoint0", format!("http://127.0.0.1:{port}/"), &dir).unwrap();
    let e = t.call("getBlockTime", json!([7])).unwrap_err();
    assert_eq!(e.reason, Reason::RpcError);
    assert!(e.detail.contains("slot skipped"));
    let _ = server.join();
    let _ = std::fs::remove_dir_all(dir);
}
