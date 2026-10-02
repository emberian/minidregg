//! V1 fixtures are transformations of the retained public RPC captures. They
//! exercise the complete agreement/cursor path without touching the network.
//! Schema source checked 2026-10-02: https://solana.com/docs/rpc/json-structures.
use minidregg_pay_watcher::decode::MAX_SUPPORTED_TRANSACTION_VERSION;
use minidregg_pay_watcher::model::{Key, Refusal};
use minidregg_pay_watcher::transport::{fixture_key, rpc_result, FixtureTransport, Transport};
use minidregg_pay_watcher::{load_receipts, run, Config, Cursor, Reason, Report};
use serde_json::{json, Value};
use std::path::Path;

#[derive(Clone, Copy)]
enum Format {
    Legacy,
    V0,
    V1,
    Future,
    MissingConfig,
    RpcUnsupported,
    Disagree,
}

struct Capture {
    inner: FixtureTransport,
    format: Format,
}
impl Transport for Capture {
    fn label(&self) -> &str {
        self.inner.label()
    }
    fn call(&self, method: &str, params: Value) -> Result<Value, Refusal> {
        if method == "getTransaction" {
            assert_eq!(
                params[1]["maxSupportedTransactionVersion"],
                MAX_SUPPORTED_TRANSACTION_VERSION
            );
            if matches!(self.format, Format::RpcUnsupported) {
                return rpc_result(json!({"jsonrpc":"2.0","id":1,"error":{
                    "code":-32015,"message":"Transaction version is not supported"}}));
            }
        }
        let mut result = self.inner.call(method, params)?;
        if method != "getTransaction" || result.is_null() {
            return Ok(result);
        }
        let version = match self.format {
            Format::Legacy => json!("legacy"),
            Format::V0 => json!(0),
            Format::Future => json!(2),
            _ => json!(1),
        };
        result["version"] = version;
        if matches!(self.format, Format::V1 | Format::Disagree) {
            result["transaction"]["message"]["transactionConfig"] = config();
        }
        if matches!(self.format, Format::Disagree) {
            if let Some(post) = result["meta"]["postTokenBalances"].as_array_mut() {
                for row in post {
                    let amount = row["uiTokenAmount"]["amount"]
                        .as_str()
                        .unwrap()
                        .parse::<u64>()
                        .unwrap();
                    row["uiTokenAmount"]["amount"] = json!((amount + 1).to_string());
                }
            }
        }
        Ok(result)
    }
}
fn config() -> Value {
    json!({"computeUnitLimit":30000,"heapSize":null,
        "loadedAccountsDataSizeLimit":200000,"priorityFee":null})
}
fn captures(a: Format, b: Format, cursor: &Cursor) -> Report {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/enrol-happy");
    let cfg = Config::load(&dir.join("config.json")).unwrap();
    let a = Capture {
        inner: FixtureTransport::new(dir.join("endpoints/a")),
        format: a,
    };
    let b = Capture {
        inner: FixtureTransport::new(dir.join("endpoints/b")),
        format: b,
    };
    let (receipts, _) = load_receipts(&cfg.receipts_dir).unwrap();
    run(&cfg, &[&a, &b], &receipts, cursor).unwrap()
}
#[test]
fn v1_keeps_exact_credit_memo_and_endpoint_agreement() {
    let legacy = captures(Format::Legacy, Format::Legacy, &Cursor::new());
    for (a, b) in [
        (Format::V0, Format::V0),
        (Format::V1, Format::V1),
        (Format::V0, Format::V1),
    ] {
        let modern = captures(a, b, &Cursor::new());
        assert!(!modern.refused(), "{:?}", modern.events);
        assert_eq!(
            modern
                .observations
                .iter()
                .map(|o| o.to_json())
                .collect::<Vec<_>>(),
            legacy
                .observations
                .iter()
                .map(|o| o.to_json())
                .collect::<Vec<_>>()
        );
        assert_eq!(modern.cursor, legacy.cursor);
        assert_eq!(
            modern.observations.iter().filter(|o| o.index == 0).count(),
            5
        );
    }
}
#[test]
fn unknown_v1_shape_or_rpc_version_failure_cannot_advance_cursor() {
    // A retained unrelated entry proves refusals preserve, rather than reset,
    // caller state; the actual enrollment account has no prior cursor.
    let cursor = Cursor::from([([0xfe; 32], [0xfd; 64])]);
    for format in [
        Format::Future,
        Format::MissingConfig,
        Format::RpcUnsupported,
    ] {
        let report = captures(format, Format::V1, &cursor);
        assert!(report.refused());
        assert!(report.observations.is_empty());
        assert_eq!(report.cursor, cursor);
        let reason = if matches!(format, Format::RpcUnsupported) {
            Reason::RpcError
        } else {
            Reason::MalformedResponse
        };
        assert!(report.events.iter().any(|e| e.reason == reason));
    }
}
#[test]
fn different_v1_credit_keeps_disagreement_and_holds_enrollment_cursor() {
    let report = captures(Format::V1, Format::Disagree, &Cursor::new());
    assert!(report.refused());
    assert!(report
        .events
        .iter()
        .any(|e| e.reason == Reason::EndpointsDisagree));
    assert!(report.cursor.is_empty());
}
#[test]
fn fixture_query_enforces_numeric_version_one() {
    for wrong in [Value::Null, json!(0), json!(2), json!("1")] {
        let params = json!(["sig",{"encoding":"jsonParsed","commitment":"finalized",
            "maxSupportedTransactionVersion":wrong}]);
        assert!(fixture_key("getTransaction", &params).is_err());
    }
    assert!(fixture_key(
        "getTransaction",
        &json!(["sig",{"encoding":"jsonParsed",
        "commitment":"finalized","maxSupportedTransactionVersion":1}])
    )
    .is_ok());
}
fn credit(result: &Value) -> Result<minidregg_pay_watcher::decode::TxOutcome, Refusal> {
    use minidregg_pay_watcher::model::unbase58;
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/enrol-happy");
    let cfg = Config::load(&dir.join("config.json")).unwrap();
    let sig = unbase58(result["transaction"]["signatures"][0].as_str().unwrap()).unwrap();
    let owner = minidregg_pay_watcher::model::base58(&cfg.book[0].address);
    let keys: Vec<Key> = result["meta"]["postTokenBalances"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|row| row["owner"].as_str() == Some(owner.as_str()))
        .map(|row| {
            let index = row["accountIndex"].as_u64().unwrap() as usize;
            unbase58(
                result["transaction"]["message"]["accountKeys"][index]["pubkey"]
                    .as_str()
                    .unwrap(),
            )
            .unwrap()
        })
        .collect();
    minidregg_pay_watcher::decode::transaction_credit(
        result,
        &sig,
        result["slot"].as_u64().unwrap(),
        &keys,
        &cfg.asset,
        &cfg.book[0].address,
    )
}
fn capture_transaction() -> Value {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures/enrol-happy/endpoints/a/getTransaction");
    // Stable existing enrollment capture, selected by a memo and a positive
    // balance owned by the enrollment account, not filesystem iteration order.
    let cfg = Config::load(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/enrol-happy/config.json"),
    )
    .unwrap();
    let owner = minidregg_pay_watcher::model::base58(&cfg.book[0].address);
    let mut paths = std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect::<Vec<_>>();
    paths.sort();
    for path in paths {
        let value: Value = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        let result = &value["result"];
        if result["meta"]["postTokenBalances"]
            .as_array()
            .is_some_and(|rows| {
                rows.iter()
                    .any(|row| row["owner"].as_str() == Some(owner.as_str()))
            })
        {
            return result.clone();
        }
    }
    panic!("no enrollment fixture");
}
#[test]
fn version_shape_rejects_ambiguous_config_and_lookup_keys() {
    let baseline = capture_transaction();
    // Existing legacy captures may omit version. The absence cannot carry the
    // new version's marker. Explicit null and future versions never downgrade.
    let mut omitted = baseline.clone();
    omitted.as_object_mut().unwrap().remove("version");
    assert!(credit(&omitted).is_ok());
    for invalid in [Value::Null, json!("1"), json!(2), json!(-1)] {
        let mut result = baseline.clone();
        result["version"] = invalid;
        assert!(credit(&result).is_err());
    }
    for version in [json!("legacy"), json!(0)] {
        let mut result = baseline.clone();
        result["version"] = version;
        result["transaction"]["message"]["transactionConfig"] = Value::Null;
        assert!(credit(&result).is_err());
    }
    let mut v1 = baseline;
    v1["version"] = json!(1);
    v1["transaction"]["message"]["transactionConfig"] = config();
    assert!(credit(&v1).is_ok());
    for invalid in [
        Value::Null,
        json!({}),
        json!({"computeUnitLimit":1}),
        json!({"computeUnitLimit":"1","heapSize":null,"loadedAccountsDataSizeLimit":2,"priorityFee":null}),
        json!({"computeUnitLimit":1,"heapSize":null,"loadedAccountsDataSizeLimit":2,"priorityFee":-1}),
    ] {
        let mut result = v1.clone();
        result["transaction"]["message"]["transactionConfig"] = invalid;
        assert!(credit(&result).is_err());
    }
    let mut result = v1.clone();
    result["transaction"]["message"]["addressTableLookups"] = json!([]);
    assert!(credit(&result).is_err());
    let mut result = v1.clone();
    result["transaction"]["message"]["accountKeys"][0]["source"] = json!("lookupTable");
    assert!(credit(&result).is_err());
    let mut result = v1;
    result["meta"]["loadedAddresses"]["writable"] = json!(["11111111111111111111111111111111"]);
    assert!(credit(&result).is_err());
}
