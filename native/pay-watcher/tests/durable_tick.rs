//! Process-level crash snapshots for the durable watcher protocol. Fixture RPC
//! answers are used only for the first scan; pending recovery must work offline.
use serde_json::Value;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!("pay-durable-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
        fs::create_dir(&root).unwrap();
        let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/enrol-dust");
        copy_tree(&source, &root.join("fixture"));
        fs::create_dir(root.join("out")).unwrap();
        Self(root)
    }
    fn out(&self) -> PathBuf { self.0.join("out") }
    fn config(&self) -> PathBuf { self.0.join("fixture/config.json") }
    fn cursor(&self) -> PathBuf { self.0.join("fixture/enrol-cursor.json") }
    fn run(&self, rpc: bool, ack: Option<&str>) -> Output {
        let mut c = Command::new(env!("CARGO_BIN_EXE_pay-watcher"));
        c.env_remove("PAY_RPC_ENDPOINTS").args(["--config"]).arg(self.config()).args(["--out"]).arg(self.out());
        if let Some(id) = ack { c.args(["--ack-tick", id]); } else { c.arg("--durable-ticks"); }
        if rpc {
            for endpoint in ["a", "b"] { c.arg("--rpc-fixture").arg(self.0.join("fixture/endpoints").join(endpoint)); }
        }
        c.output().unwrap()
    }
    fn pending(&self) -> Value { read(&self.out().join("pending.json")) }
}
impl Drop for Fixture { fn drop(&mut self) { let _ = fs::remove_dir_all(&self.0); } }
fn copy_tree(source: &Path, dest: &Path) {
    fs::create_dir(dest).unwrap();
    for e in fs::read_dir(source).unwrap() {
        let e = e.unwrap();
        if e.file_type().unwrap().is_dir() { copy_tree(&e.path(), &dest.join(e.file_name())); }
        else { fs::copy(e.path(), dest.join(e.file_name())).unwrap(); }
    }
}
fn read(path: &Path) -> Value { serde_json::from_slice(&fs::read(path).unwrap()).unwrap() }
fn success(result: Output) {
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
}

#[test]
fn crash_after_pending_before_outputs_recovers_offline_and_archives_once() {
    let f = Fixture::new();
    // A failed output rename models stopping after the durable pending write.
    fs::create_dir(f.out().join("observations.json")).unwrap();
    assert_eq!(f.run(true, None).status.code(), Some(2));
    let pending = f.pending();
    assert!(pending["events"].as_array().unwrap().iter().any(|e| e["reason"] == "belowJournalFloor"));
    assert!(!f.cursor().exists());
    fs::remove_dir(f.out().join("observations.json")).unwrap();
    success(f.run(false, None));
    assert_eq!(f.pending(), pending);
    assert_eq!(read(&f.out().join("events.json")), pending["events"]);
    assert_eq!(read(&f.cursor()), pending["cursor"]["after"]);
    let id = pending["id"].as_str().unwrap();
    assert_eq!(f.run(false, Some("00000000000000000009")).status.code(), Some(2));
    assert_eq!(f.pending(), pending);
    success(f.run(false, Some(id)));
    success(f.run(false, Some(id)));
    assert!(!f.out().join("pending.json").exists());
    assert_eq!(read(&f.out().join("ticks").join(format!("{id}.json"))), pending);
    assert_eq!(fs::read_dir(f.out().join("ticks")).unwrap().count(), 1);
}

#[test]
fn crash_after_cursor_before_archival_reuses_exact_events_and_observations() {
    let f = Fixture::new();
    success(f.run(true, None));
    let pending_bytes = fs::read(f.out().join("pending.json")).unwrap();
    let pending = f.pending();
    // Output views are disposable; the pending record alone repairs them.
    fs::remove_file(f.out().join("events.json")).unwrap();
    fs::remove_file(f.out().join("observations.json")).unwrap();
    for _ in 0..3 {
        success(f.run(false, None));
        assert_eq!(fs::read(f.out().join("pending.json")).unwrap(), pending_bytes);
        assert_eq!(read(&f.out().join("observations.json")), pending["observations"]);
        assert_eq!(read(&f.out().join("events.json")), pending["events"]);
    }
    success(f.run(false, Some(pending["id"].as_str().unwrap())));
    // Original below-floor evidence survives the next scan as an immutable tick.
    let next = f.run(true, None);
    assert!(matches!(next.status.code(), Some(0 | 3)), "{}", String::from_utf8_lossy(&next.stderr));
    assert_ne!(f.pending()["id"], pending["id"]);
    assert_eq!(read(&f.out().join("ticks/00000000000000000001.json"))["events"], pending["events"]);
}

#[test]
fn divergent_cursor_or_changed_observer_never_rewinds_pending_tick() {
    let f = Fixture::new();
    success(f.run(true, None));
    let pending = f.pending();
    let original_cursor = fs::read(f.cursor()).unwrap();
    fs::write(f.cursor(), br#"{"cursors":{"ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}}"#).unwrap();
    let divergent = fs::read(f.cursor()).unwrap();
    assert_eq!(f.run(false, None).status.code(), Some(2));
    assert_eq!(fs::read(f.cursor()).unwrap(), divergent);
    assert_eq!(f.pending(), pending);
    fs::write(f.cursor(), original_cursor).unwrap();
    let mut config = read(&f.config());
    config["receiptsDir"] = Value::String("another-observer".into());
    fs::write(f.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    assert_eq!(f.run(false, None).status.code(), Some(2));
    assert_eq!(f.pending(), pending);
}
