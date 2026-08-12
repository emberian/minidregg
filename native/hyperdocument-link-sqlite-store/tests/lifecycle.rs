use minidregg_hyperdocument_link_sqlite_store::{
    PublishStatus, SqliteLinkStore, StoreError, MAX_RECORD_BYTES,
};
use std::fs::{self, OpenOptions};
use std::io::{Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const LEAN_FIXTURE: &[u8] =
    include_bytes!("../../hyperdocument-link-store/fixtures/hyperdocument-link-recovery-v1.bin");

struct TempDir(PathBuf);

impl TempDir {
    fn new(label: &str) -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock before epoch")
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "minidregg-link-sqlite-store-{label}-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&path).expect("create test directory");
        Self(path)
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn binary() -> &'static str {
    env!("CARGO_BIN_EXE_minidregg-link-sqlite-store")
}

fn input_file(temp: &TempDir, name: &str, bytes: &[u8]) -> PathBuf {
    let path = temp.path().join(name);
    fs::write(&path, bytes).unwrap();
    path
}

fn crash_publish(root: &Path, input: &Path, phase: &str) -> ExitStatus {
    Command::new(binary())
        .args(["publish-crash"])
        .arg(root)
        .arg(input)
        .arg(phase)
        .status()
        .expect("run crash publisher")
}

fn wait_for(path: &Path, child: &mut Child) {
    let deadline = Instant::now() + Duration::from_secs(10);
    while !path.exists() {
        assert!(
            child.try_wait().unwrap().is_none(),
            "hold publisher exited before ready"
        );
        assert!(
            Instant::now() < deadline,
            "timed out waiting for ready marker"
        );
        thread::sleep(Duration::from_millis(10));
    }
}

#[test]
fn lean_fixture_is_exact_and_bounded() {
    assert_eq!(
        LEAN_FIXTURE,
        &[162, 74, 30, 216, 1, 72, 89, 80, 69, 82, 76, 78, 75, 110]
    );
    assert!(LEAN_FIXTURE.len() <= MAX_RECORD_BYTES);
}

#[test]
fn crash_after_begin_or_insert_recovers_absent() {
    for (label, phase) in [("begin", "after-begin"), ("insert", "after-insert")] {
        let temp = TempDir::new(label);
        let input = input_file(&temp, "fixture.bin", LEAN_FIXTURE);
        assert!(!crash_publish(temp.path(), &input, phase).success());
        let reopened = SqliteLinkStore::open(temp.path()).unwrap();
        assert!(matches!(reopened.read(), Err(StoreError::Missing)));
    }
}

#[test]
fn crash_after_commit_reopens_exact_and_retry_is_idempotent() {
    let temp = TempDir::new("commit");
    let input = input_file(&temp, "fixture.bin", LEAN_FIXTURE);
    assert!(!crash_publish(temp.path(), &input, "after-commit").success());
    let reopened = SqliteLinkStore::open(temp.path()).unwrap();
    assert_eq!(reopened.read().unwrap(), LEAN_FIXTURE);
    assert_eq!(
        reopened.publish(LEAN_FIXTURE).unwrap(),
        PublishStatus::AlreadyPresent
    );
    assert_eq!(reopened.read().unwrap(), LEAN_FIXTURE);
}

#[test]
fn concurrent_conflicting_transaction_waits_then_fails_without_overwrite() {
    let temp = TempDir::new("conflicting-transaction");
    let first = input_file(&temp, "first.bin", LEAN_FIXTURE);
    let mut different = LEAN_FIXTURE.to_vec();
    *different.last_mut().unwrap() = 0;
    let second = input_file(&temp, "second.bin", &different);
    let ready = temp.path().join("ready");
    let release = temp.path().join("release");

    let mut holder = Command::new(binary())
        .arg("publish-hold")
        .arg(temp.path())
        .arg(&first)
        .arg(&ready)
        .arg(&release)
        .spawn()
        .expect("spawn holding transaction");
    wait_for(&ready, &mut holder);

    let mut contender = Command::new(binary())
        .arg("publish")
        .arg(temp.path())
        .arg(&second)
        .spawn()
        .expect("spawn conflicting transaction");
    thread::sleep(Duration::from_millis(150));
    assert!(contender.try_wait().unwrap().is_none());
    fs::write(&release, b"commit\n").unwrap();
    assert!(holder.wait().unwrap().success());
    assert!(!contender.wait().unwrap().success());

    let reopened = SqliteLinkStore::open(temp.path()).unwrap();
    assert_eq!(reopened.read().unwrap(), LEAN_FIXTURE);
}

#[test]
fn corrupt_header_and_torn_database_fail_opaquely() {
    for label in ["corrupt", "torn"] {
        let temp = TempDir::new(label);
        let store = SqliteLinkStore::open(temp.path()).unwrap();
        assert_eq!(
            store.publish(LEAN_FIXTURE).unwrap(),
            PublishStatus::Installed
        );
        let database_path = store.database_path().to_path_buf();
        drop(store);

        if label == "corrupt" {
            let mut file = OpenOptions::new().write(true).open(&database_path).unwrap();
            file.seek(SeekFrom::Start(0)).unwrap();
            file.write_all(&[0; 32]).unwrap();
            file.sync_all().unwrap();
        } else {
            let length = fs::metadata(&database_path).unwrap().len();
            OpenOptions::new()
                .write(true)
                .open(&database_path)
                .unwrap()
                .set_len(length / 2)
                .unwrap();
        }

        let result = SqliteLinkStore::open(temp.path()).and_then(|store| store.read());
        assert!(
            result.is_err(),
            "{label} database unexpectedly produced bytes"
        );
    }
}

#[test]
fn oversize_fails_before_transaction() {
    let temp = TempDir::new("oversize");
    let store = SqliteLinkStore::open(temp.path()).unwrap();
    let oversized = vec![0; MAX_RECORD_BYTES + 1];
    assert!(matches!(
        store.publish(&oversized),
        Err(StoreError::TooLarge { .. })
    ));
    assert!(matches!(store.read(), Err(StoreError::Missing)));
}
