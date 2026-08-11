use minidregg_hyperdocument_link_store::{
    LocalLinkStore, PublishStatus, StageStatus, StoreError, MAX_RECORD_BYTES,
};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

const LEAN_FIXTURE: &[u8] = include_bytes!("../fixtures/hyperdocument-link-recovery-v1.bin");

struct TempDir(PathBuf);

impl TempDir {
    fn new(label: &str) -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock before epoch")
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "minidregg-link-store-{label}-{}-{nonce}",
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

#[test]
fn lean_fixture_is_exact_and_bounded() {
    assert_eq!(
        LEAN_FIXTURE,
        &[162, 74, 30, 216, 1, 72, 89, 80, 69, 82, 76, 78, 75, 110]
    );
    assert!(LEAN_FIXTURE.len() <= MAX_RECORD_BYTES);
}

#[test]
fn staged_crash_is_not_visible_and_can_be_discarded_after_restart() {
    let temp = TempDir::new("stage-crash");
    let first_process = LocalLinkStore::open(temp.path()).unwrap();
    assert_eq!(
        first_process.stage(LEAN_FIXTURE).unwrap(),
        StageStatus::Staged
    );
    drop(first_process);

    let restarted = LocalLinkStore::open(temp.path()).unwrap();
    assert!(matches!(restarted.read(), Err(StoreError::Missing)));
    restarted.discard_staged().unwrap();
    assert!(matches!(restarted.read(), Err(StoreError::Missing)));
}

#[test]
fn lost_response_restart_and_exact_retry_preserve_one_record() {
    let temp = TempDir::new("lost-response");
    let first_process = LocalLinkStore::open(temp.path()).unwrap();
    assert_eq!(
        first_process.publish(LEAN_FIXTURE).unwrap(),
        PublishStatus::Installed
    );
    // Model a lost response by dropping all process-local state after publish.
    drop(first_process);

    let restarted = LocalLinkStore::open(temp.path()).unwrap();
    assert_eq!(restarted.read().unwrap(), LEAN_FIXTURE);
    assert_eq!(
        restarted.publish(LEAN_FIXTURE).unwrap(),
        PublishStatus::AlreadyPresent
    );
    assert_eq!(restarted.read().unwrap(), LEAN_FIXTURE);
}

#[test]
fn different_retry_conflicts_without_overwrite() {
    let temp = TempDir::new("conflict");
    let store = LocalLinkStore::open(temp.path()).unwrap();
    store.publish(LEAN_FIXTURE).unwrap();
    let mut different = LEAN_FIXTURE.to_vec();
    *different.last_mut().unwrap() = 0;
    assert!(matches!(
        store.publish(&different),
        Err(StoreError::Conflict)
    ));
    assert_eq!(store.read().unwrap(), LEAN_FIXTURE);
}

#[test]
fn oversized_input_fails_before_staging() {
    let temp = TempDir::new("oversized");
    let store = LocalLinkStore::open(temp.path()).unwrap();
    let oversized = vec![0; MAX_RECORD_BYTES + 1];
    assert!(matches!(
        store.publish(&oversized),
        Err(StoreError::TooLarge { .. })
    ));
    assert!(matches!(store.read(), Err(StoreError::Missing)));
}
