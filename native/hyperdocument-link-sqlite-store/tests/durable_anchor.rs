use minidregg_hyperdocument_link_sqlite_store::{PublishStatus, SqliteByteStore, StoreError};
use std::{
    fs,
    path::PathBuf,
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

fn directory() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "mini-anchor-crash-{}-{}",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    fs::create_dir(&path).unwrap();
    path
}

#[test]
fn killed_publisher_recovers_before_and_after_commit_and_anchor() {
    for (phase, code, expected) in [
        ("after-begin", 86, 1),
        ("after-insert", 87, 1),
        ("after-commit", 88, 2),
        ("after-anchor-prepare", 90, 2),
        ("after-anchor-rename", 91, 2),
        ("after-anchor", 89, 2),
    ] {
        let dir = directory();
        let root = dir.join("store");
        let s = SqliteByteStore::open(&root).unwrap();
        s.durable_init(b"genesis").unwrap();
        s.durable_append(1, b"one", b"tag-one").unwrap();
        let snapshot = dir.join("before.sqlite3");
        fs::copy(s.database_path(), &snapshot).unwrap();
        drop(s);
        let record = dir.join("record");
        let tag = dir.join("tag");
        fs::write(&record, b"two").unwrap();
        fs::write(&tag, b"tag-two").unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_minidregg-link-sqlite-store"))
            .arg("durable-append-crash")
            .arg(&root)
            .arg("2")
            .arg(&record)
            .arg(&tag)
            .arg(phase)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(code));
        assert!(output.stdout.is_empty(), "crashed publisher must never ACK");
        let reopened = SqliteByteStore::open(&root).unwrap();
        assert_eq!(reopened.durable_read(1, true).unwrap().head, expected);
        if expected == 2 {
            assert_eq!(
                reopened.durable_append(2, b"two", b"tag-two").unwrap(),
                PublishStatus::AlreadyPresent
            );
        } else {
            assert_eq!(
                reopened.durable_append(2, b"two", b"tag-two").unwrap(),
                PublishStatus::Installed
            );
        }
        // A successful recovery/read has durably retained head 2. An older
        // whole database now refuses on a new process/open.
        let database = reopened.database_path().to_owned();
        drop(reopened);
        fs::copy(&snapshot, &database).unwrap();
        assert!(matches!(
            SqliteByteStore::open(&root).unwrap().durable_read(1, true),
            Err(StoreError::Anchor(_))
        ));
    }
}

#[test]
fn concurrent_publishers_serialize_anchor_with_commit() {
    let dir = directory();
    let root = dir.join("store");
    let s = SqliteByteStore::open(&root).unwrap();
    s.durable_init(b"genesis").unwrap();
    drop(s);
    let mut children = Vec::new();
    for n in 0..8 {
        let record = dir.join(format!("record-{n}"));
        let tag = dir.join(format!("tag-{n}"));
        fs::write(&record, [n]).unwrap();
        fs::write(&tag, [n]).unwrap();
        children.push(
            Command::new(env!("CARGO_BIN_EXE_minidregg-link-sqlite-store"))
                .arg("durable-append")
                .arg(&root)
                .arg("1")
                .arg(&record)
                .arg(&tag)
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::piped())
                .spawn()
                .unwrap(),
        );
    }
    let results: Vec<_> = children
        .into_iter()
        .map(|c| c.wait_with_output().unwrap())
        .collect();
    assert_eq!(results.iter().filter(|r| r.status.success()).count(), 1);
    assert_eq!(
        SqliteByteStore::open(&root)
            .unwrap()
            .durable_read(1, true)
            .unwrap()
            .head,
        1
    );
}
