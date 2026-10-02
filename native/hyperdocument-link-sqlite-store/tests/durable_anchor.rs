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

#[test]
fn coprocess_carries_identity_and_refuses_a_different_deployment() {
    use std::io::Write;
    let dir = directory();
    let root = dir.join("store");
    let seed = dir.join("seed");
    let out = dir.join("read");
    fs::write(&seed, b"seed").unwrap();
    let commands = vec![
        vec![
            "--anchor-identity".to_owned(),
            "domain:1;semantics:2;seed:3".to_owned(),
            "durable-init".to_owned(),
            root.display().to_string(),
            seed.display().to_string(),
        ],
        vec![
            "--anchor-identity".to_owned(),
            "domain:1;semantics:2;seed:3".to_owned(),
            "durable-read".to_owned(),
            root.display().to_string(),
            "1".to_owned(),
            "1".to_owned(),
            out.display().to_string(),
        ],
        vec![
            "--anchor-identity".to_owned(),
            "domain:4;semantics:2;seed:3".to_owned(),
            "durable-read".to_owned(),
            root.display().to_string(),
            "1".to_owned(),
            "1".to_owned(),
            out.display().to_string(),
        ],
    ];
    let mut child = Command::new(env!("CARGO_BIN_EXE_minidregg-link-sqlite-store"))
        .arg("serve")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let mut input = child.stdin.take().unwrap();
    for command in commands {
        input
            .write_all(&(command.len() as u32).to_be_bytes())
            .unwrap();
        for arg in command {
            input.write_all(&(arg.len() as u32).to_be_bytes()).unwrap();
            input.write_all(arg.as_bytes()).unwrap();
        }
    }
    drop(input);
    let result = child.wait_with_output().unwrap();
    assert!(result.status.success());
    let mut bytes = result.stdout.as_slice();
    let mut replies = Vec::new();
    while !bytes.is_empty() {
        let code = u32::from_be_bytes(bytes[..4].try_into().unwrap());
        bytes = &bytes[4..];
        let n = u64::from_be_bytes(bytes[..8].try_into().unwrap()) as usize;
        bytes = &bytes[8 + n..];
        let n = u64::from_be_bytes(bytes[..8].try_into().unwrap()) as usize;
        replies.push((code, String::from_utf8_lossy(&bytes[8..8 + n]).into_owned()));
        bytes = &bytes[8 + n..];
    }
    assert_eq!(replies.len(), 3);
    assert_eq!(replies[0].0, 0);
    assert_eq!(replies[1].0, 0);
    assert_eq!(replies[2].0, 1);
    assert!(replies[2].1.contains("genesis or retained head conflicts"));
}
