use minidregg_hyperdocument_link_sqlite_store::{PublishStatus, SqliteByteStore, StoreError};
use std::{
    fs,
    path::PathBuf,
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

mod support;

/// The crash fixtures' child (`support`): a no-op unless re-executed as one.
#[test]
fn fixture_child() {
    support::run_if_child()
}

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
    // The anchor's directory must be the Store account's alone (anchor custody).
    fs::set_permissions(&path, std::os::unix::fs::PermissionsExt::from_mode(0o700)).unwrap();
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
        s.durable_append(1, b"one", b"tag-one", &[]).unwrap();
        let snapshot = dir.join("before.sqlite3");
        s.wal_checkpoint().unwrap();
        fs::copy(s.database_path(), &snapshot).unwrap();
        drop(s);
        let record = dir.join("record");
        let tag = dir.join("tag");
        fs::write(&record, b"two").unwrap();
        fs::write(&tag, b"tag-two").unwrap();
        let nodes = dir.join("nodes");
        fs::write(&nodes, 0u64.to_be_bytes()).unwrap();
        let output = support::fixture(&[std::ffi::OsStr::new("durable-append-crash"), root.as_os_str(), "2".as_ref(),
            record.as_os_str(), tag.as_os_str(), nodes.as_os_str(), phase.as_ref()])
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(code));
        assert!(support::fixture_stdout(&output.stdout).is_empty(), "crashed publisher must never ACK");
        let reopened = SqliteByteStore::open(&root).unwrap();
        assert_eq!(reopened.durable_read(1, true).unwrap().head, expected);
        if expected == 2 {
            assert_eq!(
                reopened.durable_append(2, b"two", b"tag-two", &[]).unwrap(),
                PublishStatus::AlreadyPresent
            );
        } else {
            assert_eq!(
                reopened.durable_append(2, b"two", b"tag-two", &[]).unwrap(),
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
        let nodes = dir.join(format!("nodes-{n}"));
        fs::write(&nodes, 0u64.to_be_bytes()).unwrap();
        children.push(
            Command::new(env!("CARGO_BIN_EXE_minidregg-link-sqlite-store"))
                .arg("durable-append")
                .arg(&root)
                .arg("1")
                .arg(&record)
                .arg(&tag)
                .arg(&nodes)
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
    let total = result.stdout.len() as u64;
    let mut stream = std::io::Cursor::new(result.stdout);
    let mut replies = Vec::new();
    while stream.position() < total {
        let (code, _stdout, stderr) = serve_reply(&mut stream);
        replies.push((code, String::from_utf8_lossy(&stderr).into_owned()));
    }
    assert_eq!(replies.len(), 3);
    assert_eq!(replies[0].0, 0);
    assert_eq!(replies[1].0, 0);
    assert_eq!(replies[2].0, 1);
    assert!(replies[2].1.contains("genesis or retained head conflicts"));
}

fn serve_frame(command: &[String]) -> Vec<u8> {
    let mut out = (command.len() as u32).to_be_bytes().to_vec();
    for arg in command {
        out.extend_from_slice(&(arg.len() as u32).to_be_bytes());
        out.extend_from_slice(arg.as_bytes());
    }
    out
}

fn serve_reply(stream: &mut impl std::io::Read) -> (u32, Vec<u8>, Vec<u8>) {
    let mut tag = [0u8; 8];
    stream.read_exact(&mut tag).unwrap();
    assert_eq!(&tag, b"MDCOPRC1", "every serve reply opens with the reply tag");
    let mut word = [0u8; 4];
    stream.read_exact(&mut word).unwrap();
    let mut long = [0u8; 8];
    stream.read_exact(&mut long).unwrap();
    let mut stdout = vec![0u8; u64::from_be_bytes(long) as usize];
    stream.read_exact(&mut stdout).unwrap();
    stream.read_exact(&mut long).unwrap();
    let mut stderr = vec![0u8; u64::from_be_bytes(long) as usize];
    stream.read_exact(&mut stderr).unwrap();
    (u32::from_be_bytes(word), stdout, stderr)
}

/// The server answers ordinary commands in-process with the one-shot
/// command's exact reply (run against a twin store), and the deployed binary
/// has no crash or hold verb: one is refused as usage and the server keeps
/// serving.
#[test]
fn serve_answers_in_process_and_the_production_binary_has_no_crash_verbs() {
    use std::io::Write;
    let dir = directory();
    let (served_root, twin_root) = (dir.join("served"), dir.join("twin"));
    let seed = dir.join("seed");
    fs::write(&seed, b"seed").unwrap();
    let record = dir.join("record");
    fs::write(&record, b"record").unwrap();
    let tag = dir.join("tag");
    fs::write(&tag, b"tag").unwrap();
    let nodes = dir.join("nodes");
    fs::write(&nodes, 0u64.to_be_bytes()).unwrap();
    let id = "domain:1;semantics:2;seed:3".to_owned();
    let commands = |root: &PathBuf, out: &str| -> Vec<Vec<String>> {
        let r = root.display().to_string();
        let o = dir.join(out).display().to_string();
        vec![
            vec!["--anchor-identity".into(), id.clone(), "durable-init".into(), r.clone(), seed.display().to_string()],
            vec!["--anchor-identity".into(), id.clone(), "durable-read".into(), r.clone(), "1".into(), "1".into(), o.clone()],
            vec!["--anchor-identity".into(), id.clone(), "durable-append".into(), r.clone(), "1".into(),
                 record.display().to_string(), tag.display().to_string(), nodes.display().to_string()],
            vec!["--anchor-identity".into(), id.clone(), "durable-read".into(), r.clone(), "1".into(), "1".into(), o.clone()],
            vec!["--anchor-identity".into(), id.clone(), "durable-read".into(), r.clone(), "1".into(), "1".into(), o],
            vec!["--anchor-identity".into(), id.clone(), "durable-append".into(), r.clone(), "1".into(),
                 record.display().to_string(), tag.display().to_string(), nodes.display().to_string()],
            vec!["no-such-command".into()],
        ]
    };
    let binary = env!("CARGO_BIN_EXE_minidregg-link-sqlite-store");
    let mut server = Command::new(binary).arg("serve")
        .stdin(std::process::Stdio::piped()).stdout(std::process::Stdio::piped()).spawn().unwrap();
    let mut input = server.stdin.take().unwrap();
    let mut output = server.stdout.take().unwrap();
    for (served, twin) in commands(&served_root, "served-read").iter().zip(commands(&twin_root, "twin-read")) {
        input.write_all(&serve_frame(served)).unwrap();
        input.flush().unwrap();
        let (code, stdout, stderr) = serve_reply(&mut output);
        let one_shot = Command::new(binary).args(&twin).output().unwrap();
        assert_eq!(code, one_shot.status.code().unwrap() as u32, "{served:?}");
        let twin_text = |b: &[u8]| String::from_utf8_lossy(b).replace("twin", "served");
        assert_eq!(String::from_utf8_lossy(&stdout), twin_text(&one_shot.stdout), "{served:?}");
        assert_eq!(String::from_utf8_lossy(&stderr), twin_text(&one_shot.stderr), "{served:?}");
        if served.contains(&"durable-read".to_string()) {
            assert_eq!(fs::read(dir.join("served-read")).unwrap(), fs::read(dir.join("twin-read")).unwrap());
        }
    }
    let crash = vec!["--anchor-identity".into(), id.clone(), "durable-append-crash".into(),
        served_root.display().to_string(), "2".into(), record.display().to_string(), tag.display().to_string(),
        nodes.display().to_string(), "after-commit".into()];
    input.write_all(&serve_frame(&crash)).unwrap();
    input.flush().unwrap();
    let (code, stdout, _) = serve_reply(&mut output);
    assert_eq!((code, stdout.len()), (2, 0), "a crash verb is not a command of the production binary");
    for verb in ["cas-crash", "publish-crash", "publish-hold", "journal-append-crash"] {
        let one_shot = Command::new(binary).arg(verb).arg(&served_root).output().unwrap();
        assert_eq!(one_shot.status.code(), Some(2), "{verb}");
    }
    let read = vec!["--anchor-identity".into(), id, "durable-read".into(), served_root.display().to_string(),
        "1".into(), "1".into(), dir.join("after-crash").display().to_string()];
    input.write_all(&serve_frame(&read)).unwrap();
    input.flush().unwrap();
    assert_eq!(serve_reply(&mut output).0, 0, "server still serves after a crash fixture");
    drop(input);
    assert!(server.wait().unwrap().success());
}

fn serve_frame_memory(blobs: &[(&str, &[u8])], command: &[String]) -> Vec<u8> {
    let mut out = u32::MAX.to_be_bytes().to_vec();
    out.extend_from_slice(&(blobs.len() as u32).to_be_bytes());
    for (name, bytes) in blobs {
        out.extend_from_slice(&(name.len() as u32).to_be_bytes());
        out.extend_from_slice(name.as_bytes());
        out.extend_from_slice(&(bytes.len() as u64).to_be_bytes());
        out.extend_from_slice(bytes);
    }
    out.extend_from_slice(&serve_frame(command));
    out
}

type MemoryReply = (u32, Vec<u8>, Vec<u8>, Vec<(Vec<u8>, Vec<u8>)>);

fn serve_reply_memory(stream: &mut impl std::io::Read) -> MemoryReply {
    let mut tag = [0u8; 8];
    stream.read_exact(&mut tag).unwrap();
    assert_eq!(&tag, b"MDCOPRC2", "a memory request's reply opens with the memory reply tag");
    let mut word = [0u8; 4];
    let mut long = [0u8; 8];
    let mut field = |stream: &mut dyn std::io::Read| {
        stream.read_exact(&mut long).unwrap();
        let mut bytes = vec![0u8; u64::from_be_bytes(long) as usize];
        stream.read_exact(&mut bytes).unwrap();
        bytes
    };
    stream.read_exact(&mut word).unwrap();
    let code = u32::from_be_bytes(word);
    let (stdout, stderr) = (field(stream), field(stream));
    stream.read_exact(&mut word).unwrap();
    let mut blobs = Vec::new();
    for _ in 0..u32::from_be_bytes(word) {
        stream.read_exact(&mut word).unwrap();
        let mut name = vec![0u8; u32::from_be_bytes(word) as usize];
        stream.read_exact(&mut name).unwrap();
        blobs.push((name, field(stream)));
    }
    (code, stdout, stderr, blobs)
}

/// A memory frame (`mem:NAME` paths) answers exactly as the file frame does: the same code,
/// stdout and stderr, with the bytes the file call writes returned as a blob of that name, and
/// no file written.
#[test]
fn a_memory_request_answers_as_the_file_request_does() {
    use std::io::Write;
    let dir = directory();
    let (served, twin) = (dir.join("served"), dir.join("twin"));
    let id = "domain:1;semantics:2;seed:3".to_owned();
    for (name, bytes) in [("seed", &b"seed"[..]), ("record", b"record"), ("tag", b"tag")] {
        fs::write(dir.join(name), bytes).unwrap();
    }
    fs::write(dir.join("nodes"), 0u64.to_be_bytes()).unwrap();
    let nodes = 0u64.to_be_bytes();
    let binary = env!("CARGO_BIN_EXE_minidregg-link-sqlite-store");
    let mut server = Command::new(binary).arg("serve")
        .stdin(std::process::Stdio::piped()).stdout(std::process::Stdio::piped()).spawn().unwrap();
    let mut input = server.stdin.take().unwrap();
    let mut output = server.stdout.take().unwrap();
    let call = |args: &[&str]| -> Vec<String> {
        ["--anchor-identity", id.as_str()].iter().chain(args).map(|a| a.to_string()).collect()
    };
    let r = served.display().to_string();
    let t = twin.display().to_string();
    let path = |name: &str| dir.join(name).display().to_string();
    let steps: Vec<(Vec<(&str, &[u8])>, Vec<String>, Vec<String>, Option<&str>)> = vec![
        (vec![("seed", b"seed")], call(&["durable-init", &r, "mem:seed"]),
            call(&["durable-init", &t, &path("seed")]), None),
        (vec![("record", b"record"), ("tag", b"tag"), ("nodes", &nodes)],
            call(&["durable-append", &r, "1", "mem:record", "mem:tag", "mem:nodes"]),
            call(&["durable-append", &t, "1", &path("record"), &path("tag"), &path("nodes")]), None),
        (vec![], call(&["durable-read", &r, "1", "1", "mem:read"]),
            call(&["durable-read", &t, "1", "1", &path("twin-read")]), Some("twin-read")),
        (vec![], call(&["durable-seed", &r, "mem:seed"]),
            call(&["durable-seed", &t, &path("twin-seed")]), Some("twin-seed")),
        (vec![], call(&["durable-read", &r, "1", "1", "mem:"]),
            call(&["durable-read", &t, "1", "1", &path("twin-read2")]), Some("twin-read2")),
    ];
    for (blobs, served_call, twin_call, written) in steps {
        input.write_all(&serve_frame_memory(&blobs, &served_call)).unwrap();
        input.flush().unwrap();
        let (code, stdout, stderr, out) = serve_reply_memory(&mut output);
        let one_shot = Command::new(binary).args(&twin_call).output().unwrap();
        assert_eq!(code, one_shot.status.code().unwrap() as u32, "{served_call:?}");
        let text = |b: &[u8]| String::from_utf8_lossy(b).replace("twin", "served");
        assert_eq!(text(&stdout), text(&one_shot.stdout), "{served_call:?}");
        assert_eq!(text(&stderr), text(&one_shot.stderr), "{served_call:?}");
        match written {
            Some(file) => {
                assert_eq!(out.len(), 1, "{served_call:?}");
                assert_eq!(out[0].1, fs::read(dir.join(file)).unwrap(), "{served_call:?}");
            }
            None => assert!(out.is_empty(), "{served_call:?}"),
        }
    }
    // A request without the memory mark still gets the file reply, and a `mem:` path outside a
    // memory request is refused, not written.
    input.write_all(&serve_frame(&call(&["durable-read", &r, "1", "1", "mem:read"]))).unwrap();
    input.flush().unwrap();
    assert_ne!(serve_reply(&mut output).0, 0);
    assert!(!dir.join("mem:read").exists());
    drop(input);
    assert!(server.wait().unwrap().success());
}

/// A bound violation is not contention: the CLI exits 6 (Lean maps 4 to
/// "reload and recompute", which would retry the same bytes forever).
#[test]
fn an_append_over_a_bound_exits_six_not_conflict() {
    let dir = directory();
    let root = dir.join("store");
    let s = SqliteByteStore::open(&root).unwrap();
    s.durable_init(b"genesis").unwrap();
    assert!(matches!(s.durable_append(1, b"one", &[0u8; 4097], &[]), Err(StoreError::Bound(_))));
    assert!(matches!(s.durable_append(0, b"one", b"t", &[]), Err(StoreError::Bound(_))));
    assert!(matches!(s.journal_append(0, b"one", b"t"), Err(StoreError::Bound(_))));
    drop(s);
    let (record, tag, nodes) = (dir.join("record"), dir.join("tag"), dir.join("nodes"));
    fs::write(&record, b"one").unwrap();
    fs::write(&tag, vec![0u8; 4097]).unwrap();
    fs::write(&nodes, 0u64.to_be_bytes()).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_minidregg-link-sqlite-store"))
        .arg("durable-append").arg(&root).arg("1").arg(&record).arg(&tag).arg(&nodes)
        .output().unwrap();
    assert_eq!(out.status.code(), Some(6));
    assert!(String::from_utf8_lossy(&out.stderr).contains("not contention"), "{}", String::from_utf8_lossy(&out.stderr));
    fs::remove_dir_all(&dir).unwrap();
}

/// A read of a current Store needs no write: with the Store directory and the
/// anchor's directory made unwritable, it still answers. A disk that refuses a
/// needed write is its own error (exit 7), never "absent".
#[test]
fn a_read_needs_no_writable_disk_and_a_refused_write_is_typed() {
    use std::os::unix::fs::PermissionsExt;
    let dir = directory();
    let root = dir.join("store");
    let s = SqliteByteStore::open(&root).unwrap();
    s.durable_init(b"genesis").unwrap();
    s.durable_append(1, b"one", b"tag-one", &[]).unwrap();
    assert_eq!(s.durable_read(1, true).unwrap().head, 1);
    drop(s);
    for d in [&root, &dir] {
        fs::set_permissions(d, fs::Permissions::from_mode(0o500)).unwrap();
    }
    if unsafe { libc::geteuid() } != 0 {
        let reopened = SqliteByteStore::open(&root).unwrap();
        assert_eq!(reopened.durable_read(1, true).unwrap().head, 1);
        assert_eq!(reopened.journal_read(1).unwrap().entries.len(), 0);
    }
    for d in [&dir, &root] {
        fs::set_permissions(d, fs::Permissions::from_mode(0o700)).unwrap();
    }
    for errno in [libc::ENOSPC, libc::EROFS, libc::EDQUOT] {
        assert!(StoreError::from(std::io::Error::from_raw_os_error(errno)).is_unwritable());
    }
    assert!(!StoreError::from(std::io::Error::from_raw_os_error(libc::EACCES)).is_unwritable());
    fs::remove_dir_all(&dir).unwrap();
}

/// WAL with synchronous=FULL: a writer killed right after COMMIT (before the
/// anchor, before any checkpoint) leaves the record only in `-wal`, and the
/// next open recovers it exactly. The database file says WAL (header byte 18).
#[test]
fn a_crash_after_commit_keeps_the_record_in_the_wal() {
    let dir = directory();
    let root = dir.join("store");
    let s = SqliteByteStore::open(&root).unwrap();
    s.durable_init(b"genesis").unwrap();
    let database = s.database_path().to_owned();
    drop(s);
    let header = fs::read(&database).unwrap();
    assert_eq!((header[18], header[19]), (2, 2), "the Store file is in WAL mode");
    let (record, tag, nodes) = (dir.join("record"), dir.join("tag"), dir.join("nodes"));
    fs::write(&record, b"the committed record").unwrap();
    fs::write(&tag, b"its tag").unwrap();
    fs::write(&nodes, 0u64.to_be_bytes()).unwrap();
    let output = support::fixture(&[std::ffi::OsStr::new("durable-append-crash"), root.as_os_str(), "1".as_ref(),
        record.as_os_str(), tag.as_os_str(), nodes.as_os_str(), "after-commit".as_ref()])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(88));
    let wal = fs::metadata(format!("{}-wal", database.display())).unwrap().len();
    assert!(wal > 0, "the committed frames are in the WAL, not yet checkpointed");
    let reopened = SqliteByteStore::open(&root).unwrap();
    let read = reopened.durable_read(1, false).unwrap();
    assert_eq!(read.head, 1);
    assert_eq!((read.entries[0].record.as_slice(), read.entries[0].tag.as_slice()), (&b"the committed record"[..], &b"its tag"[..]));
    assert_eq!(reopened.durable_append(1, b"the committed record", b"its tag", &[]).unwrap(), PublishStatus::AlreadyPresent);
    fs::remove_dir_all(&dir).unwrap();
}
