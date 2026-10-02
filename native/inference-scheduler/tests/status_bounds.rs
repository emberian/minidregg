#![cfg(target_os = "linux")]
//! Real framed operator replies stay bounded even when labels need JSON escaping
//! and a valid <=64KiB inventory has thousands of capacity groups.
use minidregg_inference_scheduler::{
    core::*,
    digest, operate,
    service::{now_ms, Service, Status},
    write_frame, Command, Reply, MAX_FRAME,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command as ProcessCommand};
use std::time::{Duration, Instant};

#[test]
fn status_bounds_child() {
    let Some(root) = std::env::var_os("MINI_STATUS_BOUNDS_CHILD") else {
        return;
    };
    let root = PathBuf::from(root);
    let config = serde_json::from_slice(&fs::read(root.join("config.json")).unwrap()).unwrap();
    Service::open(config, &root.join("state"))
        .unwrap()
        .serve(&root.join("control.sock"))
        .unwrap();
}

struct Daemon {
    root: PathBuf,
    child: Child,
}
impl Drop for Daemon {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
        // This fixture exclusively created this unique directory.
        let _ = fs::remove_dir_all(&self.root);
    }
}
fn bounded(status: &Status) {
    let mut bytes = Vec::new();
    write_frame(
        &mut bytes,
        &Reply::Status {
            status: Box::new(status.clone()),
        },
    )
    .unwrap();
    assert!(bytes.len() <= MAX_FRAME + 4);
    assert_eq!(status.counts.uncertain, 64);
    assert_eq!(status.counts.running, 0);
    assert!(!status.quiescent);
}
fn status(socket: &Path, command: Command) -> Status {
    let value = operate(socket, &command).unwrap();
    bounded(&value);
    value
}

#[test]
fn escaped_job_labels_and_many_groups_paginate_after_durable_drain() {
    let root = std::env::temp_dir().join(format!(
        "mini-status-bounds-{}-{}",
        std::process::id(),
        now_ms()
    ));
    fs::create_dir(&root).unwrap();
    fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
    fs::create_dir(root.join("state")).unwrap();
    fs::set_permissions(root.join("state"), fs::Permissions::from_mode(0o700)).unwrap();
    let label = "\\\"".repeat(128); // 256 bytes, 512 escaped JSON bytes.
    assert_eq!(label.len(), 256);
    let endpoint = "http://127.0.0.1:9/v1/chat/completions";
    let mut groups: BTreeMap<_, _> = (0..3000).map(|n| (format!("g{n:04}"), 1)).collect();
    groups.insert("g0000".into(), 64);
    let config = Config {
        version: 1,
        max_jobs: 200,
        max_queued_per_principal: 100,
        max_active_per_principal: 64,
        lease_ms: 60_000,
        groups,
        controllers: BTreeMap::from([(
            label.clone(),
            Registration {
                uid: unsafe { libc::geteuid() },
                principal: label.clone(),
                pool: "members".into(),
            },
        )]),
        backends: BTreeMap::from([(
            "backend".into(),
            Backend {
                pool: "members".into(),
                group: "g0000".into(),
                endpoint: endpoint.into(),
                models: BTreeMap::from([(
                    label.clone(),
                    Model {
                        context: 4096,
                        max_output: 512,
                        tools: true,
                        input_us: 10,
                        output_us: 100,
                    },
                )]),
            },
        )]),
    };
    let encoded_config = serde_json::to_vec(&config).unwrap();
    assert!(
        encoded_config.len() <= 65_536,
        "fixture must fit production inventory bound"
    );
    fs::write(root.join("config.json"), encoded_config).unwrap();
    let mut core = Core::new(&config).unwrap();
    let now = now_ms();
    let mut expected_jobs = BTreeSet::new();
    for n in 0..64 {
        let id = digest(format!("status-job-{n}").as_bytes());
        let request = Request {
            id: id.clone(),
            request_digest: digest(format!("private-body-{n}").as_bytes()),
            model: label.clone(),
            max_input: 100,
            max_output: 20,
            tools: true,
            queue_deadline_ms: now + 120_000,
            allowed_endpoints: vec![endpoint.into()],
        };
        core.enqueue(&config, &label, request, now).unwrap();
        let lease = match core.inspect(&label, &id).unwrap().state {
            State::Placed { lease, .. } => lease,
            other => panic!("{other:?}"),
        };
        core.dispatch(&label, &id, lease, format!("private-attempt-{n}"), now)
            .unwrap();
        expected_jobs.insert(id);
    }
    fs::write(
        root.join("state/state.json"),
        serde_json::to_vec(&core).unwrap(),
    )
    .unwrap();
    fs::set_permissions(
        root.join("state/state.json"),
        fs::Permissions::from_mode(0o600),
    )
    .unwrap();
    let child = ProcessCommand::new(std::env::current_exe().unwrap())
        .args(["--exact", "status_bounds_child", "--nocapture"])
        .env("MINI_STATUS_BOUNDS_CHILD", &root)
        .spawn()
        .unwrap();
    let mut daemon = Daemon { root, child };
    let socket = daemon.root.join("control.sock");
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        assert!(daemon.child.try_wait().unwrap().is_none());
        if operate(
            &socket,
            &Command::Status {
                after: None,
                limit: 64,
            },
        )
        .is_ok()
        {
            break;
        }
        assert!(Instant::now() < deadline);
        std::thread::sleep(Duration::from_millis(5));
    }
    let drained = status(&socket, Command::Drain { enabled: true });
    assert!(drained.draining);
    assert!(
        drained.next_after.is_some(),
        "byte bound must shorten the 64-job page"
    );
    assert!(
        drained.next_group_after.is_some(),
        "large group inventory needs a cursor"
    );
    assert!(
        !drained.groups.is_empty(),
        "job labels cannot starve group pagination"
    );
    let mut jobs = BTreeSet::new();
    let mut after = None;
    loop {
        let page = status(
            &socket,
            Command::Status {
                after: after.clone(),
                limit: 64,
            },
        );
        assert!(page.draining);
        for job in page.jobs {
            assert!(jobs.insert(job.id), "duplicate job across pages");
        }
        match page.next_after {
            Some(next) => {
                assert_ne!(after.as_ref(), Some(&next));
                after = Some(next);
            }
            None => break,
        }
    }
    assert_eq!(jobs, expected_jobs);
    let mut groups = BTreeSet::new();
    let mut after = None;
    loop {
        let page = status(
            &socket,
            Command::StatusGroups {
                after: after.clone(),
            },
        );
        for group in page.groups.into_keys() {
            assert!(groups.insert(group), "duplicate group across pages");
        }
        match page.next_group_after {
            Some(next) => {
                assert_ne!(after.as_ref(), Some(&next));
                after = Some(next);
            }
            None => break,
        }
    }
    assert_eq!(groups, config.groups.into_keys().collect());
    let resumed = status(&socket, Command::Drain { enabled: false });
    assert!(!resumed.draining);
    let persisted: Core =
        serde_json::from_slice(&fs::read(daemon.root.join("state/state.json")).unwrap()).unwrap();
    assert!(!persisted.draining);
    assert_eq!(persisted.jobs.len(), 64);
    assert!(persisted
        .jobs
        .values()
        .all(|job| matches!(job.state, State::Uncertain { .. })));
}
