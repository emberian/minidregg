#![cfg(target_os = "linux")]
use minidregg_inference_scheduler::{core::*, digest, service::Service, Command};
use std::collections::BTreeMap;
use std::fs;
use std::os::unix::fs::PermissionsExt;

fn config() -> Config {
    Config {
        version: 1,
        max_jobs: 2,
        max_terminal_receipts: 1000,
        max_receipt_bytes: 16 * 1024 * 1024,
        max_queued_per_principal: 2,
        max_active_per_principal: 1,
        lease_ms: 60000,
        groups: BTreeMap::from([("gpu".into(), 1)]),
        controllers: ["one", "two"]
            .into_iter()
            .map(|id| {
                (
                    id.into(),
                    Registration {
                        uid: unsafe { libc::geteuid() },
                        principal: "member-500".into(),
                        pool: "members".into(),
                    },
                )
            })
            .collect(),
        backends: BTreeMap::from([(
            "local".into(),
            Backend {
                pool: "members".into(),
                group: "gpu".into(),
                endpoint: "http://127.0.0.1:9/".into(),
                models: BTreeMap::from([(
                    "m".into(),
                    Model {
                        context: 1000,
                        max_output: 100,
                        tools: false,
                        input_us: 10,
                        output_us: 100,
                    },
                )]),
            },
        )]),
    }
}
fn job(index: usize) -> Request {
    Request {
        id: digest(index.to_string().as_bytes()),
        request_digest: digest(format!("body-{index}").as_bytes()),
        model: "m".into(),
        max_input: 10,
        max_output: 10,
        tools: false,
        queue_deadline_ms: 100000,
        allowed_endpoints: vec!["http://127.0.0.1:9/".into()],
    }
}
fn call(service: &mut Service, command: Command) -> Job {
    service
        .execute(unsafe { libc::geteuid() }, command, 1)
        .unwrap()
}
fn enqueue(service: &mut Service, index: usize) -> Job {
    call(
        service,
        Command::Enqueue {
            controller: "one".into(),
            job: job(index),
        },
    )
}
fn finish(service: &mut Service, value: &Job) -> Job {
    let State::Placed { lease, .. } = value.state else {
        panic!("not placed")
    };
    call(
        service,
        Command::Finish {
            controller: "one".into(),
            id: value.request.id.clone(),
            lease,
            outcome: Outcome::NotSent,
        },
    )
}
struct Fixture(std::path::PathBuf);
impl Fixture {
    fn new(label: &str) -> Self {
        let root = std::env::temp_dir().join(format!(
            "mini-scheduler-retention-{}-{label}",
            std::process::id()
        ));
        fs::create_dir(&root).unwrap();
        fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
        Self(root)
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn many_completed_jobs_keep_live_capacity_bounded_and_exact_receipts_after_restart() {
    let fixture = Fixture::new("many");
    let cfg = config();
    let mut service = Service::open(cfg.clone(), &fixture.0).unwrap();
    let mut receipts = vec![];
    for index in 0..100 {
        let placed = enqueue(&mut service, index);
        receipts.push(finish(&mut service, &placed));
        let snapshot: Core =
            serde_json::from_slice(&fs::read(fixture.0.join("state.json")).unwrap()).unwrap();
        assert!(snapshot.jobs.is_empty());
        assert_eq!(snapshot.archived_receipts, index + 1);
    }
    let status = service
        .operator(unsafe { libc::geteuid() }, None, None, 64, 1)
        .unwrap();
    assert_eq!(status.terminal_receipts, 100);
    assert!(status.receipt_bytes > 0);
    drop(service);
    let mut service = Service::open(cfg, &fixture.0).unwrap();
    for (index, saved) in receipts.iter().enumerate() {
        assert_eq!(enqueue(&mut service, index), *saved);
    }
    let mut changed = job(0);
    changed.max_output += 1;
    assert!(service
        .execute(
            unsafe { libc::geteuid() },
            Command::Enqueue {
                controller: "one".into(),
                job: changed
            },
            2
        )
        .unwrap_err()
        .contains("identity conflicts"));
    assert!(service
        .execute(
            unsafe { libc::geteuid() },
            Command::Enqueue {
                controller: "two".into(),
                job: job(0)
            },
            2
        )
        .is_err());
    let held = enqueue(&mut service, 101);
    let queued = enqueue(&mut service, 102);
    assert_eq!(queued.state, State::Queued);
    assert!(service
        .execute(
            unsafe { libc::geteuid() },
            Command::Enqueue {
                controller: "one".into(),
                job: job(103)
            },
            2
        )
        .unwrap_err()
        .contains("active job capacity"));
    finish(&mut service, &held);
}

#[test]
fn death_between_receipt_and_hot_retirement_recovers_completion_without_resend() {
    let fixture = Fixture::new("crash");
    let cfg = config();
    let mut service = Service::open(cfg.clone(), &fixture.0).unwrap();
    let placed = enqueue(&mut service, 0);
    let State::Placed { lease, .. } = placed.state else {
        panic!()
    };
    call(
        &mut service,
        Command::Dispatch {
            controller: "one".into(),
            id: placed.request.id.clone(),
            lease,
            attempt: "attempt-0".into(),
        },
    );
    let old = fs::read(fixture.0.join("state.json")).unwrap();
    let terminal = call(
        &mut service,
        Command::Finish {
            controller: "one".into(),
            id: placed.request.id.clone(),
            lease,
            outcome: Outcome::Ended,
        },
    );
    drop(service);
    // This is the exact persisted cut between durable receipt and atomic snapshot.
    fs::write(fixture.0.join("state.json"), old).unwrap();
    let mut service = Service::open(cfg, &fixture.0).unwrap();
    assert_eq!(enqueue(&mut service, 0), terminal);
    assert!(service
        .execute(
            unsafe { libc::geteuid() },
            Command::Dispatch {
                controller: "one".into(),
                id: placed.request.id.clone(),
                lease,
                attempt: "resend".into()
            },
            2
        )
        .is_err());
    assert_eq!(
        service
            .operator(unsafe { libc::geteuid() }, None, None, 64, 2)
            .unwrap()
            .terminal_receipts,
        1
    );
}

#[test]
fn uncertain_work_never_retires_and_archive_limit_has_safe_actionable_recovery() {
    let fixture = Fixture::new("limit");
    let mut cfg = config();
    cfg.max_terminal_receipts = 2;
    let mut service = Service::open(cfg.clone(), &fixture.0).unwrap();
    let first = enqueue(&mut service, 0);
    finish(&mut service, &first);
    let held = enqueue(&mut service, 1);
    let State::Placed { lease, .. } = held.state else {
        panic!()
    };
    call(
        &mut service,
        Command::Dispatch {
            controller: "one".into(),
            id: held.request.id.clone(),
            lease,
            attempt: "held-1".into(),
        },
    );
    call(
        &mut service,
        Command::Finish {
            controller: "one".into(),
            id: held.request.id.clone(),
            lease,
            outcome: Outcome::Uncertain,
        },
    );
    assert!(!fixture.0.join("receipts").join(&held.request.id).exists());
    assert!(service
        .execute(
            unsafe { libc::geteuid() },
            Command::Enqueue {
                controller: "two".into(),
                job: job(2)
            },
            2
        )
        .unwrap_err()
        .contains("archive admission full"));
    drop(service);
    cfg.max_terminal_receipts = 1000;
    cfg.max_receipt_bytes *= 2;
    let mut service = Service::open(cfg, &fixture.0).unwrap();
    assert!(matches!(
        call(
            &mut service,
            Command::Inspect {
                controller: "one".into(),
                id: held.request.id.clone()
            }
        )
        .state,
        State::Uncertain { .. }
    ));
    assert_eq!(enqueue(&mut service, 2).state, State::Queued);
    call(
        &mut service,
        Command::Finish {
            controller: "one".into(),
            id: held.request.id,
            lease,
            outcome: Outcome::Ended,
        },
    );
}
