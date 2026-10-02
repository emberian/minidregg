#![cfg(target_os = "linux")]
use minidregg_inference_scheduler::{
    core::*,
    digest, request,
    service::{now_ms, Service},
    Command,
};
use std::collections::BTreeMap;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command as ProcessCommand};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

fn config() -> Config {
    let uid = unsafe { libc::geteuid() };
    Config {
        version: 1,
        max_terminal_receipts: 1000000,
        max_receipt_bytes: 8 * 1024 * 1024 * 1024,
        max_jobs: 100,
        max_queued_per_principal: 8,
        max_active_per_principal: 1,
        lease_ms: 60_000,
        groups: BTreeMap::from([("physical-gpu".into(), 1)]),
        controllers: [
            ("controller-a", "alice", uid),
            ("controller-b", "bob", uid),
            ("wrong-uid", "mallory", uid.wrapping_add(1)),
        ]
        .into_iter()
        .map(|(id, principal, uid)| {
            (
                id.into(),
                Registration {
                    uid,
                    principal: principal.into(),
                    pool: "members".into(),
                },
            )
        })
        .collect(),
        backends: BTreeMap::from([(
            "local".into(),
            Backend {
                pool: "members".into(),
                group: "physical-gpu".into(),
                endpoint: "http://127.0.0.1:9/v1/chat/completions".into(),
                models: BTreeMap::from([(
                    "test-model".into(),
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
    }
}

// Spawn the test executable as a separate daemon process. This exercises the
// same Service::serve framing, peer credentials and durable state as the CLI,
// without requiring root to provision a production-owned configuration file.
#[test]
fn scheduler_service_child() {
    let Some(root) = std::env::var_os("MINI_SCHEDULER_TEST_CHILD") else {
        return;
    };
    let root = PathBuf::from(root);
    Service::open(config(), &root.join("state"))
        .unwrap()
        .serve(&root.join("scheduler.sock"))
        .unwrap();
}

struct Daemon {
    root: PathBuf,
    child: Option<Child>,
}
impl Daemon {
    fn start() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let root = std::env::temp_dir().join(format!(
            "mini-scheduler-{}-{}-{}",
            std::process::id(),
            now_ms(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
        let mut daemon = Self { root, child: None };
        daemon.spawn();
        daemon
    }
    fn socket(&self) -> PathBuf {
        self.root.join("scheduler.sock")
    }
    fn spawn(&mut self) {
        self.child = Some(
            ProcessCommand::new(std::env::current_exe().unwrap())
                .args(["--exact", "scheduler_service_child", "--nocapture"])
                .env("MINI_SCHEDULER_TEST_CHILD", &self.root)
                .spawn()
                .unwrap(),
        );
        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            assert!(
                self.child.as_mut().unwrap().try_wait().unwrap().is_none(),
                "scheduler child exited before readiness"
            );
            // A framed request verifies the new listener rather than trusting a
            // stale filesystem socket from the process killed for restart.
            let result = request(
                &self.socket(),
                &Command::Inspect {
                    controller: "controller-a".into(),
                    id: digest(b"readiness"),
                },
            );
            if result.is_err_and(|reason| reason.contains("unknown job")) {
                break;
            }
            assert!(Instant::now() < deadline, "scheduler readiness deadline");
            std::thread::sleep(Duration::from_millis(5));
        }
    }
    fn stop(&mut self) {
        if let Some(mut child) = self.child.take() {
            child.kill().unwrap();
            child.wait().unwrap();
        }
    }
    fn restart(&mut self) {
        self.stop();
        self.spawn();
    }
}
impl Drop for Daemon {
    fn drop(&mut self) {
        if let Some(mut child) = self.child.take() {
            let _ = child.kill();
            let _ = child.wait();
        }
        // Only this fixture's fresh, uniquely created tree is removed.
        let _ = fs::remove_dir_all(&self.root);
    }
}
fn enqueue(socket: &Path, controller: &str, name: &str) -> Job {
    let body = Request {
        id: digest(name.as_bytes()),
        request_digest: digest(format!("body-{name}").as_bytes()),
        model: "test-model".into(),
        max_input: 100,
        max_output: 20,
        tools: true,
        allowed_endpoints: vec!["http://127.0.0.1:9/v1/chat/completions".into()],
        queue_deadline_ms: now_ms() + 120_000,
    };
    request(
        socket,
        &Command::Enqueue {
            controller: controller.into(),
            job: body,
        },
    )
    .unwrap()
}
fn inspect(socket: &Path, controller: &str, id: &str) -> Job {
    request(
        socket,
        &Command::Inspect {
            controller: controller.into(),
            id: id.into(),
        },
    )
    .unwrap()
}
fn ticket(job: &Job) -> u64 {
    match job.state {
        State::Placed { lease, .. } => lease,
        ref state => panic!("expected placed, got {state:?}"),
    }
}
fn dispatch(socket: &Path, controller: &str, job: &Job, lease: u64) -> Job {
    request(
        socket,
        &Command::Dispatch {
            controller: controller.into(),
            id: job.request.id.clone(),
            lease,
            attempt: "provider-attempt-one".into(),
        },
    )
    .unwrap()
}

#[test]
fn two_socket_controllers_share_capacity_and_recover_without_resending() {
    let mut daemon = Daemon::start();
    let socket = daemon.socket();
    let a = enqueue(&socket, "controller-a", "first-controller-job");
    let old_lease = ticket(&a);
    let b = enqueue(&socket, "controller-b", "second-controller-job");
    assert_eq!(b.state, State::Queued);
    assert!(request(
        &socket,
        &Command::Inspect {
            controller: "controller-b".into(),
            id: a.request.id.clone()
        }
    )
    .is_err());

    // A response-lost placement is safe to place again only with a fresh lease.
    daemon.restart();
    let recovered = inspect(&socket, "controller-a", &a.request.id);
    let lease = ticket(&recovered);
    assert_ne!(lease, old_lease);
    assert!(request(
        &socket,
        &Command::Dispatch {
            controller: "controller-a".into(),
            id: a.request.id.clone(),
            lease: old_lease,
            attempt: "stale".into()
        }
    )
    .is_err());
    dispatch(&socket, "controller-a", &a, lease);
    assert!(request(
        &socket,
        &Command::Dispatch {
            controller: "controller-a".into(),
            id: a.request.id.clone(),
            lease,
            attempt: "provider-attempt-one".into()
        }
    )
    .is_err());

    // A process crash after dispatch leaves the exact attempt quarantined and
    // the competing controller queued, even though a new daemon is serving.
    daemon.restart();
    let uncertain = inspect(&socket, "controller-a", &a.request.id);
    assert!(
        matches!(uncertain.state, State::Uncertain { lease: actual, ref attempt, .. } if actual == lease && attempt == "provider-attempt-one")
    );
    assert_eq!(
        inspect(&socket, "controller-b", &b.request.id).state,
        State::Queued
    );
    request(
        &socket,
        &Command::Cancel {
            controller: "controller-a".into(),
            id: a.request.id.clone(),
        },
    )
    .unwrap();
    assert_eq!(
        inspect(&socket, "controller-b", &b.request.id).state,
        State::Queued
    );

    let finish = Command::Finish {
        controller: "controller-a".into(),
        id: a.request.id.clone(),
        lease,
        outcome: Outcome::Ended,
    };
    let terminal = request(&socket, &finish).unwrap();
    assert!(matches!(
        terminal.state,
        State::Terminal {
            outcome: Outcome::Ended,
            ..
        }
    ));
    let b_placed = inspect(&socket, "controller-b", &b.request.id);
    let b_lease = ticket(&b_placed);
    assert_eq!(request(&socket, &finish).unwrap().state, terminal.state);
    assert!(request(
        &socket,
        &Command::Finish {
            controller: "controller-a".into(),
            id: a.request.id.clone(),
            lease: lease + 1,
            outcome: Outcome::Ended
        }
    )
    .is_err());
    assert_eq!(
        ticket(&inspect(&socket, "controller-b", &b.request.id)),
        b_lease
    );
    let cancelled = request(
        &socket,
        &Command::Cancel {
            controller: "controller-b".into(),
            id: b.request.id,
        },
    )
    .unwrap();
    assert!(matches!(
        cancelled.state,
        State::Terminal {
            outcome: Outcome::Cancelled,
            ..
        }
    ));
}

#[test]
fn peer_uid_registration_and_request_identity_are_enforced_over_socket() {
    let daemon = Daemon::start();
    let socket = daemon.socket();
    let a = enqueue(&socket, "controller-a", "identity");
    let refused = request(
        &socket,
        &Command::Inspect {
            controller: "wrong-uid".into(),
            id: a.request.id.clone(),
        },
    )
    .unwrap_err();
    assert!(refused.contains("peer uid"), "{refused}");
    assert!(request(
        &socket,
        &Command::Inspect {
            controller: "unregistered".into(),
            id: a.request.id.clone()
        }
    )
    .unwrap_err()
    .contains("unregistered"));
    let same = Command::Enqueue {
        controller: "controller-a".into(),
        job: a.request.clone(),
    };
    assert_eq!(request(&socket, &same).unwrap().state, a.state);
    let mut changed = a.request.clone();
    changed.request_digest = digest(b"other-body");
    assert!(request(
        &socket,
        &Command::Enqueue {
            controller: "controller-a".into(),
            job: changed
        }
    )
    .unwrap_err()
    .contains("identity conflicts"));
    assert_eq!(
        inspect(&socket, "controller-a", &a.request.id).state,
        a.state
    );
    assert!(
        Service::open(config(), &daemon.root.join("state")).is_err(),
        "second process acquired live state"
    );
}
