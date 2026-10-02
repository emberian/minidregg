#![cfg(target_os = "linux")]
//! Operator journeys use the genuine CLI against a real Unix Service process.
//! Provider work is represented by exact scheduler transitions; no inference runs.
use minidregg_inference_scheduler::{
    core::*,
    digest, operate, request,
    service::{now_ms, Service, Status},
    Command,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command as ProcessCommand, Output};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

const ENDPOINT: &str = "http://127.0.0.1:9/v1/chat/completions";
fn config() -> Config {
    Config {
        version: 1,
        max_jobs: 200,
        max_queued_per_principal: 100,
        max_active_per_principal: 1,
        lease_ms: 60_000,
        groups: BTreeMap::from([("gpu".into(), 3)]),
        controllers: ["a", "b", "c", "d"]
            .into_iter()
            .map(|name| {
                (
                    name.into(),
                    Registration {
                        uid: unsafe { libc::geteuid() },
                        principal: format!("member-{name}"),
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
                endpoint: ENDPOINT.into(),
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
fn directory() -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let root = std::env::temp_dir().join(format!(
        "mini-scheduler-operations-{}-{}-{}",
        std::process::id(),
        now_ms(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&root).unwrap();
    fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
    root
}
#[test]
fn operator_service_child() {
    let Some(root) = std::env::var_os("MINI_SCHEDULER_OPERATIONS_CHILD") else {
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
        let mut daemon = Self {
            root: directory(),
            child: None,
        };
        daemon.spawn();
        daemon
    }
    fn socket(&self) -> PathBuf {
        self.root.join("scheduler.sock")
    }
    fn spawn(&mut self) {
        self.child = Some(
            ProcessCommand::new(std::env::current_exe().unwrap())
                .args(["--exact", "operator_service_child", "--nocapture"])
                .env("MINI_SCHEDULER_OPERATIONS_CHILD", &self.root)
                .spawn()
                .unwrap(),
        );
        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            assert!(
                self.child.as_mut().unwrap().try_wait().unwrap().is_none(),
                "operator service child exited"
            );
            if operate(
                &self.socket(),
                &Command::Status {
                    after: None,
                    limit: 1,
                },
            )
            .is_ok()
            {
                break;
            }
            assert!(
                Instant::now() < deadline,
                "operator service readiness deadline"
            );
            std::thread::sleep(Duration::from_millis(5));
        }
    }
    fn restart(&mut self) {
        let mut child = self.child.take().unwrap();
        child.kill().unwrap();
        child.wait().unwrap();
        self.spawn();
    }
    fn cli(&self, verb: &str, extra: Option<&str>) -> Output {
        let mut command = ProcessCommand::new(env!("CARGO_BIN_EXE_mini-inference-scheduler"));
        command.arg(verb).arg(self.socket());
        if let Some(extra) = extra {
            command.arg(extra);
        }
        command.output().unwrap()
    }
    fn ok(&self, verb: &str, extra: Option<&str>) -> Status {
        let result = self.cli(verb, extra);
        assert!(
            result.status.success(),
            "CLI {verb}: {}",
            String::from_utf8_lossy(&result.stderr)
        );
        serde_json::from_slice(&result.stdout).unwrap()
    }
}
impl Drop for Daemon {
    fn drop(&mut self) {
        if let Some(mut child) = self.child.take() {
            let _ = child.kill();
            let _ = child.wait();
        }
        let _ = fs::remove_dir_all(&self.root);
    }
}
fn job(name: &str, now: u64) -> Request {
    Request {
        id: digest(name.as_bytes()),
        request_digest: digest(format!("private-prompt-marker-{name}").as_bytes()),
        model: "test-model".into(),
        max_input: 100,
        max_output: 20,
        tools: true,
        allowed_endpoints: vec![ENDPOINT.into()],
        queue_deadline_ms: now + 120_000,
    }
}
fn enqueue(socket: &Path, controller: &str, name: &str) -> Job {
    request(
        socket,
        &Command::Enqueue {
            controller: controller.into(),
            job: job(name, now_ms()),
        },
    )
    .unwrap()
}
fn inspect(socket: &Path, controller: &str, job: &Job) -> Job {
    request(
        socket,
        &Command::Inspect {
            controller: controller.into(),
            id: job.request.id.clone(),
        },
    )
    .unwrap()
}
fn ticket(job: &Job) -> u64 {
    match job.state {
        State::Placed { lease, .. } => lease,
        ref other => panic!("expected placed, got {other:?}"),
    }
}
fn dispatch(socket: &Path, controller: &str, job: &Job) {
    request(
        socket,
        &Command::Dispatch {
            controller: controller.into(),
            id: job.request.id.clone(),
            lease: ticket(job),
            attempt: format!("private-provider-attempt-{controller}"),
        },
    )
    .unwrap();
}
fn finish(socket: &Path, controller: &str, job: &Job, outcome: Outcome) -> Job {
    request(
        socket,
        &Command::Finish {
            controller: controller.into(),
            id: job.request.id.clone(),
            lease: ticket(job),
            outcome,
        },
    )
    .unwrap()
}

#[test]
fn cli_drain_resume_and_restart_preserve_uncertainty_and_allow_running_completion() {
    let mut daemon = Daemon::start();
    let socket = daemon.socket();
    let a = enqueue(&socket, "a", "running");
    dispatch(&socket, "a", &a);
    let b = enqueue(&socket, "b", "uncertain");
    dispatch(&socket, "b", &b);
    finish(&socket, "b", &b, Outcome::Uncertain);
    let c = enqueue(&socket, "c", "placed");
    let d = enqueue(&socket, "d", "queued");
    assert_eq!(d.state, State::Queued);
    let before = daemon.ok("status", None);
    assert_eq!(
        (
            before.counts.running,
            before.counts.uncertain,
            before.counts.placed,
            before.counts.queued
        ),
        (1, 1, 1, 1)
    );
    let drained = daemon.ok("drain", None);
    assert!(drained.draining);
    assert!(!drained.quiescent);
    assert_eq!(
        (
            drained.counts.running,
            drained.counts.uncertain,
            drained.counts.placed,
            drained.counts.queued,
            drained.counts.terminal
        ),
        (1, 1, 0, 0, 2)
    );
    for (name, old) in [("c", &c), ("d", &d)] {
        assert!(matches!(
            inspect(&socket, name, old).state,
            State::Terminal {
                outcome: Outcome::Drained,
                ..
            }
        ));
        let replay = request(
            &socket,
            &Command::Enqueue {
                controller: name.into(),
                job: old.request.clone(),
            },
        )
        .unwrap();
        assert!(matches!(
            replay.state,
            State::Terminal {
                outcome: Outcome::Drained,
                ..
            }
        ));
    }
    assert!(request(
        &socket,
        &Command::Enqueue {
            controller: "d".into(),
            job: job("new-during-drain", now_ms())
        }
    )
    .unwrap_err()
    .contains("drain"));
    assert!(
        request(
            &socket,
            &Command::Dispatch {
                controller: "c".into(),
                id: c.request.id.clone(),
                lease: ticket(&c),
                attempt: "late-drained-send".into()
            }
        )
        .is_err(),
        "drained placement must not authorize a later send"
    );
    // Running completion remains usable while admission is closed.
    assert!(matches!(
        finish(&socket, "a", &a, Outcome::Ended).state,
        State::Terminal {
            outcome: Outcome::Ended,
            ..
        }
    ));
    daemon.restart();
    let restored = daemon.ok("status", None);
    assert!(restored.draining);
    assert!(!restored.quiescent);
    assert_eq!(restored.counts.uncertain, 1);
    assert!(
        matches!(inspect(&socket, "b", &b).state, State::Uncertain { lease, ref attempt, .. } if lease == ticket(&b) && attempt == "private-provider-attempt-b")
    );
    assert!(request(
        &socket,
        &Command::Enqueue {
            controller: "a".into(),
            job: job("new-after-restart", now_ms())
        }
    )
    .is_err());
    // A bounded drain wait reports unresolved physical work; it cannot erase it.
    let waiting = daemon.cli("drain", Some("1"));
    assert!(!waiting.status.success());
    let waiting_status: Status = serde_json::from_slice(&waiting.stdout).unwrap();
    assert!(waiting_status.draining);
    assert_eq!(waiting_status.counts.uncertain, 1);
    assert!(String::from_utf8_lossy(&waiting.stderr).contains("running or uncertain"));
    let resumed = daemon.ok("resume", None);
    assert!(!resumed.draining);
    assert_eq!(resumed.counts.uncertain, 1);
    let fresh = enqueue(&socket, "c", "new-after-resume");
    let fresh_lease = ticket(&fresh);
    // Late cleanup of the drained unsent allocation cannot release its successor.
    assert!(matches!(
        finish(&socket, "c", &c, Outcome::NotSent).state,
        State::Terminal {
            outcome: Outcome::Drained,
            ..
        }
    ));
    assert_eq!(ticket(&inspect(&socket, "c", &fresh)), fresh_lease);
    finish(&socket, "b", &b, Outcome::Ended);
    request(
        &socket,
        &Command::Cancel {
            controller: "c".into(),
            id: fresh.request.id,
        },
    )
    .unwrap();
    let quiet = daemon.ok("status", None);
    assert!(quiet.quiescent);
    assert_eq!(quiet.counts.uncertain, 0);
    assert!(daemon.ok("drain", Some("1")).quiescent);
}

#[test]
fn cli_status_pages_are_bounded_and_omit_request_and_destination_material() {
    let daemon = Daemon::start();
    let socket = daemon.socket();
    let mut expected = BTreeSet::new();
    let mut private_digests = Vec::new();
    for index in 0..35 {
        let controller = ["a", "b", "c", "d"][index % 4];
        let job = enqueue(&socket, controller, &format!("pagination-{index}"));
        expected.insert(job.request.id);
        private_digests.push(job.request.request_digest);
    }
    let first_output = daemon.cli("status", None);
    assert!(first_output.status.success());
    let first: Status = serde_json::from_slice(&first_output.stdout).unwrap();
    assert_eq!(first.jobs.len(), 32);
    assert_eq!(first.counts.queued + first.counts.placed, 35);
    let cursor = first.next_after.as_deref().expect("bounded page cursor");
    let second_output = daemon.cli("status", Some(cursor));
    assert!(second_output.status.success());
    let second: Status = serde_json::from_slice(&second_output.stdout).unwrap();
    assert_eq!(second.jobs.len(), 3);
    assert!(second.next_after.is_none());
    assert_eq!(
        second.counts.queued + second.counts.placed,
        35,
        "counts describe all jobs, not just this page"
    );
    let actual: BTreeSet<_> = first
        .jobs
        .iter()
        .chain(&second.jobs)
        .map(|job| job.id.clone())
        .collect();
    assert_eq!(actual, expected);
    for output in [&first_output, &second_output] {
        let text = String::from_utf8_lossy(&output.stdout);
        for omitted in [
            ENDPOINT,
            "request_digest",
            "allowed_endpoints",
            "exact_body",
            "queue_deadline_ms",
            "private-prompt-marker",
            "private-provider-attempt",
        ] {
            assert!(!text.contains(omitted), "status leaked {omitted}");
        }
        for private_digest in &private_digests {
            assert!(
                !text.contains(private_digest),
                "status leaked request digest"
            );
        }
        let json: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        for job in json["jobs"].as_array().unwrap() {
            let fields: BTreeSet<_> = job
                .as_object()
                .unwrap()
                .keys()
                .map(String::as_str)
                .collect();
            assert_eq!(
                fields,
                BTreeSet::from(["id", "controller", "principal", "model", "state"])
            );
        }
    }
    for limit in [0, 65] {
        assert!(operate(&socket, &Command::Status { after: None, limit }).is_err());
    }
}

#[test]
fn expiry_cleanup_keeps_successors_and_operator_authentication_cannot_mutate_state() {
    let root = directory();
    let uid = unsafe { libc::geteuid() };
    let mut cfg = config();
    cfg.groups.insert("gpu".into(), 1);
    cfg.lease_ms = 100;
    {
        let mut service = Service::open(cfg, &root.join("state")).unwrap();
        let a = service
            .execute(
                uid,
                Command::Enqueue {
                    controller: "a".into(),
                    job: job("expired-a", 1000),
                },
                1000,
            )
            .unwrap();
        let a_lease = ticket(&a);
        let b = service
            .execute(
                uid,
                Command::Enqueue {
                    controller: "b".into(),
                    job: job("successor-b", 1100),
                },
                1100,
            )
            .unwrap();
        let b_lease = ticket(&b);
        service
            .execute(
                uid,
                Command::Dispatch {
                    controller: "b".into(),
                    id: b.request.id.clone(),
                    lease: b_lease,
                    attempt: "successor-send".into(),
                },
                1101,
            )
            .unwrap();
        let cleaned = service
            .execute(
                uid,
                Command::Finish {
                    controller: "a".into(),
                    id: a.request.id.clone(),
                    lease: a_lease,
                    outcome: Outcome::NotSent,
                },
                1102,
            )
            .unwrap();
        assert!(matches!(
            cleaned.state,
            State::Terminal {
                outcome: Outcome::Expired,
                ..
            }
        ));
        let live = service
            .execute(
                uid,
                Command::Inspect {
                    controller: "b".into(),
                    id: b.request.id,
                },
                1102,
            )
            .unwrap();
        assert!(matches!(live.state, State::Dispatched { lease, .. } if lease == b_lease));
        assert!(service
            .execute(
                uid,
                Command::Finish {
                    controller: "a".into(),
                    id: a.request.id,
                    lease: a_lease + 1000,
                    outcome: Outcome::NotSent
                },
                1102
            )
            .is_err());
        let foreign = if uid == 1 { 2 } else { 1 };
        assert!(service
            .operator(foreign, Some(true), None, 32, 1102)
            .unwrap_err()
            .contains("operator"));
        for limit in [0, 65] {
            assert!(service
                .operator(uid, Some(true), None, limit, 1102)
                .is_err());
        }
        let status = service.operator(uid, None, None, 32, 1102).unwrap();
        assert!(!status.draining);
        assert_eq!(status.counts.running, 1);
        assert!(!status.quiescent);
    }
    fs::remove_dir_all(root).unwrap();
}
