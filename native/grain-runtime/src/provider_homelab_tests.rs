//! Physical receiving-path acceptance. Mini signed controller acknowledgements
//! are deliberately faked here; Unix scheduling, GatewayEndpoint, curl HTTP I/O,
//! placement verification and dispatch/recovery transitions are real.
use super::*;
use minidregg_inference_scheduler::{self as scheduler, core as sc, service::Service};
use std::collections::BTreeMap;

const TOKEN: &str = "homelab_test_worker_token_0123456789abcdef";
const BODY: &[u8] = br#"{"model":"operator-model","messages":[{"role":"user","content":"hello"}]}"#;

#[test]
fn homelab_scheduler_child() {
    let Some(root) = std::env::var_os("MINI_PROVIDER_SCHEDULER_CHILD") else {
        return;
    };
    let root = PathBuf::from(root);
    let config = serde_json::from_slice(&fs::read(root.join("config.json")).unwrap()).unwrap();
    Service::open(config, &root.join("state"))
        .unwrap()
        .serve(&root.join("scheduler.sock"))
        .unwrap();
}

fn until(mut condition: impl FnMut() -> bool) {
    let deadline = Instant::now() + Duration::from_secs(8);
    while !condition() {
        assert!(Instant::now() < deadline, "condition deadline elapsed");
        thread::sleep(Duration::from_millis(5));
    }
}

struct SchedulerFixture {
    root: PathBuf,
    child: Child,
}
impl SchedulerFixture {
    fn start(a: SocketAddr, b: SocketAddr) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let root = std::env::temp_dir().join(format!(
            "mini-provider-scheduler-{}-{}-{}",
            std::process::id(),
            scheduler::service::now_ms(),
            NEXT.fetch_add(1, Ordering::SeqCst)
        ));
        fs::create_dir(&root).unwrap();
        fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
        let mut config = sc::Config {
            version: 1,
            max_jobs: 100,
            max_queued_per_principal: 8,
            max_active_per_principal: 1,
            lease_ms: 60_000,
            groups: BTreeMap::from([("shared-gpu".into(), 1)]),
            controllers: BTreeMap::new(),
            backends: BTreeMap::new(),
        };
        for (name, addr) in [("a", a), ("b", b)] {
            config.controllers.insert(
                name.into(),
                sc::Registration {
                    uid: unsafe { libc::geteuid() },
                    principal: format!("member-{name}"),
                    pool: format!("pool-{name}"),
                },
            );
            config.backends.insert(
                name.into(),
                sc::Backend {
                    pool: format!("pool-{name}"),
                    group: "shared-gpu".into(),
                    endpoint: format!("http://{addr}/v1/chat/completions"),
                    models: BTreeMap::from([(
                        "operator-model".into(),
                        sc::Model {
                            context: 4096,
                            max_output: 512,
                            tools: true,
                            input_us: 10,
                            output_us: 100,
                        },
                    )]),
                },
            );
        }
        fs::write(
            root.join("config.json"),
            serde_json::to_vec(&config).unwrap(),
        )
        .unwrap();
        let child = Command::new(std::env::current_exe().unwrap())
            .args(["homelab_scheduler_child", "--nocapture"])
            .env("MINI_PROVIDER_SCHEDULER_CHILD", &root)
            .spawn()
            .unwrap();
        let mut fixture = Self { root, child };
        until(|| {
            assert!(
                fixture.child.try_wait().unwrap().is_none(),
                "scheduler child died"
            );
            scheduler::request(
                &fixture.socket(),
                &scheduler::Command::Inspect {
                    controller: "a".into(),
                    id: scheduler::digest(b"ready"),
                },
            )
            .is_err_and(|error| error.contains("unknown job"))
        });
        fixture
    }
    fn socket(&self) -> PathBuf {
        self.root.join("scheduler.sock")
    }
    fn state(&self, controller: &str, id: &str) -> sc::State {
        let mut state = None;
        until(|| {
            match scheduler::request(
                &self.socket(),
                &scheduler::Command::Inspect {
                    controller: controller.into(),
                    id: id.into(),
                },
            ) {
                Ok(job) => {
                    state = Some(job.state);
                    true
                }
                Err(error) if error.contains("unknown job") => false,
                Err(error) => panic!("scheduler inspect: {error}"),
            }
        });
        state.unwrap()
    }
    fn gateway(&self, name: &str) -> (GatewayEndpoint, Receiver<ProviderCommand>) {
        let private_dir = self.root.join(format!("gateway-{name}"));
        fs::create_dir(&private_dir).unwrap();
        fs::set_permissions(&private_dir, fs::Permissions::from_mode(0o700)).unwrap();
        let (tx, rx) = mpsc::sync_channel(4);
        let gateway = GatewayEndpoint::start(
            GatewayConfig {
                scheduled_homelab: true,
                bind: "127.0.0.1:0".parse().unwrap(),
                unix_socket: None,
                pinned_model: "operator-model".into(),
                private_dir,
                max_request_bytes: 16_384,
                max_response_bytes: 16_384,
                timeout: Duration::from_secs(5),
                max_input_tokens: Some(1024),
                max_output_tokens: Some(64),
            },
            tx,
        )
        .unwrap();
        gateway
            .control()
            .activate(
                Lease {
                    id: LeaseId {
                        prompt_operation_id: 1,
                        parent_generation: format!("parent-{name}"),
                    },
                    worker_token: TOKEN.into(),
                },
                Instant::now() + Duration::from_secs(30),
            )
            .unwrap();
        (gateway, rx)
    }
}
impl Drop for SchedulerFixture {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
        let _ = fs::remove_dir_all(&self.root);
    }
}

// Controller fixture fakes only Mini's signed reserve/outcome acknowledgements.
// It uses the real adapter to verify the exact body and dispatch the exact lease.
fn controller(
    socket: PathBuf,
    name: &'static str,
    commands: Receiver<ProviderCommand>,
    replay: bool,
    wait_only: bool,
) -> (Receiver<String>, JoinHandle<()>) {
    let config: sc::Config =
        serde_json::from_slice(&fs::read(socket.parent().unwrap().join("config.json")).unwrap())
            .unwrap();
    let allowed_endpoints = vec![config.backends[name].endpoint.clone()];
    let (ids, observed) = mpsc::channel();
    let handle = thread::spawn(move || {
        let mut placement: Option<crate::homelab::Placement> = None;
        let mut saved: Option<(Vec<u8>, Vec<u8>)> = None;
        let mut reserved = Vec::new();
        loop {
            match commands
                .recv_timeout(Duration::from_secs(10))
                .expect("controller command")
            {
                ProviderCommand::Prepare { request, reply } => {
                    if saved.is_some() {
                        reply.send(Ok(None)).unwrap();
                        continue;
                    }
                    let id = scheduler::digest(
                        format!("{name}:{}", scheduler::digest(&request.exact_body)).as_bytes(),
                    );
                    let plan = crate::homelab::Plan {
                        config: crate::homelab::Config {
                            socket: socket.clone(),
                            controller: name.into(),
                            domain: "test-domain".into(),
                            principal: format!("member-{name}"),
                            pool: format!("pool-{name}"),
                            backends: vec![name.into()],
                            queue_timeout_ms: 30_000,
                        },
                        request: sc::Request {
                            id: id.clone(),
                            request_digest: scheduler::digest(&request.exact_body),
                            model: request.model,
                            max_input: 1024,
                            max_output: 64,
                            tools: false,
                            allowed_endpoints: allowed_endpoints.clone(),
                            queue_deadline_ms: scheduler::service::now_ms() + 30_000,
                        },
                    };
                    reply.send(Ok(Some(plan))).unwrap();
                    ids.send(id).unwrap();
                    if wait_only {
                        break;
                    }
                }
                ProviderCommand::Reserve { request, reply } => {
                    if let Some((exact_request, exact_response)) = &saved {
                        assert!(
                            request.placement.is_none(),
                            "exact replay must bypass placement"
                        );
                        assert_eq!(&request.exact_body, exact_request);
                        reply
                            .send(Ok(ForwardPermit::Replay {
                                lease: request.lease,
                                exact_body: request.exact_body,
                                status: 200,
                                content_type: "application/json".into(),
                                exact_response: exact_response.clone(),
                            }))
                            .unwrap();
                        break;
                    }
                    let pinned = request
                        .placement
                        .expect("scheduled request carries placement");
                    pinned.verify(&request.exact_body).unwrap();
                    reserved = request.exact_body.clone();
                    let endpoint = pinned.endpoint.clone();
                    placement = Some(pinned);
                    reply
                        .send(Ok(ForwardPermit::Fresh {
                            attempt_id: 7,
                            lease: request.lease,
                            exact_body: request.exact_body,
                            route: Route {
                                endpoint,
                                bearer: None,
                            },
                        }))
                        .unwrap();
                }
                ProviderCommand::BeforeSend {
                    attempt_id, reply, ..
                } => {
                    assert_eq!(attempt_id, 7);
                    placement
                        .as_ref()
                        .unwrap()
                        .dispatch("fake-mini-attempt-7".into())
                        .unwrap();
                    reply.send(Ok(())).unwrap();
                }
                ProviderCommand::Outcome { outcome, reply, .. } => {
                    let received = if let ProviderOutcome::Received {
                        status, exact_body, ..
                    } = outcome
                    {
                        assert_eq!(status, 200);
                        saved = Some((reserved.clone(), exact_body));
                        true
                    } else {
                        assert!(matches!(outcome, ProviderOutcome::Uncertain { .. }));
                        false
                    };
                    reply.send(Ok(())).unwrap();
                    if !received {
                        break;
                    }
                }
                ProviderCommand::Delivery {
                    local_write_success,
                    reply,
                    ..
                } => {
                    assert!(local_write_success);
                    reply.send(Ok(())).unwrap();
                    if !replay {
                        break;
                    }
                }
            }
        }
    });
    (observed, handle)
}

fn worker(gateway: &GatewayEndpoint) -> JoinHandle<Vec<u8>> {
    let address = gateway.local_addr();
    thread::spawn(move || {
        let mut socket = TcpStream::connect(address).unwrap();
        socket
            .set_read_timeout(Some(Duration::from_secs(10)))
            .unwrap();
        write!(socket, "POST /v1/chat/completions HTTP/1.1\r\nAuthorization: Bearer {TOKEN}\r\nContent-Type: application/json\r\nContent-Length: {}\r\n\r\n", BODY.len()).unwrap();
        socket.write_all(BODY).unwrap();
        let mut response = Vec::new();
        match socket.read_to_end(&mut response) {
            Ok(_) => {}
            Err(error) if error.kind() == io::ErrorKind::ConnectionReset => {}
            Err(error) => panic!("worker read: {error}"),
        }
        response
    })
}

fn upstream(
    listener: TcpListener,
    response: Option<&'static [u8]>,
) -> (Receiver<()>, Sender<()>, JoinHandle<()>) {
    let (reached, seen) = mpsc::channel();
    let (release, released) = mpsc::channel();
    let handle = thread::spawn(move || {
        listener.set_nonblocking(true).unwrap();
        let mut accepted = None;
        until(|| match listener.accept() {
            Ok((socket, _)) => {
                accepted = Some(socket);
                true
            }
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => false,
            Err(error) => panic!("upstream accept: {error}"),
        });
        let mut stream = GatewayStream::Tcp(accepted.unwrap());
        stream
            .set_read_timeout(Some(Duration::from_secs(5)))
            .unwrap();
        // This is the upstream HTTP peer, so no worker gateway bearer belongs
        // here. Read ordinary Content-Length HTTP independently of read_request.
        let mut bytes = Vec::new();
        let header_end = loop {
            let mut byte = [0u8; 1];
            stream.read_exact(&mut byte).unwrap();
            bytes.push(byte[0]);
            assert!(bytes.len() <= 16_384);
            if bytes.ends_with(b"\r\n\r\n") {
                break bytes.len();
            }
        };
        let header = std::str::from_utf8(&bytes[..header_end]).unwrap();
        assert!(header.starts_with("POST /v1/chat/completions HTTP/1.1\r\n"));
        assert!(!header.to_ascii_lowercase().contains("authorization:"));
        let length: usize = header
            .lines()
            .find_map(|line| {
                line.split_once(":")
                    .filter(|(key, _)| key.eq_ignore_ascii_case("content-length"))
                    .map(|(_, value)| value.trim().parse().unwrap())
            })
            .unwrap();
        assert!(length <= 16_384);
        let mut body = vec![0; length];
        stream.read_exact(&mut body).unwrap();
        let json: Value = serde_json::from_slice(&body).unwrap();
        assert_eq!(json["max_tokens"], 64);
        assert_eq!(json["model"], "operator-model");
        reached.send(()).unwrap();
        released.recv_timeout(Duration::from_secs(10)).unwrap();
        if let Some(body) = response {
            write_http(&mut stream, 200, "application/json", body).unwrap();
        }
    });
    (seen, release, handle)
}

#[test]
fn homelab_gateways_share_capacity_and_exact_replay_bypasses_queue() {
    let a_server = TcpListener::bind("127.0.0.1:0").unwrap();
    let b_server = TcpListener::bind("127.0.0.1:0").unwrap();
    let scheduler = SchedulerFixture::start(
        a_server.local_addr().unwrap(),
        b_server.local_addr().unwrap(),
    );
    let (a_seen, a_release, a_upstream) = upstream(a_server, Some(br#"{"id":"first-provider"}"#));
    let (b_seen, b_release, b_upstream) = upstream(b_server, Some(br#"{"id":"second-provider"}"#));
    let (a, a_commands) = scheduler.gateway("a");
    let (b, b_commands) = scheduler.gateway("b");
    let (a_ids, a_controller) = controller(scheduler.socket(), "a", a_commands, true, false);
    let (b_ids, b_controller) = controller(scheduler.socket(), "b", b_commands, false, false);
    let a_worker = worker(&a);
    let a_id = a_ids.recv_timeout(Duration::from_secs(5)).unwrap();
    a_seen.recv_timeout(Duration::from_secs(5)).unwrap();
    let b_worker = worker(&b);
    let b_id = b_ids.recv_timeout(Duration::from_secs(5)).unwrap();
    until(|| matches!(scheduler.state("b", &b_id), sc::State::Queued));
    assert!(matches!(
        scheduler.state("a", &a_id),
        sc::State::Dispatched { .. }
    ));
    assert!(matches!(b_seen.try_recv(), Err(mpsc::TryRecvError::Empty)));
    a_release.send(()).unwrap();
    assert!(String::from_utf8_lossy(&a_worker.join().unwrap()).contains("first-provider"));
    b_seen.recv_timeout(Duration::from_secs(5)).unwrap();
    assert!(matches!(
        scheduler.state("b", &b_id),
        sc::State::Dispatched { .. }
    ));
    until(|| !a.control.shared.active_request.load(Ordering::SeqCst));
    // B still holds the only slot. A's exact replay must nevertheless finish
    // without acquiring a new scheduler job or reaching an upstream again.
    assert!(String::from_utf8_lossy(&worker(&a).join().unwrap()).contains("first-provider"));
    assert!(matches!(
        scheduler.state("b", &b_id),
        sc::State::Dispatched { .. }
    ));
    b_release.send(()).unwrap();
    assert!(String::from_utf8_lossy(&b_worker.join().unwrap()).contains("second-provider"));
    a_upstream.join().unwrap();
    b_upstream.join().unwrap();
    a_controller.join().unwrap();
    b_controller.join().unwrap();
    assert!(matches!(
        scheduler.state("a", &a_id),
        sc::State::Terminal {
            outcome: sc::Outcome::Ended,
            ..
        }
    ));
    assert!(matches!(
        scheduler.state("b", &b_id),
        sc::State::Terminal {
            outcome: sc::Outcome::Ended,
            ..
        }
    ));
}

#[test]
fn homelab_uncertain_send_keeps_capacity_and_stopped_wait_never_reaches_upstream() {
    let a_server = TcpListener::bind("127.0.0.1:0").unwrap();
    let b_server = TcpListener::bind("127.0.0.1:0").unwrap();
    b_server.set_nonblocking(true).unwrap();
    let scheduler = SchedulerFixture::start(
        a_server.local_addr().unwrap(),
        b_server.local_addr().unwrap(),
    );
    let (a_seen, a_release, a_upstream) = upstream(a_server, None);
    let (a, a_commands) = scheduler.gateway("a");
    let (b, b_commands) = scheduler.gateway("b");
    let (a_ids, a_controller) = controller(scheduler.socket(), "a", a_commands, false, false);
    let (b_ids, b_controller) = controller(scheduler.socket(), "b", b_commands, false, true);
    let a_worker = worker(&a);
    let a_id = a_ids.recv_timeout(Duration::from_secs(5)).unwrap();
    a_seen.recv_timeout(Duration::from_secs(5)).unwrap();
    a_release.send(()).unwrap();
    assert!(String::from_utf8_lossy(&a_worker.join().unwrap()).contains("502"));
    assert!(matches!(
        scheduler.state("a", &a_id),
        sc::State::Uncertain { .. }
    ));
    let b_worker = worker(&b);
    let b_id = b_ids.recv_timeout(Duration::from_secs(5)).unwrap();
    until(|| matches!(scheduler.state("b", &b_id), sc::State::Queued));
    b.control().revoke();
    b_worker.join().unwrap();
    until(|| {
        matches!(
            scheduler.state("b", &b_id),
            sc::State::Terminal {
                outcome: sc::Outcome::Cancelled,
                ..
            }
        )
    });
    assert!(matches!(b_server.accept(), Err(error) if error.kind() == io::ErrorKind::WouldBlock));
    assert!(matches!(
        scheduler.state("a", &a_id),
        sc::State::Uncertain { .. }
    ));
    a_upstream.join().unwrap();
    a_controller.join().unwrap();
    b_controller.join().unwrap();
    until(|| !b.control.shared.active_request.load(Ordering::SeqCst));
}
