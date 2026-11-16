//! The broker over real Unix sockets with real peer credentials.
//!
//! Sudo-free shape: the broker and its clients run as this one test uid, so the
//! config says `singleAccount` and names this uid in exactly the roles a test
//! needs; every other row is refused by the same code a split box runs. The
//! one row that needs a second uid (`two_uid_*`) is #[ignore]: it wants
//! `sudo -n setpriv` and MINI_TEST_FOREIGN_UID (scripts/check-rust-tests.sh
//! names it in its sudo-only section).
use ed25519_dalek::Signer;
use mini_keys::client::{self, Broker};
use mini_keys::server::{self, Config};
use mini_keys::{peer, wire};
use serde_json::{json, Value};
use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpListener;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::UnixListener;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

static N: AtomicUsize = AtomicUsize::new(0);
const SECRET: &str = "sk-member-secret-0123456789abcdef";
const POOL_SECRET: &str = "sk-pool-secret-fedcba9876543210";
const BOT_TOKEN: &str = "bot.token-0123456789_ABCDEF";

fn private_dir(path: &Path) {
    std::fs::create_dir_all(path).unwrap();
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o700)).unwrap();
}

fn write_mode(path: &Path, bytes: &[u8], mode: u32) {
    std::fs::write(path, bytes).unwrap();
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(mode)).unwrap();
}

/// One HTTP/1.1 request read off a TCP stream: (request line + headers, body).
fn http_request(stream: &mut std::net::TcpStream) -> (String, Vec<u8>) {
    let mut reader = BufReader::new(stream.try_clone().unwrap());
    let mut head = String::new();
    let mut length = 0usize;
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line).unwrap() == 0 || line == "\r\n" {
            break;
        }
        if let Some(v) = line.to_ascii_lowercase().strip_prefix("content-length:") {
            length = v.trim().parse().unwrap();
        }
        head.push_str(&line);
    }
    let mut body = vec![0; length];
    reader.read_exact(&mut body).unwrap();
    (head, body)
}

/// A fake upstream: answers every request with `reply(head, body)`; records the heads.
fn upstream(reply: impl Fn(&str, &[u8]) -> (u16, String, Duration) + Send + 'static) -> (String, Arc<Mutex<Vec<(String, Vec<u8>)>>>) {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let base = format!("http://{}", listener.local_addr().unwrap());
    let seen = Arc::new(Mutex::new(Vec::new()));
    let log = seen.clone();
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let mut stream = stream.unwrap();
            let (head, body) = http_request(&mut stream);
            log.lock().unwrap().push((head.clone(), body.clone()));
            let (status, text, delay) = reply(&head, &body);
            std::thread::sleep(delay);
            let _ = write!(stream, "HTTP/1.1 {status} OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{text}", text.len());
        }
    });
    (base, seen)
}

/// The Store's public socket, as far as the broker asks it: operation 144.
fn fake_store(path: &Path, view: Arc<Mutex<Value>>) {
    let listener = UnixListener::bind(path).unwrap();
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let mut stream = stream.unwrap();
            let end = Instant::now() + Duration::from_secs(5);
            let frame = wire::read_frame(&mut stream, 1 << 20, end).unwrap();
            assert_eq!(frame[0], 2, "a pinned envelope");
            assert_eq!(*frame.iter().rev().find(|_| true).unwrap() as char, '}');
            let mut reply = vec![144u8];
            reply.extend_from_slice(&serde_json::to_vec(&*view.lock().unwrap()).unwrap());
            wire::write_frame(&mut stream, &reply, end).unwrap();
        }
    });
}

struct Fixture {
    dir: PathBuf,
    config: PathBuf,
    socket: PathBuf,
    audit: PathBuf,
    key: PathBuf,
    root: PathBuf,
    mirror: PathBuf,
    view: Arc<Mutex<Value>>,
    member: ed25519_dalek::SigningKey,
    provider: (String, Arc<Mutex<Vec<(String, Vec<u8>)>>>),
    discord: (String, Arc<Mutex<Vec<(String, Vec<u8>)>>>),
}

impl Fixture {
    fn new(tag: &str) -> Self {
        let dir = std::env::temp_dir()
            .join(format!("mk-{tag}-{}-{}", std::process::id(), N.fetch_add(1, Ordering::SeqCst)));
        let _ = std::fs::remove_dir_all(&dir);
        private_dir(&dir);
        let dir = dir.canonicalize().unwrap();
        for sub in ["etc", "keys", "run", "state", "credentials"] {
            private_dir(&dir.join(sub));
        }
        let key = dir.join("keys/credentials.key");
        write_mode(&key, &[7u8; 32], 0o600);
        write_mode(&dir.join("etc/host"), b"host image bytes", 0o755);
        write_mode(&dir.join("etc/pinned-config.json"), br#"{"deployment":"test"}"#, 0o644);
        let provider = upstream(|head, body| {
            if String::from_utf8_lossy(body).contains("echo-the-bearer") {
                let auth = head.lines().find(|l| l.to_ascii_lowercase().starts_with("authorization:")).unwrap_or("").to_owned();
                return (200, json!({"echo":auth}).to_string(), Duration::ZERO);
            }
            if String::from_utf8_lossy(body).contains("slow") {
                return (200, "{}".into(), Duration::from_secs(8));
            }
            (200, json!({"choices":[{"message":{"content":"hello"}}]}).to_string(), Duration::ZERO)
        });
        let discord = upstream(|head, _| {
            if head.starts_with("GET") {
                (200, json!([{"id":"1001","content":"hi","author":{"id":"77","username":"alice"}}]).to_string(), Duration::ZERO)
            } else {
                (200, json!({"id":"2001"}).to_string(), Duration::ZERO)
            }
        });
        let table = json!({"type":"mini-provider-table-v2","providers":[
            {"name":"openrouter","endpoint":format!("{}/v1/chat/completions",provider.0),"kind":"openai-compatible","models":["m1"],"credential":"user"},
            {"name":"poolrow","endpoint":format!("{}/v1/chat/completions",provider.0),"kind":"openai-compatible","models":["m1"],"credential":"pool","caps":{"perCall":"256","perDay":"2","ceilingMicroUsd":"40000000","callMicroUsd":"5000"}},
            {"name":"homelab","endpoint":format!("{}/v1/chat/completions",provider.0),"kind":"openai-compatible","models":["m1"],"credential":"homelab"}]});
        write_mode(&dir.join("etc/providers.json"), table.to_string().as_bytes(), 0o644);
        let mirror = dir.join("keys/discord-mirror.json");
        write_mode(&mirror, json!({"type":"mini-discord-mirror-secrets-v1","webhookUrl":format!("{}/webhook/1/tok",discord.0),
            "channelUrl":format!("{}/channels/9/messages",discord.0),"botToken":BOT_TOKEN}).to_string().as_bytes(), 0o600);
        let member = ed25519_dalek::SigningKey::from_bytes(&[41; 32]);
        // The Host's reply shape today: no publicKey, no height (the Lean ask adds both).
        let view = Arc::new(Mutex::new(json!({"type":"subject-key-status-v1","subject":"20","keyEpoch":"3","isCurrent":true,"currentRevoked":false})));
        fake_store(&dir.join("run/public.sock"), view.clone());
        Fixture {
            config: dir.join("etc/broker.json"),
            socket: dir.join("run/broker.sock"),
            audit: dir.join("state/audit.jsonl"),
            root: dir.join("credentials"),
            key,
            mirror,
            view,
            member,
            provider,
            discord,
            dir,
        }
    }

    fn config_json(&self, peers: Value, single: bool) -> Value {
        let mut v = json!({"type":"mini-keys-broker-v1","socket":self.socket,"audit":self.audit,"spool":self.dir.join("state/spool"),
            "peers":peers,
            "credentials":{"host":self.dir.join("etc/host"),"hostSha256":server::native::sha256_hex(b"host image bytes"),
                "hostConfig":self.dir.join("etc/pinned-config.json"),
                "publicSocket":self.dir.join("run/public.sock"),"publicSocketUid":peer::euid(),"providers":self.dir.join("etc/providers.json"),
                "root":self.root,"key":self.key},
            "discord":{"mirror":self.mirror}});
        if single {
            v["singleAccount"] = json!(true);
        }
        v
    }

    fn all_roles(&self) -> Value {
        let me = peer::euid();
        json!([{"role":"member","gids":[peer::egid()]},{"role":"provider","uids":[me]},{"role":"discord","uids":[me]},{"role":"operator","uids":[me]}])
    }

    fn start(&self, config: Value) -> Result<Broker, String> {
        write_mode(&self.config, config.to_string().as_bytes(), 0o644);
        let config = Config::load(&self.config, peer::euid())?;
        let (broker, listener) = server::Broker::start(config)?;
        std::thread::spawn(move || broker.serve(listener));
        Ok(Broker::new(&self.socket, peer::euid()))
    }

    fn owner(&self) -> Value {
        json!({"subject":"20","publicKey":wire::hex(self.member.verifying_key().as_bytes())})
    }

    fn audit_text(&self) -> String {
        std::thread::sleep(Duration::from_millis(50));
        std::fs::read_to_string(&self.audit).unwrap()
    }

    /// The member side of the exchange (resource-client's, in miniature).
    fn member_action(&self, broker: &Broker, action: Value) -> Value {
        let end = Instant::now() + Duration::from_secs(10);
        let mut s = broker.connect(end).unwrap();
        wire::send(&mut s, &json!({"op":"member-action"}), end).unwrap();
        let challenge = wire::recv(&mut s, wire::MEMBER_FRAME, end).unwrap();
        if challenge.get("refused").is_some() || challenge["type"] == server::member::REFUSED {
            return challenge;
        }
        assert_eq!(challenge["type"], server::member::CHALLENGE);
        assert_eq!(challenge["configSha256"], server::native::sha256_hex(br#"{"deployment":"test"}"#));
        let mut request = json!({"challenge":challenge,"owner":self.owner(),"action":action});
        let sig = self.member.sign(&server::member::signing_bytes(&request).unwrap());
        request["signature"] = json!(wire::hex(&sig.to_bytes()));
        wire::send(&mut s, &request, end).unwrap();
        wire::recv(&mut s, wire::MEMBER_FRAME, end).unwrap()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

fn body_sha(body: &[u8]) -> String {
    server::native::sha256_hex(body)
}

#[test]
fn start_refuses_every_unsafe_custody_by_name() {
    let f = Fixture::new("custody");
    let me = peer::euid();
    // Split shape: a peer rule naming the broker's own account.
    let err = f.start(f.config_json(json!([{"role":"provider","uids":[me]}]), false)).unwrap_err();
    assert!(err.contains("names the broker's own uid"), "{err}");
    // A readable seal key.
    std::fs::set_permissions(&f.key, std::fs::Permissions::from_mode(0o640)).unwrap();
    let err = f.start(f.config_json(f.all_roles(), true)).unwrap_err();
    assert!(err.contains("the seal key"), "{err}");
    std::fs::set_permissions(&f.key, std::fs::Permissions::from_mode(0o600)).unwrap();
    // Readable Discord secrets.
    std::fs::set_permissions(&f.mirror, std::fs::Permissions::from_mode(0o604)).unwrap();
    let err = f.start(f.config_json(f.all_roles(), true)).unwrap_err();
    assert!(err.contains("Discord mirror secrets"), "{err}");
    std::fs::set_permissions(&f.mirror, std::fs::Permissions::from_mode(0o600)).unwrap();
    // A config another account may write.
    write_mode(&f.config, f.config_json(f.all_roles(), true).to_string().as_bytes(), 0o666);
    assert!(Config::load(&f.config, me).unwrap_err().contains("writable by no other account"));
    // Something else at the socket path.
    write_mode(&f.socket, b"not a socket", 0o600);
    let err = f.start(f.config_json(f.all_roles(), true)).unwrap_err();
    assert!(err.contains("is not this broker's socket"), "{err}");
    std::fs::remove_file(&f.socket).unwrap();
    // Unknown fields, and a non-member role admitted by group.
    let mut extra = f.config_json(f.all_roles(), true);
    extra["bearer"] = json!("x");
    assert!(Config::parse(extra.to_string().as_bytes(), me).is_err());
    assert!(Config::parse(f.config_json(json!([{"role":"provider","gids":[1]}]), true).to_string().as_bytes(), me)
        .unwrap_err()
        .contains("only members are admitted by group"));
}

#[test]
fn a_peer_without_a_role_and_an_op_outside_its_role_are_refused_by_name() {
    let f = Fixture::new("roles");
    let me = peer::euid();
    // Only a uid that is not this one: this test process holds no role.
    let b = f.start(f.config_json(json!([{"role":"provider","uids":[me.wrapping_add(7)]}]), true)).unwrap();
    assert_eq!(client::hello(&b).unwrap_err().code, "peer-not-allowed");
    let f2 = Fixture::new("roles2");
    let b2 = f2.start(f2.config_json(json!([{"role":"member","gids":[peer::egid()]}]), true)).unwrap();
    let hello = client::hello(&b2).unwrap();
    assert_eq!(hello["roles"], json!(["member"]));
    assert_eq!(hello["singleAccount"], true);
    let r = b2.call(&json!({"op":"provider-authorize","kind":"pool","provider":"poolrow","runner":"9","maxTokens":8,"bodySha256":"0".repeat(64)}), Duration::from_secs(5)).unwrap_err();
    assert_eq!(r.code, "op-not-granted");
    assert_eq!(b2.call(&json!({"op":"pool","action":"ls"}), Duration::from_secs(5)).unwrap_err().code, "op-not-granted");
    assert_eq!(b2.call(&json!({"op":"discord-read","limit":1}), Duration::from_secs(5)).unwrap_err().code, "op-not-granted");
    assert_eq!(b2.call(&json!({"op":"read-the-seal-key"}), Duration::from_secs(5)).unwrap_err().code, "op-unknown");
    let audit = f.audit_text();
    assert!(audit.contains("\"refused\":\"peer-not-allowed\""), "{audit}");
    let audit2 = f2.audit_text();
    assert!(audit2.contains("\"refused\":\"op-not-granted\"") && audit2.contains("\"refused\":\"op-unknown\""), "{audit2}");
}

#[test]
fn member_keys_are_sealed_by_the_broker_and_never_come_back() {
    let f = Fixture::new("member");
    let b = f.start(f.config_json(f.all_roles(), true)).unwrap();
    let set = f.member_action(&b, json!({"action":"set","provider":"openrouter","secret":SECRET}));
    assert_eq!(set["type"], server::member::RESULT, "{set}");
    assert_eq!(set["result"]["stored"], "sealed");
    assert_eq!(set["authentication"]["keyEpoch"], "3");
    let grant = f.member_action(&b, json!({"action":"grant","provider":"openrouter","runner":"9","perCall":"256","perDay":"1","notAfter":"100","model":"m1"}));
    assert_eq!(grant["result"]["grant"]["ownerEpoch"], "3", "{grant}");
    let ls = f.member_action(&b, json!({"action":"ls"}));
    assert_eq!(ls["result"]["credentials"][0]["provider"], "openrouter");
    let catalogue = f.member_action(&b, json!({"action":"providers"}));
    assert!(catalogue["result"]["custody"].as_str().unwrap().contains("mini-keys"));
    for v in [&set, &grant, &ls, &catalogue] {
        assert!(!v.to_string().contains(SECRET));
    }
    // On disk the key is sealed; the audit log names the action, never the value.
    let mut disk = Vec::new();
    for entry in walk(&f.root) {
        disk.extend(std::fs::read(entry).unwrap());
    }
    assert!(!disk.windows(SECRET.len()).any(|w| w == SECRET.as_bytes()));
    let audit = f.audit_text();
    assert!(!audit.contains(SECRET) && audit.contains("\"action\":\"set\""), "{audit}");
    // A key the Store says is revoked gets nothing.
    f.view.lock().unwrap()["currentRevoked"] = json!(true);
    let refused = f.member_action(&b, json!({"action":"ls"}));
    assert_eq!(refused["type"], server::member::REFUSED);
    assert!(f.audit_text().contains("\"refused\":\"owner-not-current\""));
}

fn walk(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    for e in std::fs::read_dir(dir).unwrap() {
        let p = e.unwrap().path();
        if p.is_dir() {
            out.extend(walk(&p));
        } else {
            out.push(p);
        }
    }
    out
}

fn forward(b: &Broker, ticket: &str, body: &[u8]) -> Result<Value, client::Refused> {
    b.call(&json!({"op":"provider-forward","ticket":ticket,"body":wire::hex(body),"timeoutMs":5000,"maxResponseBytes":65536}), Duration::from_secs(20))
}

#[test]
fn a_ticket_forwards_one_exact_body_with_the_bearer_the_caller_never_sees() {
    let f = Fixture::new("ticket");
    let b = f.start(f.config_json(f.all_roles(), true)).unwrap();
    f.member_action(&b, json!({"action":"set","provider":"openrouter","secret":SECRET}));
    f.member_action(&b, json!({"action":"grant","provider":"openrouter","runner":"9","perCall":"256","perDay":"2","notAfter":"100","model":"m1"}));
    let body = br#"{"model":"m1","max_tokens":64,"messages":[]}"#;
    let authorize = |body: &[u8], height: u64| {
        b.call(&json!({"op":"provider-authorize","kind":"user","provider":"openrouter","runner":"9","maxTokens":64,
            "bodySha256":body_sha(body),"owner":f.owner(),"model":"m1","height":height}), Duration::from_secs(10))
    };
    let t = authorize(body, 50).unwrap();
    assert_eq!(t["route"], "user:20");
    assert_eq!(t["ownerEpoch"], "3");
    assert!(!t.to_string().contains(SECRET));
    let ticket = t["ticket"].as_str().unwrap().to_owned();
    // Another body under this ticket: refused, and the ticket is spent.
    assert_eq!(forward(&b, &ticket, b"{\"other\":1}").unwrap_err().code, "ticket-body-mismatch");
    assert_eq!(forward(&b, &ticket, body).unwrap_err().code, "ticket-spent");
    let t = authorize(body, 50).unwrap();
    let r = forward(&b, t["ticket"].as_str().unwrap(), body).unwrap();
    assert_eq!(r["complete"], true);
    let response = String::from_utf8(wire::unhex(r["body"].as_str().unwrap()).unwrap()).unwrap();
    assert!(response.contains("hello"));
    assert!(!r.to_string().contains(SECRET));
    let seen = f.provider.1.lock().unwrap().clone();
    let (head, sent) = seen.last().unwrap();
    assert!(head.contains(&format!("Bearer {SECRET}")), "the upstream got the bearer");
    assert_eq!(sent.as_slice(), body, "and exactly the authorized body");
    // perDay 2 is spent: the third authorization refuses before any ticket.
    assert_eq!(authorize(body, 50).unwrap_err().code, "provider-refused:per-day-cap");
    // A grant past its height refuses.
    f.member_action(&b, json!({"action":"grant","provider":"openrouter","runner":"8","perCall":"256","perDay":"5","notAfter":"10","model":"m1"}));
    let late = b.call(&json!({"op":"provider-authorize","kind":"user","provider":"openrouter","runner":"8","maxTokens":64,
        "bodySha256":body_sha(body),"owner":f.owner(),"model":"m1","height":11}), Duration::from_secs(10)).unwrap_err();
    assert_eq!(late.code, "provider-refused:grant-expired");
    // The broker asks the Store itself: a revoked key gets no ticket, whatever the caller says.
    f.view.lock().unwrap()["currentRevoked"] = json!(true);
    let revoked = b.call(&json!({"op":"provider-authorize","kind":"user","provider":"openrouter","runner":"8","maxTokens":64,
        "bodySha256":body_sha(body),"owner":f.owner(),"model":"m1","height":5}), Duration::from_secs(10)).unwrap_err();
    assert_eq!(revoked.code, "provider-refused:owner-not-current");
    assert!(!f.audit_text().contains(SECRET));
}

/// B-F1: the controller states maxTokens 64 and model m1 at authorize; the
/// body it forwards asks for more. The grant, read against the body, refuses.
#[test]
fn the_forwarded_body_is_held_to_the_grant_whatever_the_controller_claimed() {
    let f = Fixture::new("claims");
    let b = f.start(f.config_json(f.all_roles(), true)).unwrap();
    f.member_action(&b, json!({"action":"set","provider":"openrouter","secret":SECRET}));
    f.member_action(&b, json!({"action":"grant","provider":"openrouter","runner":"9","perCall":"256","perDay":"9","notAfter":"100","model":"m1"}));
    let claimed = |body: &[u8]| {
        b.call(&json!({"op":"provider-authorize","kind":"user","provider":"openrouter","runner":"9","maxTokens":64,
            "bodySha256":body_sha(body),"owner":f.owner(),"model":"m1","height":5}), Duration::from_secs(10)).unwrap()["ticket"].as_str().unwrap().to_owned()
    };
    for body in [&br#"{"model":"m1","max_tokens":100000,"messages":[]}"#[..], br#"{"model":"expensive","max_tokens":8}"#,
        br#"{"model":"m1","max_tokens":8,"n":50}"#, br#"{"model":"m1","max_tokens":100000,"max_tokens":8}"#] {
        let t = claimed(body);
        assert_eq!(forward(&b, &t, body).unwrap_err().code, "provider-refused:body-exceeds-grant", "{}", String::from_utf8_lossy(body));
    }
    assert!(f.provider.1.lock().unwrap().is_empty(), "nothing reached the provider");
}

/// B-F2: a lost authorize reply and a lost forward reply are both recovered by
/// an exact retry, across a broker restart, with one count and one provider call.
#[test]
fn an_exact_retry_recovers_a_lost_reply_without_a_second_count_or_call() {
    let f = Fixture::new("retry");
    let b = f.start(f.config_json(f.all_roles(), true)).unwrap();
    b.call(&json!({"op":"pool","action":"set","provider":"poolrow","secret":POOL_SECRET}), Duration::from_secs(10)).unwrap();
    let body = br#"{"model":"m1","max_tokens":64,"messages":[]}"#;
    let authorize = |b: &Broker| b.call(&json!({"op":"provider-authorize","kind":"pool","provider":"poolrow","runner":"9","maxTokens":64,"bodySha256":body_sha(body)}), Duration::from_secs(10));
    let first = authorize(&b).unwrap();
    let again = authorize(&b).unwrap();
    assert_eq!(first["ticket"], again["ticket"], "the same live ticket, counted once");
    let ticket = first["ticket"].as_str().unwrap().to_owned();
    let answer = forward(&b, &ticket, body).unwrap();
    // The broker restarts; the reply was lost; the controller presents the ticket again.
    let b = f.start(f.config_json(f.all_roles(), true)).unwrap();
    let replay = forward(&b, &ticket, body).unwrap();
    assert_eq!(replay["replayed"], true);
    assert_eq!(replay["body"], answer["body"]);
    assert_eq!(f.provider.1.lock().unwrap().len(), 1, "one provider call");
    // perDay 2: only one call was counted, so one more fits; then the cap.
    let other = br#"{"model":"m1","max_tokens":8,"messages":[]}"#;
    let t = b.call(&json!({"op":"provider-authorize","kind":"pool","provider":"poolrow","runner":"9","maxTokens":8,"bodySha256":body_sha(other)}), Duration::from_secs(10)).unwrap();
    assert_ne!(t["ticket"], first["ticket"]);
    let third = br#"{"model":"m1","max_tokens":9,"messages":[]}"#;
    assert_eq!(b.call(&json!({"op":"provider-authorize","kind":"pool","provider":"poolrow","runner":"9","maxTokens":9,"bodySha256":body_sha(third)}), Duration::from_secs(10)).unwrap_err().code, "provider-refused:per-day-cap");
    let ls = b.call(&json!({"op":"pool","action":"ls"}), Duration::from_secs(10)).unwrap();
    assert_eq!(ls["result"]["credentials"][0]["spentMicroUsd"], 10000, "two calls charged at the row's worst case");
}

/// B-F4: an operation-144 answer from any account but the pinned one is refused.
#[test]
fn an_owner_status_from_an_unpinned_account_or_about_another_key_is_refused() {
    let f = Fixture::new("pin144");
    let mut cfg = f.config_json(f.all_roles(), true);
    cfg["credentials"]["publicSocketUid"] = json!(peer::euid().wrapping_add(1));
    let b = f.start(cfg).unwrap();
    let r = f.member_action(&b, json!({"action":"ls"}));
    assert_eq!(r["type"], server::member::REFUSED);
    assert!(r["error"].as_str().unwrap().contains("not the pinned public-socket uid"), "{r}");
    let f = Fixture::new("key144");
    let b = f.start(f.config_json(f.all_roles(), true)).unwrap();
    f.view.lock().unwrap()["publicKey"] = json!("cd".repeat(32));
    assert_eq!(f.member_action(&b, json!({"action":"ls"}))["error"], "owner-not-current");
    f.view.lock().unwrap()["publicKey"] = json!(wire::hex(f.member.verifying_key().as_bytes()));
    assert_eq!(f.member_action(&b, json!({"action":"ls"}))["type"], server::member::RESULT);
}

/// B-F3: a session account gets four connections and a small first frame;
/// the Host image is pinned by digest, and a swapped image refuses.
#[test]
fn a_member_account_cannot_take_the_slots_or_force_a_large_frame_and_the_host_is_pinned() {
    let f = Fixture::new("slots");
    let b = f.start(f.config_json(json!([{"role":"member","gids":[peer::egid()]}]), true)).unwrap();
    let end = Instant::now() + Duration::from_secs(5);
    let held: Vec<_> = (0..4).map(|_| b.connect(end).unwrap()).collect();
    std::thread::sleep(Duration::from_millis(100));
    let mut fifth = b.connect(end).unwrap();
    assert_eq!(wire::recv(&mut fifth, 4096, end).unwrap()["refused"], "busy");
    drop(held);
    std::thread::sleep(Duration::from_millis(100));
    let mut s = b.connect(end).unwrap();
    wire::write_frame(&mut s, &vec![b' '; 64 * 1024], end).unwrap_or(());
    let r = wire::recv(&mut s, 4096, end).unwrap();
    assert_eq!(r["refused"], "bad-request");
    assert!(r["detail"].as_str().unwrap().contains("exceeds bound"), "{r}");
    drop(s);
    // The image changes under the broker: the next member action refuses by name.
    write_mode(&f.dir.join("etc/host"), b"another host image", 0o755);
    let r = f.member_action(&b, json!({"action":"ls"}));
    assert!(r["error"].as_str().unwrap_or("").contains("not the pinned candidate image"), "{r}");
    // And a broker whose pin is not the image does not start.
    let mut cfg = f.config_json(f.all_roles(), true);
    cfg["credentials"]["hostSha256"] = json!("0".repeat(64));
    assert!(f.start(cfg).unwrap_err().contains("not the pinned candidate image"));
}

/// B-F7: an operation the audit log cannot record does not run.
///
/// RLIMIT_FSIZE is process-wide and the other tests in this binary write files on
/// their own threads, so the limited part runs in a child copy of this binary; putting
/// the old limit back after the call would not do, since those writes land in the window.
#[test]
fn an_operation_that_cannot_be_audited_is_refused_and_has_no_effect() {
    const NAME: &str = "an_operation_that_cannot_be_audited_is_refused_and_has_no_effect";
    const CHILD: &str = "MINI_TEST_AUDIT_LIMITED_CHILD";
    let args = ["--exact", NAME, "--nocapture", "--test-threads=1"];
    // An ambient marker alone must never put the parallel test harness under the limit.
    // Only our direct child, running exactly this one test, may change process-wide state.
    let is_child = std::env::var(CHILD).ok() == Some(unsafe { libc::getppid() }.to_string())
        && std::env::args().skip(1).eq(args.iter().copied());
    if !is_child {
        let limit = || unsafe {
            let mut value = std::mem::zeroed::<libc::rlimit>();
            assert_eq!(libc::getrlimit(libc::RLIMIT_FSIZE, &mut value), 0);
            (value.rlim_cur, value.rlim_max)
        };
        let signal_handler = || unsafe {
            let mut action = std::mem::zeroed::<libc::sigaction>();
            assert_eq!(libc::sigaction(libc::SIGXFSZ, std::ptr::null(), &mut action), 0);
            action.sa_sigaction
        };
        let before_limit = limit();
        let before_handler = signal_handler();
        let out = std::process::Command::new(std::env::current_exe().unwrap())
            .args(args)
            .env(CHILD, std::process::id().to_string())
            .output()
            .unwrap();
        assert_eq!(limit(), before_limit, "the child's file limit leaked into the parent");
        assert_eq!(signal_handler(), before_handler, "the child's signal handler leaked into the parent");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let text = format!("stdout:\n{stdout}\nstderr:\n{}", String::from_utf8_lossy(&out.stderr));
        assert!(out.status.success(), "limited child failed ({}):\n{text}", out.status);
        assert!(stdout.lines().any(|line| line == format!("test {NAME} ... ok"))
            && stdout.contains("test result: ok. 1 passed"), "limited child did not pass the named test:\n{text}");
        return;
    }
    let f = Fixture::new("audit");
    let b = f.start(f.config_json(f.all_roles(), true)).unwrap();
    // Every later write by this process (the broker's audit appends among them) fails EFBIG.
    unsafe {
        assert_ne!(libc::signal(libc::SIGXFSZ, libc::SIG_IGN), libc::SIG_ERR);
        let size = std::fs::metadata(&f.audit).unwrap().len() as libc::rlim_t;
        let mut limit = std::mem::zeroed::<libc::rlimit>();
        assert_eq!(libc::getrlimit(libc::RLIMIT_FSIZE, &mut limit), 0);
        limit.rlim_cur = size;
        assert_eq!(libc::setrlimit(libc::RLIMIT_FSIZE, &limit), 0);
    }
    let r = b.call(&json!({"op":"pool","action":"set","provider":"poolrow","secret":POOL_SECRET}), Duration::from_secs(10)).unwrap_err();
    assert_eq!(r.code, "audit-unavailable", "{r}");
    assert!(!f.root.join("_pool/poolrow.key").exists(), "nothing was sealed");
}

#[test]
fn single_account_is_a_test_shape_a_root_owned_config_cannot_select() {
    let f = Fixture::new("single");
    let err = Config::parse(f.config_json(f.all_roles(), true).to_string().as_bytes(), 0).unwrap_err();
    assert!(err.contains("test shape"), "{err}");
}

#[test]
fn an_upstream_that_echoes_the_bearer_is_withheld_and_a_kind_mismatch_refuses() {
    let f = Fixture::new("echo");
    let b = f.start(f.config_json(f.all_roles(), true)).unwrap();
    let pool = b.call(&json!({"op":"pool","action":"set","provider":"poolrow","secret":POOL_SECRET}), Duration::from_secs(10)).unwrap();
    assert_eq!(pool["result"]["stored"], "sealed");
    assert_eq!(b.call(&json!({"op":"pool","action":"set","provider":"openrouter","secret":POOL_SECRET}), Duration::from_secs(10)).unwrap_err().code, "provider-kind-mismatch");
    let body = br#"{"model":"m1","max_tokens":64,"echo-the-bearer":true}"#;
    let t = b.call(&json!({"op":"provider-authorize","kind":"pool","provider":"poolrow","runner":"9","maxTokens":64,"bodySha256":body_sha(body)}), Duration::from_secs(10)).unwrap();
    let r = forward(&b, t["ticket"].as_str().unwrap(), body).unwrap();
    assert_eq!(r["withheld"], true);
    assert!(!r.to_string().contains(POOL_SECRET));
    // Pool caps: perCall 256.
    let big = b.call(&json!({"op":"provider-authorize","kind":"pool","provider":"poolrow","runner":"9","maxTokens":999,"bodySha256":body_sha(body)}), Duration::from_secs(10)).unwrap_err();
    assert_eq!(big.code, "provider-refused:per-call-cap");
    // A user row cannot be authorized as pool; a homelab row needs no ticket and carries no bearer.
    assert_eq!(b.call(&json!({"op":"provider-authorize","kind":"pool","provider":"openrouter","runner":"9","maxTokens":8,"bodySha256":body_sha(body)}), Duration::from_secs(10)).unwrap_err().code, "provider-kind-mismatch");
    let home = b.call(&json!({"op":"provider-forward","homelab":"homelab","body":wire::hex(b"{\"max_tokens\":1}"),"timeoutMs":5000,"maxResponseBytes":65536}), Duration::from_secs(10)).unwrap();
    assert_eq!(home["complete"], true);
    let seen = f.provider.1.lock().unwrap().clone();
    assert!(!seen.last().unwrap().0.to_ascii_lowercase().contains("authorization"));
    assert_eq!(b.call(&json!({"op":"provider-forward","homelab":"poolrow","body":"00","timeoutMs":5000,"maxResponseBytes":10}), Duration::from_secs(10)).unwrap_err().code, "provider-kind-mismatch");
}

#[test]
fn a_caller_that_hangs_up_stops_the_provider_call() {
    let f = Fixture::new("hangup");
    let b = f.start(f.config_json(f.all_roles(), true)).unwrap();
    let body = br#"{"slow":true}"#;
    let end = Instant::now() + Duration::from_secs(10);
    let mut s = b.connect(end).unwrap();
    wire::send(&mut s, &json!({"op":"provider-forward","homelab":"homelab","body":wire::hex(body),"timeoutMs":30000,"maxResponseBytes":1024}), end).unwrap();
    std::thread::sleep(Duration::from_millis(400));
    let started = Instant::now();
    s.shutdown(std::net::Shutdown::Both).unwrap();
    drop(s);
    loop {
        if f.audit_text().contains("\"refused\":\"caller-gone\"") {
            break;
        }
        assert!(started.elapsed() < Duration::from_secs(4), "the broker kept calling for a caller that left");
        std::thread::sleep(Duration::from_millis(100));
    }
}

#[test]
fn the_mirror_posts_and_reads_its_one_channel_without_holding_the_token() {
    let f = Fixture::new("discord");
    let b = f.start(f.config_json(f.all_roles(), true)).unwrap();
    let posted = b.call(&json!({"op":"discord-post","body":{"content":"alice: hi"}}), Duration::from_secs(10)).unwrap();
    assert_eq!(posted["status"], 200);
    let read = b.call(&json!({"op":"discord-read","before":"1500","limit":50}), Duration::from_secs(10)).unwrap();
    assert!(read["body"].as_str().unwrap().contains("alice"));
    for v in [&posted, &read] {
        assert!(!v.to_string().contains(BOT_TOKEN) && !v.to_string().contains("/webhook/1/tok"));
    }
    let seen = f.discord.1.lock().unwrap().clone();
    assert!(seen[0].0.starts_with("POST /webhook/1/tok?wait=true"), "{}", seen[0].0);
    assert_eq!(seen[0].1, br#"{"content":"alice: hi"}"#);
    assert!(seen[1].0.starts_with("GET /channels/9/messages?before=1500&limit=50"), "{}", seen[1].0);
    assert!(seen[1].0.contains(&format!("Bot {BOT_TOKEN}")));
    assert_eq!(b.call(&json!({"op":"discord-read","limit":51}), Duration::from_secs(5)).unwrap_err().code, "bad-request");
    assert_eq!(b.call(&json!({"op":"discord-post","body":{"content":"x"},"url":"https://evil"}), Duration::from_secs(5)).unwrap_err().code, "bad-request");
    assert!(!f.audit_text().contains(BOT_TOKEN));
}

/// Two real uids: the broker as this account, a client as
/// MINI_TEST_FOREIGN_UID through `sudo -n setpriv`. Not armed by default.
#[test]
#[ignore = "needs sudo -n setpriv and MINI_TEST_FOREIGN_UID; scripts/check-rust-tests.sh sudo-only section"]
fn two_uid_a_foreign_account_reaches_only_its_role_and_cannot_read_a_secret() {
    let foreign: u32 = std::env::var("MINI_TEST_FOREIGN_UID").expect("MINI_TEST_FOREIGN_UID").parse().unwrap();
    let f = Fixture::new("twouid");
    // A copy the foreign account can execute (the build tree may sit under a 0750 home).
    let bin = f.dir.join("run/mini-keys");
    std::fs::copy(env!("CARGO_BIN_EXE_mini-keys"), &bin).unwrap();
    std::fs::set_permissions(&bin, std::fs::Permissions::from_mode(0o755)).unwrap();
    // The foreign account may traverse to the socket and reach it; nothing else in the tree.
    for d in [&f.dir, &f.dir.join("run")] {
        std::fs::set_permissions(d, std::fs::Permissions::from_mode(0o711)).unwrap();
    }
    let me = peer::euid();
    let peers = json!([{"role":"member","uids":[foreign]},{"role":"provider","uids":[me.wrapping_add(100_000)]}]);
    let mut cfg = f.config_json(peers, false);
    cfg.as_object_mut().unwrap().remove("discord");
    let b = f.start(cfg).unwrap();
    std::fs::set_permissions(&f.socket, std::fs::Permissions::from_mode(0o666)).unwrap();
    let as_foreign = |args: &[&str]| {
        std::process::Command::new("sudo")
            .args(["-n", "setpriv", &format!("--reuid={foreign}"), &format!("--regid={foreign}"), "--clear-groups", "--"])
            .args(args)
            .output()
            .unwrap()
    };
    let hello = as_foreign(&[bin.to_str().unwrap(), "hello", "--socket", f.socket.to_str().unwrap(), "--uid", &me.to_string()]);
    let out: Value = serde_json::from_slice(&hello.stdout).unwrap_or(Value::Null);
    assert_eq!(out["roles"], json!(["member"]), "stderr: {}", String::from_utf8_lossy(&hello.stderr));
    assert_eq!(out["peer"]["uid"], foreign);
    let pool = as_foreign(&[bin.to_str().unwrap(), "pool", "--action", "ls", "--socket", f.socket.to_str().unwrap(), "--uid", &me.to_string()]);
    assert!(String::from_utf8_lossy(&pool.stderr).contains("op-not-granted"), "{}", String::from_utf8_lossy(&pool.stderr));
    for secret in [&f.key, &f.mirror] {
        let cat = as_foreign(&["cat", secret.to_str().unwrap()]);
        assert!(!cat.status.success() && cat.stdout.is_empty(), "uid {foreign} read {}", secret.display());
    }
    // This test's own process holds no role in the split shape.
    assert_eq!(client::hello(&b).unwrap_err().code, "peer-not-allowed");
}
