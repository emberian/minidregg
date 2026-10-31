//! The endpoint end to end over loopback: signed interactions in, a stand-in forced command
//! (a script that reports what it was given), follow-ups PATCHed through /usr/bin/curl to a
//! loopback listener. The real `mini shell` path is the evidence run's job; this pins the
//! entrance's own decisions.

use std::net::TcpListener;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::time::Duration;

use ed25519_dalek::{Signer, SigningKey};
use minidregg_discord_entrance::curl::Poster;
#[path = "support/client.rs"]
mod client;
use client::client_request;
use minidregg_discord_entrance::http::{read_request, write_response};
use minidregg_discord_entrance::now_s;
use minidregg_discord_entrance::server::{App, Config};
use minidregg_discord_entrance::session::{Deployment, Sessions};
use minidregg_discord_entrance::signature::hex_encode;
use serde_json::{json, Value};

const APP: &str = "4242";
const FRIEND: &str = "111";
const STRANGER: &str = "222";

const WRAPPER: &str = r#"#!/bin/sh
case "$SSH_ORIGINAL_COMMAND" in
  refuse*) echo "workspace read attempt: x" >&2; echo "refused: no-grant: this key holds no grant (Host refused query, reply byte 255)" >&2; echo "  outcome ..." >&2; exit 3 ;;
  big*) i=0; while [ $i -lt 300 ]; do echo "0123456789"; i=$((i+1)); done; exit 0 ;;
esac
printf 'argc=%s ws=%s home=%s line=[%s] home_env=%s\n' "$#" "$5" "$6" "$SSH_ORIGINAL_COMMAND" "${HOME-unset}"
"#;

struct World {
    addr: String,
    key: SigningKey,
    patches: mpsc::Receiver<(String, Value)>,
    sessions: PathBuf,
    cfg: Config,
}

fn world(tag: &str) -> World {
    world_with(tag, false)
}

/// The split shape: the entrance runs each line through the root runner's socket as the
/// session's own account (here a stand-in listener speaking the runner's protocol:
/// `NAME\nLINE\n` in, `mini-session-run-v1 EXIT OUTLEN ERRLEN\n` and the streams out) and
/// keeps its custody and log in its own state directory.
fn stand_in_runner(socket: &Path) {
    use std::io::{Read, Write};
    let listener = std::os::unix::net::UnixListener::bind(socket).unwrap();
    std::thread::spawn(move || {
        for s in listener.incoming() {
            let mut s = s.unwrap();
            let mut request = String::new();
            s.read_to_string(&mut request).unwrap();
            let mut lines = request.splitn(3, '\n');
            let (name, line) = (lines.next().unwrap_or(""), lines.next().unwrap_or(""));
            let out = format!("runner name={name} line=[{line}] ssh_env=unset\n");
            let _ = s.write_all(format!("mini-session-run-v1 0 {} 0\n{out}", out.len()).as_bytes());
        }
    });
}

fn world_with(tag: &str, split: bool) -> World {
    let root = std::env::temp_dir().join(format!("discord-entrance-{tag}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    for d in ["sessions/friend", "spool"] {
        std::fs::create_dir_all(root.join(d)).unwrap();
    }
    let wrapper = root.join("wrapper");
    std::fs::write(&wrapper, WRAPPER).unwrap();
    std::fs::set_permissions(&wrapper, std::fs::Permissions::from_mode(0o755)).unwrap();
    let roster = root.join("roster.json");
    std::fs::write(&roster, json!({ "version": 1, "users": { FRIEND: "friend" } }).to_string()).unwrap();
    std::fs::set_permissions(&roster, std::fs::Permissions::from_mode(0o644)).unwrap();
    let uid = std::os::unix::fs::MetadataExt::uid(&std::fs::metadata(&roster).unwrap());

    // The Discord API stand-in: records each PATCH.
    let api = TcpListener::bind("127.0.0.1:0").unwrap();
    let api_addr = api.local_addr().unwrap().to_string();
    let (tx, patches) = mpsc::channel();
    std::thread::spawn(move || {
        for s in api.incoming() {
            let mut s = s.unwrap();
            let req = read_request(&mut s).unwrap();
            let _ = write_response(&mut s, 200, "OK", "application/json", b"{}");
            let _ = tx.send((format!("{} {}", req.method, req.path), serde_json::from_slice(&req.body).unwrap()));
        }
    });

    let key = SigningKey::from_bytes(&[9u8; 32]);
    let p = |x: &str| PathBuf::from(format!("/fixed/{x}"));
    let cfg = Config {
        mode: minidregg_discord_entrance::server::Mode::Http,
        bot_token_file: None,
        gateway_url: String::new(),
        ca_file: PathBuf::from("/nonexistent"),
        listen: String::new(),
        application_id: APP.into(),
        public_key_hex: hex_encode(key.verifying_key().as_bytes()),
        api_base: format!("http://{api_addr}/api/v10"),
        roster,
        roster_owner_uid: uid,
        max_inflight: 4,
        deployment: Deployment {
            wrapper,
            mini: p("mini"),
            host: p("host"),
            config: p("config"),
            socket: p("socket"),
            timeout: Duration::from_secs(20),
            runner: split.then(|| {
                let runner = root.join("runner.sock");
                stand_in_runner(&runner);
                runner
            }),
        },
        sessions: Sessions { dir: root.join("sessions"), sponsor: "ember".into(), sponsor_workspace: p("sponsor-ws") },
        poster: Poster { curl: "/usr/bin/curl".into(), spool: root.join("spool"), max_time_s: 10 },
        state: split.then(|| {
            let state = root.join("entrance-state");
            std::fs::create_dir_all(&state).unwrap();
            std::fs::set_permissions(&state, std::fs::Permissions::from_mode(0o700)).unwrap();
            state
        }),
        door_links: split.then(|| root.join("entrance-state/door-links")),
        door_url: Some("https://demo.example/join".into()),
        retention: minidregg_discord_entrance::session::Retention { max_age_s: 7 * 86_400, max_records: 2000 },
    };
    let app = App::new(cfg.clone()).unwrap();
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap().to_string();
    std::thread::spawn(move || app.serve(listener));
    World { addr, key, patches, sessions: root.join("sessions"), cfg }
}

fn post(w: &World, body: &Value, corrupt: bool) -> (u16, String) {
    let body = body.to_string();
    let ts = now_s().to_string();
    let mut m = ts.as_bytes().to_vec();
    m.extend_from_slice(body.as_bytes());
    let mut sig = w.key.sign(&m).to_bytes();
    if corrupt {
        sig[5] ^= 0x80;
    }
    let sig = hex_encode(&sig);
    let (status, resp) = client_request(
        &w.addr,
        "POST",
        "/interactions",
        &[("X-Signature-Ed25519", &sig), ("X-Signature-Timestamp", &ts)],
        body.as_bytes(),
    )
    .unwrap();
    (status, String::from_utf8(resp).unwrap())
}

fn command(id: &str, user: &str, name: &str, line: Option<&str>) -> Value {
    let mut data = json!({ "name": name });
    if let Some(l) = line {
        data["options"] = json!([{ "name": "line", "type": 3, "value": l }]);
    }
    json!({ "type": 2, "id": id, "application_id": APP, "token": format!("tok-{id}"),
            "member": { "user": { "id": user } }, "data": data })
}

fn feedback_command(id: &str, user: &str, text: &str) -> Value {
    json!({ "type": 2, "id": id, "application_id": APP, "token": format!("tok-{id}"),
            "member": { "user": { "id": user } },
            "data": { "name": "feedback", "options": [{ "name": "text", "type": 3, "value": text }] } })
}

fn content(resp: &str) -> String {
    let v: Value = serde_json::from_str(resp).unwrap();
    assert_eq!(v["type"], 4, "{resp}");
    assert_eq!(v["data"]["flags"], 64);
    v["data"]["content"].as_str().unwrap().split("\nCustody:").next().unwrap().to_string()
}

fn deferred_then_patch(w: &World, id: &str, resp: (u16, String)) -> String {
    assert_eq!(resp.0, 200);
    let v: Value = serde_json::from_str(&resp.1).unwrap();
    assert_eq!(v, json!({ "type": 5, "data": { "flags": 64 } }));
    let (route, body) = w.patches.recv_timeout(Duration::from_secs(20)).expect("no follow-up PATCH");
    assert_eq!(route, format!("PATCH /api/v10/webhooks/{APP}/tok-{id}/messages/@original"));
    assert_eq!(body["allowed_mentions"], json!({ "parse": [] }));
    body["content"].as_str().unwrap().split("\nCustody:").next().unwrap().to_string()
}

/// The Discord stand-in answers the PATCH before the worker records delivery and drops its
/// custody lease. A retry or restart that races it sees the record held ("already held by a
/// worker"), which is the entrance behaving correctly. Wait for the lease itself (the worker
/// is gone) and return, so what follows runs against the retained record.
fn wait_for_worker_release(w: &World, id: &str) {
    let custody = w.sessions.join(".discord-custody");
    let key = format!("{APP}-{id}");
    let t0 = std::time::Instant::now();
    loop {
        if mini_sdk::store::Record::lock(&custody, &key).unwrap().is_some() {
            return;
        }
        assert!(t0.elapsed() < Duration::from_secs(20), "worker never released its custody lease");
        std::thread::sleep(Duration::from_millis(5));
    }
}

#[test]
fn ping_and_signatures() {
    let w = world("sig");
    assert_eq!(post(&w, &json!({ "type": 1 }), false), (200, r#"{"type":1}"#.to_string()));
    let (status, body) = post(&w, &json!({ "type": 1 }), true);
    assert_eq!((status, body.as_str()), (401, "invalid request signature"));
    let (status, _) = client_request(&w.addr, "POST", "/interactions", &[], b"{\"type\":1}").unwrap();
    assert_eq!(status, 401);
    let (status, _) = client_request(&w.addr, "GET", "/interactions", &[], b"").unwrap();
    assert_eq!(status, 405);
}

#[test]
fn a_rostered_line_runs_in_its_session_deferred_and_logged() {
    let w = world("run");
    let c = deferred_then_patch(&w, "1", post(&w, &command("1", FRIEND, "mini", Some("read 'a b' {\"x\":1}")), false));
    let home = w.sessions.join("friend");
    let expect = format!(
        "argc=6 ws={}/workspace home={} line=[read 'a b' {{\"x\":1}}] home_env=unset",
        home.display(),
        home.display()
    );
    assert_eq!(c, format!("```\n{expect}\n```"));
    wait_for_worker_release(&w, "1");
    // The same signed body returns retained output without re-execution.
    let (status, body) = post(&w, &command("1", FRIEND, "mini", Some("read 'a b' {\"x\":1}")), false);
    assert_eq!(status, 200);
    assert_eq!(content(&body), c);
    // /mini-help is the shell's own `help`.
    let c = deferred_then_patch(&w, "2", post(&w, &command("2", FRIEND, "mini-help", None), false));
    assert!(c.contains("line=[help]"), "{c}");
    // A refusal comes back as the shell's own ending line, verbatim.
    let c = deferred_then_patch(&w, "3", post(&w, &command("3", FRIEND, "mini", Some("refuse me")), false));
    assert_eq!(c, "```\nrefused: no-grant: this key holds no grant (Host refused query, reply byte 255)\n```");
    // Long output is cut to 2000 characters with a note.
    let c = deferred_then_patch(&w, "4", post(&w, &command("4", FRIEND, "mini", Some("big")), false));
    assert!(c.chars().count() <= 2000 && c.contains("truncated"), "{}", c.len());
    let log = std::fs::read_to_string(home.join("discord.log")).unwrap();
    let recs: Vec<Value> = log.lines().map(|l| serde_json::from_str(l).unwrap()).collect();
    assert_eq!(recs.len(), 4);
    assert_eq!(recs[0]["discord_user"], FRIEND);
    assert_eq!(recs[0]["ending"], "ok");
    assert_eq!(recs[2]["line"], "refuse me");
    assert_eq!(recs[2]["ending"], "refused");
    assert_eq!(recs[2]["exit"], 3);
    let mode = std::fs::metadata(home.join("discord.log")).unwrap().permissions().mode() & 0o777;
    assert_eq!(mode, 0o600);
}

/// `/feedback text:` runs the member's own `feedback --via discord "TEXT"` line in the member's
/// session (the same turn the shell and the web make), the text quoted whole so none of its words
/// can be read as a flag of the verb; an empty text runs nothing.
#[test]
fn feedback_is_the_members_own_report_line() {
    let w = world("feedback");
    let c = deferred_then_patch(&w, "1", post(&w, &feedback_command("1", FRIEND, "--clause fake the button is gone"), false));
    let home = w.sessions.join("friend");
    assert!(c.contains("line=[feedback --via discord \"--clause fake the button is gone\"]"), "{c}");
    assert!(c.contains(&format!("home={}", home.display())), "{c}");
    wait_for_worker_release(&w, "1");
    let (status, body) = post(&w, &feedback_command("2", FRIEND, "   "), false);
    assert_eq!(status, 200);
    assert!(content(&body).contains("usage: /feedback text:"), "{body}");
}

#[test]
fn split_tenancy_lines_go_through_the_runner_and_nothing_is_written_in_the_sessions_tree() {
    let w = world_with("split", true);
    let c = deferred_then_patch(&w, "1", post(&w, &command("1", FRIEND, "mini", Some("read 'a b' {\"x\":1}")), false));
    assert_eq!(c, "```\nrunner name=friend line=[read 'a b' {\"x\":1}] ssh_env=unset\n```");
    let state = w.cfg.state.clone().unwrap();
    let log = std::fs::read_to_string(state.join("log/friend.discord.log")).unwrap();
    assert_eq!(log.lines().count(), 1);
    assert!(std::fs::read_dir(state.join("custody")).unwrap().count() >= 1);
    // The entrance wrote nothing a session account owns.
    assert!(!w.sessions.join("friend/discord.log").exists());
    assert!(!w.sessions.join(".discord-custody").exists());
}

#[test]
fn refusals_before_any_line_runs() {
    let w = world("refuse");
    let c = content(&post(&w, &command("10", STRANGER, "mini", Some("refs")), false).1);
    assert_eq!(
        c,
        "```\nerror: You have no Mini account linked to this Discord user yet; nothing ran. Get one at https://demo.example/join and its page gives you the line `/mini line:link CODE`.\n```"
    );
    let long = "x".repeat(1001);
    let c = content(&post(&w, &command("11", FRIEND, "mini", Some(&long)), false).1);
    assert_eq!(c, "```\nusage: the line is 1001 characters; the limit is 1000\n```");
    let c = content(&post(&w, &command("12", FRIEND, "mini", None), false).1);
    assert!(c.starts_with("```\nusage:"), "{c}");
    let c = content(&post(&w, &command("13", FRIEND, "other", Some("refs")), false).1);
    assert!(c.contains("error: unknown command /other"), "{c}");
    // Nothing was PATCHed and nothing ran; the rostered refusal was logged.
    assert!(w.patches.recv_timeout(Duration::from_millis(300)).is_err());
    let log = std::fs::read_to_string(w.sessions.join("friend/discord.log")).unwrap();
    assert_eq!(log.lines().count(), 1);
    assert!(log.contains("\"ending\":\"usage\""));
    assert!(!Path::new(&w.sessions.join("stranger")).exists());
}

#[test]
fn a_roster_writable_by_others_answers_no_one() {
    let w = world("mode");
    let roster = w.sessions.parent().unwrap().join("roster.json");
    std::fs::set_permissions(&roster, std::fs::Permissions::from_mode(0o666)).unwrap();
    let c = content(&post(&w, &command("20", FRIEND, "mini", Some("refs")), false).1);
    assert_eq!(c, "```\nerror: the Discord roster is unavailable on this box; nothing ran\n```");
}

fn signed(w:&World,v:&Value)->minidregg_discord_entrance::http::Request {
    let body=v.to_string().into_bytes();let ts=now_s().to_string();let mut msg=ts.as_bytes().to_vec();msg.extend_from_slice(&body);
    minidregg_discord_entrance::http::Request{method:"POST".into(),path:"/interactions".into(),query:String::new(),headers:vec![("x-signature-timestamp".into(),ts),("x-signature-ed25519".into(),hex_encode(&w.key.sign(&msg).to_bytes()))],body}
}
#[test]
fn durable_restart_exact_binding_unknown_and_roster_revocation(){
    let w=world("restart");let cmd=command("70",FRIEND,"mini",Some("read shared"));
    let first=deferred_then_patch(&w,"70",post(&w,&cmd,false));
    // The PATCH is answered before the worker records delivery and drops its custody lease; a
    // restart that races it sees the record held. Wait for the lease, then require what it
    // left: delivery confirmed.
    wait_for_worker_release(&w,"70");let custody=w.sessions.join(".discord-custody");
    assert_eq!(serde_json::from_slice::<Value>(&std::fs::read(custody.join("4242-70.json")).unwrap()).unwrap()["delivery"],"confirmed");
    let restarted=App::new(w.cfg.clone()).unwrap();
    let (resp,job)=restarted.handle(&signed(&w,&cmd),now_s());assert!(job.is_none());assert_eq!(content(&String::from_utf8(resp.body).unwrap()),first);
    let (resp,job)=restarted.handle(&signed(&w,&command("70",FRIEND,"mini",Some("submit foreign"))),now_s());assert_eq!(resp.status,409);assert!(job.is_none());
    // Persisted start is a transport unknown even when this test's worker never ran.
    let path=w.sessions.join(".discord-custody/4242-70.json");let mut rec:Value=serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();rec["phase"]=json!("started");
    mini_sdk::store::atomic_json(&path,&rec).unwrap();
    let (resp,job)=restarted.handle(&signed(&w,&cmd),now_s());assert!(job.is_none());assert!(content(&String::from_utf8(resp.body).unwrap()).contains("UNKNOWN"));
    std::fs::write(&w.cfg.roster,json!({"version":1,"users":{}}).to_string()).unwrap();
    let (resp,job)=restarted.handle(&signed(&w,&cmd),now_s());assert!(job.is_none());assert!(content(&String::from_utf8(resp.body).unwrap()).contains("no Mini account linked"));
    assert_eq!(std::fs::read_to_string(w.sessions.join("friend/discord.log")).unwrap().lines().count(),1);
}
#[test]
fn nothing_is_retained_before_the_deferral_is_written_and_status_is_actor_bound(){
    // No write stands between Discord's request and the deferral: `handle` only takes the
    // custody lease; the acceptance is retained after the deferral is on the wire. A request
    // whose deferral was never written leaves nothing and ran nothing.
    let w=world("accepted");let app=App::new(w.cfg.clone()).unwrap();let cmd=command("80",FRIEND,"mini",Some("read shared"));
    let (_,job)=app.handle(&signed(&w,&cmd),now_s());assert!(job.is_some());drop(job);drop(app);
    assert!(!w.sessions.join(".discord-custody/4242-80.json").exists());
    let app=App::new(w.cfg.clone()).unwrap();
    let mut status=command("81",FRIEND,"mini-status",None);status["data"]["options"]=json!([{"name":"target","value":"80","type":3}]);
    let (resp,job)=app.handle(&signed(&w,&status),now_s());assert!(job.is_none());assert!(content(&String::from_utf8(resp.body).unwrap()).contains("no retained interaction"));
    // A completed line is visible to its own user and session only.
    deferred_then_patch(&w,"82",post(&w,&command("82",FRIEND,"mini",Some("read shared")),false));
    wait_for_worker_release(&w,"82");
    status["data"]["options"]=json!([{"name":"target","value":"82","type":3}]);
    let (resp,_)=app.handle(&signed(&w,&status),now_s());assert!(content(&String::from_utf8(resp.body).unwrap()).contains("argc=6"));
    // A second rostered Discord user on the same hosted session still cannot inspect it.
    std::fs::write(&w.cfg.roster,json!({"version":1,"users":{FRIEND:"friend",STRANGER:"friend"}}).to_string()).unwrap();
    status["member"]["user"]["id"]=json!(STRANGER);
    let (resp,_)=app.handle(&signed(&w,&status),now_s());assert!(content(&String::from_utf8(resp.body).unwrap()).contains("no retained interaction"));
}

#[test]
fn an_unrostered_link_line_queues_one_request_for_the_door_and_never_runs() {
    let w = world_with("link", true);
    let spool = w.cfg.door_links.clone().unwrap();
    let c = content(&post(&w, &command("20", STRANGER, "mini", Some("link abcdefghijklmnop")), false).1);
    assert!(c.starts_with("```\nlink request queued"), "{c}");
    let files: Vec<_> = std::fs::read_dir(&spool).unwrap().map(|e| e.unwrap().path()).collect();
    assert_eq!(files.len(), 1);
    let link = minidregg_discord_entrance::door::Link::parse(&std::fs::read(&files[0]).unwrap()).unwrap();
    assert_eq!((link.user.as_str(), link.code.as_str(), link.interaction.as_str()), (STRANGER, "ABCDEFGHIJKLMNOP", "20"));
    // The same interaction again is refused by the spool (create_new), not queued twice.
    let c = content(&post(&w, &command("20", STRANGER, "mini", Some("link ABCDEFGHIJKLMNOP")), false).1);
    assert!(c.contains("error:"), "{c}");
    // A rostered user cannot relink; a malformed code is just an unrostered line.
    let c = content(&post(&w, &command("21", FRIEND, "mini", Some("link ABCDEFGHIJKLMNOP")), false).1);
    assert!(c.contains("already linked to session friend"), "{c}");
    let c = content(&post(&w, &command("22", STRANGER, "mini", Some("link short")), false).1);
    assert!(c.contains("no Mini account linked"), "{c}");
    assert_eq!(std::fs::read_dir(&spool).unwrap().count(), 1);
}
