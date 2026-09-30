//! The interactions endpoint.
//!
//! `POST /interactions`: verify the signature (401 otherwise, which is also what Discord's
//! own endpoint check sends a bad signature to find), answer PING, and for `/mini <line>` or
//! `/mini-help`:
//!
//! 1. refuse a replayed interaction id (401) and a foreign application id (400);
//! 2. resolve the Discord user through the roster to a session, or answer an `error:` line
//!    that says ember must add them;
//! 3. check the line (≤ 1000 characters, one line), or answer a `usage:` line;
//! 4. answer DEFERRED (ephemeral) at once, and only after that response is written run the
//!    line through the session's forced command, log `(user, line, ending)` to the session's
//!    `discord.log`, and PATCH the output or the ending line into `@original`.
//!
//! Lines of one session run one at a time, in arrival order; at most `max_inflight` lines
//! run at once across sessions.

use std::collections::HashMap;
use std::net::{TcpListener, TcpStream};
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use serde_json::Value;

use crate::curl::Poster;
use crate::http::{read_request, write_response, Request};
use crate::interaction::{self, Interaction, COMMAND_HELP, COMMAND_LINE};
use crate::reply::{self, Ending};
use crate::roster::Roster;
use crate::session::{append_log, check_line, log_record, Deployment, Session, Sessions};
use crate::signature::Verifier;
use crate::{env_required, env_u64, now_s};

pub const DISCORD_API: &str = "https://discord.com/api/v10";
/// How long an interaction id is remembered (Discord's interaction token lives 15 minutes).
pub const SEEN_TTL_S: u64 = 900;
pub const MAX_CONNECTIONS: usize = 64;
pub const LOG_FILE: &str = "discord.log";

#[derive(Debug, Clone)]
pub struct Config {
    pub listen: String,
    pub application_id: String,
    pub public_key_hex: String,
    pub api_base: String,
    pub roster: PathBuf,
    pub roster_owner_uid: u32,
    pub max_inflight: usize,
    pub deployment: Deployment,
    pub sessions: Sessions,
    pub poster: Poster,
}

impl Config {
    /// Everything comes from the environment (the unit's 0600 `EnvironmentFile`); nothing is
    /// read from argv.
    pub fn from_env() -> Result<Self, String> {
        let application_id = env_required("MINI_DISCORD_APPLICATION_ID")?;
        if !interaction::is_snowflake(&application_id) {
            return Err("MINI_DISCORD_APPLICATION_ID must be a Discord snowflake".into());
        }
        let api_base = std::env::var("MINI_DISCORD_API_BASE").unwrap_or_else(|_| DISCORD_API.to_string());
        if !crate::curl::is_plain_url(&api_base) {
            return Err("MINI_DISCORD_API_BASE is not a plain URL".into());
        }
        let path_or = |name: &str, default: &str| -> Result<PathBuf, String> {
            match std::env::var(name) {
                Ok(v) if !v.is_empty() => crate::env_path(name),
                _ => Ok(PathBuf::from(default)),
            }
        };
        Ok(Config {
            listen: std::env::var("MINI_DISCORD_LISTEN").unwrap_or_else(|_| "127.0.0.1:8793".to_string()),
            application_id,
            public_key_hex: env_required("MINI_DISCORD_PUBLIC_KEY")?,
            api_base: api_base.trim_end_matches('/').to_string(),
            roster: path_or("MINI_DISCORD_ROSTER", "/etc/mini/discord-roster.json")?,
            roster_owner_uid: env_u64("MINI_DISCORD_ROSTER_OWNER_UID", 0)? as u32,
            max_inflight: env_u64("MINI_DISCORD_MAX_INFLIGHT", 4)? as usize,
            deployment: Deployment::from_env()?,
            sessions: Sessions::from_env()?,
            poster: Poster {
                curl: path_or("MINI_DISCORD_CURL", crate::curl::CURL)?,
                spool: path_or("MINI_DISCORD_SPOOL", "/run/mini-discord")?,
                max_time_s: 20,
            },
        })
    }
}

/// A line accepted for running after the DEFERRED response is on the wire.
pub struct Job {
    user: String,
    interaction: String,
    token: String,
    session: Session,
    line: String,
}

pub struct Reply {
    pub status: u16,
    pub reason: &'static str,
    pub content_type: &'static str,
    pub body: Vec<u8>,
}

impl Reply {
    fn json(v: &Value) -> Self {
        Reply { status: 200, reason: "OK", content_type: "application/json", body: v.to_string().into_bytes() }
    }
    fn text(status: u16, reason: &'static str, text: &str) -> Self {
        Reply { status, reason, content_type: "text/plain; charset=utf-8", body: text.as_bytes().to_vec() }
    }
}

pub struct App {
    cfg: Config,
    verifier: Verifier,
    seen: Mutex<HashMap<String, u64>>,
    locks: Mutex<HashMap<String, Arc<Mutex<()>>>>,
    inflight: Arc<AtomicUsize>,
}

/// One running line; dropping it frees the slot.
pub struct Inflight(Arc<AtomicUsize>);
impl Drop for Inflight {
    fn drop(&mut self) {
        self.0.fetch_sub(1, Ordering::SeqCst);
    }
}

impl App {
    pub fn new(cfg: Config) -> Result<Arc<Self>, String> {
        let verifier = Verifier::from_hex(&cfg.public_key_hex)?;
        Ok(Arc::new(App {
            cfg,
            verifier,
            seen: Mutex::new(HashMap::new()),
            locks: Mutex::new(HashMap::new()),
            inflight: Arc::new(AtomicUsize::new(0)),
        }))
    }

    pub fn handle(&self, req: &Request, now: u64) -> (Reply, Option<(Job, Inflight)>) {
        if req.path == "/healthz" && req.method == "GET" {
            return (Reply::text(200, "OK", "ok\n"), None);
        }
        if req.path != "/interactions" {
            return (Reply::text(404, "Not Found", "not found\n"), None);
        }
        if req.method != "POST" {
            return (Reply::text(405, "Method Not Allowed", "POST only\n"), None);
        }
        if let Err(e) = self.verifier.verify(
            req.header("x-signature-ed25519"),
            req.header("x-signature-timestamp"),
            &req.body,
            now,
        ) {
            eprintln!("mini-discord: 401 {}", e.as_str());
            return (Reply::text(401, "Unauthorized", e.as_str()), None);
        }
        let cmd = match interaction::parse(&req.body) {
            Ok(Interaction::Ping) => return (Reply::json(&interaction::pong()), None),
            Ok(Interaction::Unsupported(t)) => {
                return (Reply::text(400, "Bad Request", &format!("unsupported interaction type {t}")), None)
            }
            Ok(Interaction::Command(c)) => c,
            Err(e) => return (Reply::text(400, "Bad Request", &e), None),
        };
        if cmd.application_id != self.cfg.application_id {
            return (Reply::text(400, "Bad Request", "interaction for another application"), None);
        }
        if !interaction::is_token(&cmd.token) || !interaction::is_snowflake(&cmd.user_id) {
            return (Reply::text(400, "Bad Request", "malformed interaction token or user id"), None);
        }
        {
            let mut seen = self.seen.lock().unwrap_or_else(|p| p.into_inner());
            seen.retain(|_, t| now.saturating_sub(*t) <= SEEN_TTL_S);
            if seen.insert(cmd.id.clone(), now).is_some() {
                eprintln!("mini-discord: 401 replayed interaction {}", cmd.id);
                return (Reply::text(401, "Unauthorized", "replayed interaction"), None);
            }
        }
        let say = |ending: Ending| Reply::json(&interaction::message(&reply::code_block(&ending.line)));

        let line = match (cmd.name.as_str(), cmd.line) {
            (COMMAND_LINE, Some(l)) => l,
            (COMMAND_LINE, None) => {
                return (say(Ending::entrance("usage", "/mini LINE: the line option is required")), None)
            }
            (COMMAND_HELP, _) => "help".to_string(),
            (other, _) => return (say(Ending::entrance("error", &format!("unknown command /{other}"))), None),
        };

        let roster = match Roster::load(&self.cfg.roster, self.cfg.roster_owner_uid) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("mini-discord: roster unavailable: {e}");
                return (say(Ending::entrance("error", "the Discord roster is unavailable on this box; nothing ran")), None);
            }
        };
        let Some(name) = roster.session_of(&cmd.user_id) else {
            eprintln!("mini-discord: user {} is not rostered; line not run", cmd.user_id);
            let text = format!(
                "Discord user {} is not on this Mini's roster; nothing ran. Ember must add you: send ember this id.",
                cmd.user_id
            );
            return (say(Ending::entrance("error", &text)), None);
        };
        let session = match self.cfg.sessions.open(name) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("mini-discord: user {}: {e}", cmd.user_id);
                return (say(Ending::entrance("error", &e)), None);
            }
        };
        let refuse = |ending: Ending| {
            self.log(&session, now, &cmd.user_id, &cmd.id, &line, &ending, None);
            say(ending)
        };
        if let Err(e) = check_line(&line) {
            return (refuse(Ending::entrance("usage", &e)), None);
        }
        let running = self.inflight.fetch_add(1, Ordering::SeqCst);
        let guard = Inflight(self.inflight.clone());
        if running >= self.cfg.max_inflight {
            drop(guard);
            let text = format!("the Discord entrance is running {running} lines; nothing ran, try again shortly");
            return (refuse(Ending::entrance("error", &text)), None);
        }
        let job = Job { user: cmd.user_id, interaction: cmd.id, token: cmd.token, session, line };
        (Reply::json(&interaction::deferred()), Some((job, guard)))
    }

    #[allow(clippy::too_many_arguments)]
    fn log(&self, s: &Session, at: u64, user: &str, id: &str, line: &str, ending: &Ending, exit: Option<i32>) {
        let rec = log_record(at, user, id, line, ending, exit);
        if let Err(e) = append_log(&s.home, LOG_FILE, &rec) {
            eprintln!("mini-discord: session {}: cannot append {LOG_FILE}: {e}", s.name);
        }
        eprintln!("mini-discord: user {} session {} ending {}", user, s.name, ending.word);
    }

    /// Run an accepted line and PATCH its answer into `@original`.
    pub fn run_job(&self, job: Job, _inflight: Inflight) {
        let lock = {
            let mut locks = self.locks.lock().unwrap_or_else(|p| p.into_inner());
            locks.entry(job.session.name.clone()).or_default().clone()
        };
        let outcome = {
            let _one_at_a_time = lock.lock().unwrap_or_else(|p| p.into_inner());
            self.cfg.deployment.run(&job.session, &job.line)
        };
        self.log(&job.session, now_s(), &job.user, &job.interaction, &job.line, &outcome.ending, outcome.exit);
        let content = reply::render(&outcome.stdout, &outcome.ending);
        let url = format!(
            "{}/webhooks/{}/{}/messages/@original",
            self.cfg.api_base, self.cfg.application_id, job.token
        );
        let body = interaction::followup(&content).to_string();
        match self.cfg.poster.send("PATCH", &url, body.as_bytes()) {
            Ok(code) if (200..300).contains(&code) => {}
            Ok(code) => eprintln!("mini-discord: follow-up for {} answered HTTP {code}", job.interaction),
            Err(e) => eprintln!("mini-discord: follow-up for {} failed: {e}", job.interaction),
        }
    }

    pub fn connection(self: &Arc<Self>, mut stream: TcpStream) {
        let req = match read_request(&mut stream) {
            Ok(r) => r,
            Err(e) => {
                if let Some((status, reason)) = e.status {
                    let _ = write_response(&mut stream, status, reason, "text/plain", e.detail.as_bytes());
                }
                return;
            }
        };
        let (reply, job) = self.handle(&req, now_s());
        let written = write_response(&mut stream, reply.status, reply.reason, reply.content_type, &reply.body);
        drop(stream);
        if let Some((job, guard)) = job {
            if let Err(e) = written {
                // Discord never saw the deferral; running the line would act unseen.
                eprintln!("mini-discord: deferral for {} not delivered ({e}); line not run", job.interaction);
                return;
            }
            self.run_job(job, guard);
        }
    }

    pub fn serve(self: &Arc<Self>, listener: TcpListener) -> ! {
        let open = Arc::new(AtomicUsize::new(0));
        loop {
            let stream = match listener.accept() {
                Ok((s, _)) => s,
                Err(e) => {
                    eprintln!("mini-discord: accept: {e}");
                    continue;
                }
            };
            if open.fetch_add(1, Ordering::SeqCst) >= MAX_CONNECTIONS {
                open.fetch_sub(1, Ordering::SeqCst);
                continue;
            }
            let app = self.clone();
            let open = open.clone();
            std::thread::spawn(move || {
                app.connection(stream);
                open.fetch_sub(1, Ordering::SeqCst);
            });
        }
    }
}
