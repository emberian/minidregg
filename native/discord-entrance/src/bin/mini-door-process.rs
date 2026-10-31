//! `mini-door-process`: the door's root processor (deploy/door/README.md).
//!
//! A oneshot, every minute (`mini-door-process.timer`). It is the ONLY writer of door accounts,
//! hosted keys, the door's roster entries (and so `authorized_keys`) and the Discord roster,
//! and it acts only on requests of the exact schema in `door` that the unprivileged writers put
//! in their spools. It does nothing itself that the box's scripts already do: a door account is
//! a roster entry in the box's per-box roster (`$INFRA/friends/door/NAME.pub`), made real by
//! `render-authorized-keys.sh`, keyed by the session's own `keygen mini.key` run as
//! `mini-s-NAME`, and enrolled by `mini-reenroll NAME` (free) or by the stranger's payment to
//! that hosted key (`mini join --memo-version v2`, paid).
//!
//! Every request's phase is retained before the next step, and every step is idempotent, so a
//! crash anywhere is finished by the next tick. A refusal is final and is shown on the
//! stranger's status page.
//!
//!   mini-door-process [--root DIR]      DIR prefixes every box path (tests and the dry journey)

use std::collections::HashMap;
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use minidregg_discord_entrance::door::{self, Link, Request, Route};
use minidregg_discord_entrance::now_s;
use serde_json::{json, Value};

const DOOR_USER: &str = "mini-door";
/// The read bound a house publication is delegated under: the public reader's (`deploy/demo-seed`).
const PUBLIC_READ_MAX_COST: &str = include_str!("../../../../deploy/demo-seed/public-read-max-cost");
const DISCORD_USER: &str = "mini-discord";
const TENANT_GROUP: &str = "mini-sessions";
/// A stranger who never finishes paying: the request is closed after this long.
const PAID_TTL_S: u64 = 7 * 86_400;

/// Every box path, under an optional root prefix.
#[derive(Clone)]
struct Paths {
    root: PathBuf,
}

impl Paths {
    fn at(&self, path: &str) -> PathBuf {
        self.root.join(path.trim_start_matches('/'))
    }
    fn etc(&self) -> PathBuf { self.at("/etc/mini") }
    fn lib(&self) -> PathBuf { self.at("/usr/local/lib/mini") }
    fn friends(&self) -> PathBuf { self.lib().join("infra/friends") }
    fn door_friends(&self) -> PathBuf { self.friends().join("door") }
    fn candidate(&self) -> PathBuf { self.at("/var/lib/mini/candidate/current") }
    fn node(&self) -> PathBuf { self.at("/var/lib/mini/store/node") }
    fn sessions(&self) -> PathBuf { self.at("/var/lib/mini/sessions") }
    fn home(&self, name: &str) -> PathBuf { self.sessions().join(name) }
    fn queue(&self) -> PathBuf { self.at("/var/lib/mini-door/queue") }
    fn links(&self) -> PathBuf { self.at("/var/lib/mini-discord/door-links") }
    fn status(&self) -> PathBuf { self.at("/var/lib/mini-door-status") }
    fn state(&self) -> PathBuf { self.at("/var/lib/mini-door-process") }
    /// The web front end's one-time login records (minidregg docs/WEB-FRONTEND-2026-10-27.md §2):
    /// root 0600 files named by the SHA-256 of the code, read and deleted by `mini-web-spawn`.
    fn web_logins(&self) -> PathBuf { self.at("/var/lib/mini-web-spawn/logins") }
    fn config(&self) -> PathBuf { self.node().join("deployment/pinned-config.json") }
    fn node_state(&self) -> PathBuf { self.node().join("state.json") }
    fn socket(&self) -> PathBuf { self.node().join("public/mini.sock") }
}

/// `/etc/mini/door.json`.
#[derive(Clone, Debug)]
struct DoorConfig {
    funding: u128,
    free_cap: usize,
    /// Of `free_cap`, the seats only an invite code can take: an uncoded free enrolment is
    /// admitted only while the free accounts made are fewer than `free_cap - invite_reserve`.
    /// 0 (the default) is the door without invite codes.
    invite_reserve: usize,
    /// The root-owned codes file (under the processor's root prefix); required when `invite_reserve > 0`.
    invite_codes: Option<PathBuf>,
    daily_cap: usize,
    per_run: usize,
    sponsor_floor: u128,
    link_ttl_s: u64,
    login_host: String,
    pay: Option<PayConfig>,
    /// The built-in story every member joins at enrolment (`story`: `{"author": "box", "name":
    /// "tale"}`): the author's account invites the member as a player and the member joins, so the
    /// tour's story door has a cell to move on. Absent: no story step.
    story: Option<StoryConfig>,
    /// The house's shared room every member joins at enrolment (`room`: `{"founder": "house",
    /// "name": "lobby"}`): the founder's account invites the member and the member joins, so the
    /// tour's Hermes step has the room the house summoned Hermes into. Absent: no room step.
    room: Option<StoryConfig>,
}

#[derive(Clone, Debug)]
struct StoryConfig {
    /// The hosted account that founded the story (`mini-s-AUTHOR`); only the author invites.
    author: String,
    name: String,
}

/// An atomic amount as a decimal token amount ("50000007", 6 -> "50.000007"; trailing zeros kept
/// off, a whole amount without a point).
fn decimal_tokens(atomic: &str, decimals: usize) -> Option<String> {
    if atomic.is_empty() || !atomic.bytes().all(|b| b.is_ascii_digit()) || decimals > 38 {
        return None;
    }
    let padded = format!("{atomic:0>width$}", width = decimals + 1);
    let (whole, frac) = padded.split_at(padded.len() - decimals);
    let whole = whole.trim_start_matches('0');
    let whole = if whole.is_empty() { "0" } else { whole };
    let frac = frac.trim_end_matches('0');
    Some(if frac.is_empty() { whole.to_owned() } else { format!("{whole}.{frac}") })
}

#[derive(Clone, Debug)]
struct PayConfig {
    enrol_pin: PathBuf,
    birth_context: Option<PathBuf>,
    network: String,
    /// The token's symbol on the page ("50.000007 DREGG"); `pay.symbol`, DREGG by default.
    symbol: String,
    /// The public RPC endpoint the stranger's BROWSER sends the payment to (the box has no egress
    /// and names it only); `pay.rpc`, by default the cluster's public endpoint for the network.
    rpc: String,
}

impl DoorConfig {
    fn load(path: &Path) -> Result<Self, String> {
        let v: Value = serde_json::from_slice(&std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?)
            .map_err(|e| format!("door config: {e}"))?;
        let known = ["version", "funding", "freeCap", "inviteReserve", "inviteCodes", "dailyCap", "perRun", "sponsorFloor", "linkTtlHours", "loginHost", "pay", "story", "room"];
        if let Some(k) = v.as_object().ok_or("door config is not an object")?.keys().find(|k| !known.contains(&k.as_str())) {
            return Err(format!("door config has an unknown key {k}"));
        }
        if v["version"] != 1 {
            return Err("door config version must be 1".into());
        }
        let nat = |k: &str, d: u64| -> Result<u64, String> {
            match &v[k] { Value::Null => Ok(d), n => n.as_u64().ok_or(format!("{k} is not a natural")) }
        };
        let big = |k: &str, d: u128| -> Result<u128, String> {
            match &v[k] { Value::Null => Ok(d), Value::String(s) => s.parse().map_err(|_| format!("{k} is not a decimal")), _ => Err(format!("{k} is a decimal string")) }
        };
        let pay = match &v["pay"] {
            Value::Null => None,
            p => Some(PayConfig {
                enrol_pin: PathBuf::from(p["enrolPin"].as_str().ok_or("pay.enrolPin")?),
                birth_context: p["birthContext"].as_str().map(PathBuf::from),
                network: match p["network"].as_str() {
                    Some(n @ ("mainnet" | "devnet")) => n.to_owned(),
                    _ => return Err("pay.network is mainnet or devnet".into()),
                },
                symbol: p["symbol"].as_str().filter(|s| !s.is_empty() && s.len() <= 12 && s.bytes().all(|b| b.is_ascii_alphanumeric())).unwrap_or("DREGG").to_owned(),
                rpc: match (p["rpc"].as_str(), p["network"].as_str()) {
                    (Some(url), _) if url.starts_with("https://") => url.to_owned(),
                    (Some(_), _) => return Err("pay.rpc is an https URL".into()),
                    (None, Some("devnet")) => "https://api.devnet.solana.com".to_owned(),
                    (None, _) => "https://solana-rpc.publicnode.com".to_owned(),
                },
            }),
        };
        let login_host = v["loginHost"].as_str().unwrap_or("demo.dregg.online").to_owned();
        if login_host.is_empty() || !login_host.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'.' || b == b'-') {
            return Err("loginHost is a host name".into());
        }
        let free_cap = nat("freeCap", 50)? as usize;
        let invite_reserve = nat("inviteReserve", 0)? as usize;
        if invite_reserve > free_cap {
            return Err(format!("inviteReserve {invite_reserve} exceeds freeCap {free_cap}"));
        }
        let invite_codes = match &v["inviteCodes"] {
            Value::Null => None,
            Value::String(p) if p.starts_with('/') && !p.contains("..") => Some(PathBuf::from(p)),
            _ => return Err("inviteCodes is an absolute path".into()),
        };
        if invite_reserve > 0 && invite_codes.is_none() {
            return Err("inviteReserve above 0 needs inviteCodes (the codes file)".into());
        }
        let word = |w: &str| !w.is_empty() && w.len() <= 32 && w.bytes().all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-');
        let story = match &v["story"] {
            Value::Null => None,
            st => match (st["author"].as_str(), st["name"].as_str()) {
                (Some(a), Some(n)) if word(a) && word(n) => Some(StoryConfig { author: a.to_owned(), name: n.to_owned() }),
                _ => return Err("story is {\"author\": WORD, \"name\": WORD} (lowercase letters, digits, -)".into()),
            },
        };
        let room = match &v["room"] {
            Value::Null => None,
            rm => match (rm["founder"].as_str(), rm["name"].as_str()) {
                (Some(f), Some(n)) if word(f) && word(n) => Some(StoryConfig { author: f.to_owned(), name: n.to_owned() }),
                _ => return Err("room is {\"founder\": WORD, \"name\": WORD} (lowercase letters, digits, -)".into()),
            },
        };
        Ok(DoorConfig {
            funding: big("funding", 1000)?,
            free_cap,
            invite_reserve,
            invite_codes,
            daily_cap: nat("dailyCap", 20)? as usize,
            per_run: nat("perRun", 4)?.max(1) as usize,
            sponsor_floor: big("sponsorFloor", 20_000)?,
            link_ttl_s: nat("linkTtlHours", 168)?.saturating_mul(3600),
            login_host,
            pay,
            story,
            room,
        })
    }
}

/// One line of the invite codes file (`inviteCodes`, root-owned, mode 0600). Comments (`#`) and
/// blank lines are kept as they are. A code line is `SERIAL CODE` (unspent) or
/// `SERIAL CODE used NAME REQUEST-ID AT` (struck): SERIAL is a decimal of 1 or more, unique; CODE
/// is 8 to 64 of A-Z a-z 0-9 -, unique. The struck line names the request that holds the code, so
/// a retry by the same request finds its own strike.
#[derive(Clone, Debug, PartialEq, Eq)]
enum CodeLine {
    Other(String),
    Code { serial: u32, code: String, used: Option<String> },
}

fn parse_codes(text: &str) -> Result<Vec<CodeLine>, String> {
    let mut out: Vec<CodeLine> = Vec::new();
    for (n, line) in text.lines().enumerate() {
        let t = line.trim();
        if t.is_empty() || t.starts_with('#') {
            out.push(CodeLine::Other(line.to_owned()));
            continue;
        }
        let mut w = t.split_whitespace();
        let (Some(serial), Some(code)) = (w.next(), w.next()) else { return Err(format!("line {}: want SERIAL CODE", n + 1)) };
        let serial: u32 = serial.parse().ok().filter(|s| *s >= 1).ok_or(format!("line {}: the serial is a decimal of 1 or more", n + 1))?;
        if !door::is_invite_code(code) {
            return Err(format!("line {}: the code is 8 to 64 of A-Z a-z 0-9 -", n + 1));
        }
        let rest: Vec<&str> = w.collect();
        let used = match rest.as_slice() {
            [] => None,
            ["used", name, request, at] if door::is_door_name(name) && door::is_request_id(request) && at.bytes().all(|b| b.is_ascii_digit()) => Some(format!("{name} {request} {at}")),
            _ => return Err(format!("line {}: after the code, nothing or `used NAME REQUEST-ID AT`", n + 1)),
        };
        if out.iter().any(|l| matches!(l, CodeLine::Code { serial: s, code: c, .. } if *s == serial || c == code)) {
            return Err(format!("line {}: a serial or code is repeated", n + 1));
        }
        out.push(CodeLine::Code { serial, code: code.to_owned(), used });
    }
    Ok(out)
}

fn render_codes(lines: &[CodeLine]) -> String {
    let mut out = String::new();
    for l in lines {
        match l {
            CodeLine::Other(t) => out.push_str(t),
            CodeLine::Code { serial, code, used: None } => out.push_str(&format!("{serial} {code}")),
            CodeLine::Code { serial, code, used: Some(u) } => out.push_str(&format!("{serial} {code} used {u}")),
        }
        out.push('\n');
    }
    out
}

/// What the codes file says of one code for one request.
#[derive(Debug, PartialEq, Eq)]
enum InviteState {
    Unknown,
    /// Struck by another request.
    Spent,
    /// Struck by this very request (a retry after a crash): its own reservation.
    Mine(u32),
    Unspent(u32),
}

/// One finished command.
struct Ran {
    ok: bool,
    stdout: String,
    stderr: String,
}

impl Ran {
    /// The diagnostic the operator reads in the log and a stranger's status: the first `error:`/
    /// `refused:`/`undecided:`/`usage:` line in full (to 4000 bytes, not the 300 that cut a
    /// `local process …/minidregg-client-consent ended before …` line mid-sentence), and the last
    /// line when it says something else (the child's own last words).
    fn why(&self) -> String {
        let cap = |l: &str| -> String { l.chars().take(4000).collect() };
        let first = self.stderr.lines().find(|l| ["error:", "refused:", "undecided:", "usage:"].iter().any(|w| l.starts_with(w)));
        let last = self.stderr.lines().rev().find(|l| !l.trim().is_empty());
        match (first, last) {
            (Some(f), Some(l)) if f != l => format!("{} | last stderr line: {}", cap(f), cap(l)),
            (Some(f), _) => cap(f),
            (None, Some(l)) => cap(l),
            (None, None) => "no diagnostic".to_owned(),
        }
    }
}

/// What the processor asks of the box. The real implementation runs the box's own scripts and
/// the session's own lines; the tests substitute a fake.
trait BoxOps {
    fn uid(&self, user: &str) -> Option<u32>;
    fn gid(&self, group: &str) -> Option<u32>;
    /// `render-authorized-keys.sh --on-box --roster $INFRA/friends` (an operator render: it
    /// creates a missing hosted account and its home).
    fn render(&self) -> Ran;
    /// One `mini shell` line in NAME's session, as `mini-s-NAME`.
    fn tenant_line(&self, name: &str, line: &str) -> Ran;
    /// One `mini` client command as `mini-s-NAME`.
    fn tenant_mini(&self, name: &str, args: &[String]) -> Ran;
    /// `mini-reenroll NAME` with the door's funding.
    fn reenroll(&self, name: &str, funding: u128) -> Ran;
    /// The sponsor's signed `credit` read.
    fn sponsor_credit(&self) -> Ran;
    /// Hand NAME's account a file in its own home (written by root, then given to the tenant).
    fn give(&self, name: &str, path: &Path, bytes: &[u8]) -> Result<(), String>;
    /// A fresh ssh-ed25519 public line whose secret is destroyed at once: the roster needs one key
    /// per account, a browser-only stranger has none, and nobody must ever log in with it.
    fn throwaway_key(&self) -> Result<String, String>;
}

struct RealBox {
    p: Paths,
}

fn run(mut cmd: Command) -> Ran {
    cmd.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped());
    match cmd.output() {
        Ok(o) => Ran {
            ok: o.status.success(),
            stdout: String::from_utf8_lossy(&o.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&o.stderr).into_owned(),
        },
        Err(e) => Ran { ok: false, stdout: String::new(), stderr: format!("error: cannot run {cmd:?}: {e}") },
    }
}

fn lookup(file: &str, name: &str, field: usize) -> Option<u32> {
    std::fs::read_to_string(file).ok()?.lines().find_map(|l| {
        let f: Vec<&str> = l.split(':').collect();
        (f.first() == Some(&name)).then(|| f.get(field)?.parse().ok()).flatten()
    })
}

impl RealBox {
    fn as_tenant(&self, name: &str) -> Command {
        let mut cmd = Command::new("/usr/bin/timeout");
        cmd.args(["--kill-after=5", "300", "/usr/bin/setpriv"])
            .arg(format!("--reuid=mini-s-{name}"))
            .arg(format!("--regid={TENANT_GROUP}"))
            .args(["--init-groups", "--reset-env", "--", "/usr/bin/env", "-i", "PATH=/usr/bin:/bin", "LANG=C.UTF-8"]);
        cmd.env_clear();
        cmd
    }
}

impl BoxOps for RealBox {
    fn uid(&self, user: &str) -> Option<u32> { lookup("/etc/passwd", user, 2) }
    fn gid(&self, group: &str) -> Option<u32> { lookup("/etc/group", group, 2) }
    fn render(&self) -> Ran {
        let mut cmd = Command::new(self.p.lib().join("infra/render-authorized-keys.sh"));
        cmd.arg("--on-box").arg("--roster").arg(self.p.friends());
        run(cmd)
    }
    fn tenant_line(&self, name: &str, line: &str) -> Ran {
        let home = self.p.home(name);
        let mut cmd = self.as_tenant(name);
        cmd.arg(format!("SSH_ORIGINAL_COMMAND={line}"))
            .arg(self.p.lib().join("mini-shell-ssh"))
            .arg(self.p.candidate().join("bin/mini"))
            .arg(self.p.candidate().join("bin/minidregg-host"))
            .arg(self.p.config())
            .arg(self.p.socket())
            .arg(home.join("workspace"))
            .arg(&home);
        run(cmd)
    }
    fn tenant_mini(&self, name: &str, args: &[String]) -> Ran {
        let mut cmd = self.as_tenant(name);
        cmd.arg(self.p.candidate().join("bin/mini")).args(args);
        run(cmd)
    }
    fn reenroll(&self, name: &str, funding: u128) -> Ran {
        let mut cmd = Command::new(self.p.lib().join("mini-reenroll"));
        cmd.env_clear().env("PATH", "/usr/sbin:/usr/bin:/sbin:/bin").env("MINI_REENROLL_FUNDING", funding.to_string()).arg(name);
        run(cmd)
    }
    fn sponsor_credit(&self) -> Ran {
        let node = self.p.node();
        let mut cmd = Command::new("/usr/sbin/runuser");
        cmd.env_clear()
            .args(["-u", "mini-core", "--", "/usr/bin/env", "-i", "PATH=/usr/bin:/bin", "LANG=C.UTF-8", "SSH_ORIGINAL_COMMAND=credit"])
            .arg(self.p.lib().join("mini-shell-ssh"))
            .arg(self.p.candidate().join("bin/mini"))
            .arg(self.p.candidate().join("bin/minidregg-host"))
            .arg(self.p.config())
            .arg(self.p.socket())
            .arg(node.join("sponsor"))
            .arg(node.join("sponsor-home"));
        run(cmd)
    }
    fn throwaway_key(&self) -> Result<String, String> {
        let dir = self.p.state().join("tmp");
        std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
        std::fs::set_permissions(&dir, std::os::unix::fs::PermissionsExt::from_mode(0o700)).map_err(|e| e.to_string())?;
        let file = dir.join(format!("web-only-{}", std::process::id()));
        let _ = std::fs::remove_file(&file);
        let _ = std::fs::remove_file(file.with_extension("pub"));
        let ran = run({ let mut c = Command::new("ssh-keygen"); c.arg("-q").arg("-t").arg("ed25519").arg("-N").arg("").arg("-C").arg("web-only").arg("-f").arg(&file); c });
        let public = std::fs::read_to_string(file.with_extension("pub"));
        let _ = std::fs::remove_file(&file);
        let _ = std::fs::remove_file(file.with_extension("pub"));
        if !ran.ok {
            return Err(format!("ssh-keygen: {}", ran.why()));
        }
        door::ssh_ed25519(&public.map_err(|e| e.to_string())?)
    }
    fn give(&self, name: &str, path: &Path, bytes: &[u8]) -> Result<(), String> {
        let uid = self.uid(&format!("mini-s-{name}")).ok_or("no hosted account")?;
        let gid = self.gid(TENANT_GROUP).ok_or("no tenant group")?;
        let parent = path.parent().ok_or("no parent")?;
        for dir in [parent] {
            if !dir.exists() {
                std::fs::create_dir_all(dir).map_err(|e| e.to_string())?;
            }
            chown(dir, uid, gid)?;
            std::fs::set_permissions(dir, std::fs::Permissions::from_mode(0o700)).map_err(|e| e.to_string())?;
        }
        write_atomic(path, bytes, 0o600)?;
        chown(path, uid, gid)
    }
}

fn chown(path: &Path, uid: u32, gid: u32) -> Result<(), String> {
    use std::os::unix::ffi::OsStrExt;
    let c = std::ffi::CString::new(path.as_os_str().as_bytes()).map_err(|e| e.to_string())?;
    if unsafe { libc::lchown(c.as_ptr(), uid, gid) } != 0 {
        return Err(format!("chown {}: {}", path.display(), std::io::Error::last_os_error()));
    }
    Ok(())
}

/// Temp file, fsync, rename, fsync the directory.
/// 32 random bytes as 43 base64url characters: the token shape `mini-web-spawn` accepts.
fn web_login_code() -> Result<String, String> {
    const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
    let bytes = door::random(32)?;
    let mut out = String::new();
    for chunk in bytes.chunks(3) {
        let mut n = 0u32;
        for (i, b) in chunk.iter().enumerate() {
            n |= (*b as u32) << (16 - 8 * i);
        }
        for i in 0..4 {
            if i <= chunk.len() {
                out.push(ALPHABET[((n >> (18 - 6 * i)) & 63) as usize] as char);
            }
        }
    }
    Ok(out)
}

/// A world's identity. `run.sh upgrade` rewrites the pinned config (new binary bindings, same Store),
/// so the config digest names a world only until the next in-place upgrade; the node's `state.json`
/// carries `createdUtc`, written once by `run.sh init` and kept by every upgrade, and a re-genesis
/// writes a new one. That stamp names the world; the config digest is the fallback for a node whose
/// state file is unreadable.
fn world_id(config: &[u8], state: Option<&[u8]>) -> String {
    let created = state
        .and_then(|bytes| serde_json::from_slice::<Value>(bytes).ok())
        .and_then(|v| v["createdUtc"].as_str().filter(|c| !c.is_empty()).map(str::to_owned));
    match created {
        Some(stamp) => sha256_hex(format!("minidregg-world-v1\n{stamp}").as_bytes()),
        None => sha256_hex(config),
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    use sha2::Digest;
    sha2::Sha256::digest(bytes).iter().map(|b| format!("{b:02x}")).collect()
}

fn write_atomic(path: &Path, bytes: &[u8], mode: u32) -> Result<(), String> {
    use std::io::Write;
    let dir = path.parent().ok_or("no parent")?;
    let tmp = dir.join(format!(".{}.tmp", path.file_name().and_then(|n| n.to_str()).unwrap_or("x")));
    let _ = std::fs::remove_file(&tmp);
    let mut f = std::fs::OpenOptions::new().write(true).create_new(true).mode(mode).custom_flags(libc::O_NOFOLLOW)
        .open(&tmp).map_err(|e| format!("{}: {e}", tmp.display()))?;
    f.write_all(bytes).and_then(|_| f.sync_all()).map_err(|e| format!("{}: {e}", tmp.display()))?;
    std::fs::set_permissions(&tmp, std::fs::Permissions::from_mode(mode)).map_err(|e| e.to_string())?;
    std::fs::rename(&tmp, path).map_err(|e| format!("{}: {e}", path.display()))?;
    std::fs::File::open(dir).and_then(|d| d.sync_all()).map_err(|e| e.to_string())
}

fn read_json(path: &Path) -> Option<Value> {
    serde_json::from_slice(&std::fs::read(path).ok()?).ok()
}

fn b58(bytes: &[u8]) -> String {
    const A: &[u8] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    let mut digits: Vec<u8> = Vec::new();
    for &b in bytes {
        let mut carry = b as u32;
        for d in digits.iter_mut() {
            carry += (*d as u32) << 8;
            *d = (carry % 58) as u8;
            carry /= 58;
        }
        while carry > 0 {
            digits.push((carry % 58) as u8);
            carry /= 58;
        }
    }
    let zeros = bytes.iter().take_while(|b| **b == 0).count();
    std::iter::repeat('1').take(zeros).chain(digits.iter().rev().map(|d| A[*d as usize] as char)).collect()
}

fn b64(bytes: &[u8]) -> String {
    const T: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::new();
    for chunk in bytes.chunks(3) {
        let n = chunk.iter().enumerate().fold(0u32, |n, (i, b)| n | (u32::from(*b) << (16 - 8 * i)));
        for i in 0..=chunk.len() {
            out.push(T[((n >> (18 - 6 * i)) & 63) as usize] as char);
        }
        for _ in chunk.len()..3 {
            out.push('=');
        }
    }
    out
}

fn unhex(text: &str) -> Option<Vec<u8>> {
    (text.len() % 2 == 0).then(|| (0..text.len()).step_by(2).map(|i| u8::from_str_radix(&text[i..i + 2], 16).ok()).collect())?
}

struct Processor<O: BoxOps> {
    p: Paths,
    cfg: DoorConfig,
    ops: O,
    now: u64,
    /// The sponsor's balance as read this run (read at most once).
    sponsor: Option<Result<u128, String>>,
    log: Vec<String>,
}

impl<O: BoxOps> Processor<O> {
    fn say(&mut self, line: String) {
        eprintln!("mini-door-process: {line}");
        self.log.push(line);
    }

    fn request_path(&self, id: &str) -> PathBuf { self.p.state().join("requests").join(format!("{id}.json")) }

    fn requests(&self) -> Vec<Value> {
        let Ok(entries) = std::fs::read_dir(self.p.state().join("requests")) else { return Vec::new() };
        let mut out: Vec<Value> = entries.filter_map(|e| read_json(&e.ok()?.path())).collect();
        out.sort_by_key(|v| (v["at"].as_u64().unwrap_or(0), v["id"].as_str().unwrap_or("").to_owned()));
        out
    }

    fn save(&mut self, r: &mut Value) -> Result<(), String> {
        r["updated"] = json!(self.now);
        let id = r["id"].as_str().ok_or("request without id")?.to_owned();
        write_atomic(&self.request_path(&id), &serde_json::to_vec_pretty(r).map_err(|e| e.to_string())?, 0o600)?;
        self.publish_status(r)
    }

    /// The stranger's view: root-owned, readable by the form's group, never the secrets.
    fn publish_status(&self, r: &Value) -> Result<(), String> {
        let mut v = json!({"type":door::STATUS_TYPE,"id":r["id"],"phase":r["phase"],"name":r["name"],"route":r["route"]});
        for k in ["detail", "linkCode", "sign", "payment", "webLogin", "webOnly", "funding", "researchConsent", "story", "room"] {
            if !r[k].is_null() {
                v[k] = r[k].clone();
            }
        }
        if r["webOnly"] != true && matches!(r["phase"].as_str(), Some("enrolled" | "sign" | "signed" | "awaiting-payment" | "paid" | "keyed" | "account")) {
            v["login"] = json!(format!("mini-s-{}@{}", r["name"].as_str().unwrap_or(""), self.cfg.login_host));
        }
        self.publish(&format!("{}.json", r["id"].as_str().unwrap_or("x")), &v)
    }

    fn publish(&self, name: &str, v: &Value) -> Result<(), String> {
        let path = self.p.status().join(name);
        write_atomic(&path, &serde_json::to_vec_pretty(v).map_err(|e| e.to_string())?, 0o640)?;
        if let Some(gid) = self.ops.gid(DOOR_USER) {
            if self.p.root == Path::new("/") {
                chown(&path, 0, gid)?;
            }
        }
        Ok(())
    }

    fn refuse(&mut self, r: &mut Value, why: &str) -> Result<(), String> {
        if !r["inviteSerial"].is_null() && r["phase"] != "enrolled" {
            // Refused after the code was struck, never enrolled: the code goes back to the operator's pool.
            self.release_invite(r["id"].as_str().unwrap_or(""))?;
            r["inviteSerial"] = Value::Null;
        }
        r["phase"] = json!("refused");
        r["detail"] = json!(why);
        self.say(format!("request {} refused: {why}", r["id"].as_str().unwrap_or("")));
        self.save(r)
    }

    fn reject_file(&mut self, file: &Path, why: &str) {
        let dir = self.p.state().join("rejected");
        let name = file.file_name().and_then(|n| n.to_str()).unwrap_or("x").to_owned();
        let record = json!({"file":name,"reason":why,"at":self.now});
        let _ = std::fs::create_dir_all(&dir)
            .map_err(|e| e.to_string())
            .and_then(|_| write_atomic(&dir.join(format!("{}-{name}", self.now)), record.to_string().as_bytes(), 0o600));
        let _ = std::fs::remove_file(file);
        self.say(format!("rejected {name}: {why}"));
    }

    // ── names, keys and caps ───────────────────────────────────────────────────────────────

    fn roster_keys(&self) -> HashMap<String, String> {
        let mut out = HashMap::new();
        for dir in [self.p.friends(), self.p.door_friends()] {
            let Ok(entries) = std::fs::read_dir(&dir) else { continue };
            for e in entries.flatten() {
                let path = e.path();
                let Some(name) = path.file_name().and_then(|n| n.to_str()).and_then(|n| n.strip_suffix(".pub")) else { continue };
                if let Ok(text) = std::fs::read_to_string(&path) {
                    for line in text.lines().filter(|l| !l.trim_start().starts_with('#')) {
                        if let Some(blob) = line.split_whitespace().nth(1) {
                            out.insert(blob.to_owned(), name.to_owned());
                        }
                    }
                }
                out.insert(format!("name:{name}"), name.to_owned());
            }
        }
        out
    }

    fn day(&self) -> u64 { self.now / 86_400 }

    /// Accounts the door has made or is making (not refused, past `queued`), other than `except`.
    fn counted(&self, route: Option<&str>, today: bool, except: Option<&str>) -> usize {
        self.requests().iter().filter(|r| {
            r["phase"] != "refused"
                && except.is_none_or(|id| r["id"] != id)
                && route.is_none_or(|w| r["route"] == w)
                && (!today || r["day"].as_u64() == Some(self.day()))
                && r["phase"] != "queued"
        }).count()
    }

    fn sponsor_balance(&mut self) -> Result<u128, String> {
        if self.sponsor.is_none() {
            let ran = self.ops.sponsor_credit();
            let parsed = if ran.ok {
                ran.stdout.lines().find_map(|l| l.strip_prefix("credit ")?.split_whitespace().next()?.parse::<u128>().ok())
                    .ok_or_else(|| "the sponsor's credit read printed no balance".to_owned())
            } else {
                Err(format!("the sponsor's credit read failed: {}", ran.why()))
            };
            self.sponsor = Some(parsed);
        }
        self.sponsor.clone().unwrap()
    }

    /// Why the free route is closed, if it is.
    /// `coded`: the request holds (or is claiming) an invite code, so the reserve is open to it.
    fn free_closed(&mut self, except: Option<&str>, coded: bool) -> Option<String> {
        let made = self.counted(Some("free"), false, except);
        if made >= self.cfg.free_cap {
            return Some(format!("all {} free accounts are taken", self.cfg.free_cap));
        }
        if !coded && made >= self.cfg.free_cap - self.cfg.invite_reserve {
            return Some(format!("open-seats-gone: the open free accounts are taken; {} remain for people with an invite code", self.cfg.free_cap - made));
        }
        if self.counted(None, true, except) >= self.cfg.daily_cap {
            return Some(format!("today's {} accounts are taken; try tomorrow", self.cfg.daily_cap));
        }
        match self.sponsor_balance() {
            Ok(b) if b >= self.cfg.sponsor_floor.saturating_add(self.cfg.funding) => None,
            Ok(b) => Some(format!("sponsorBelowFloor: the sponsor's balance {b} is below the floor {} plus one account's funding {}", self.cfg.sponsor_floor, self.cfg.funding)),
            Err(e) => Some(e),
        }
    }

    // ── invite codes ───────────────────────────────────────────────────────────────────────

    fn codes_path(&self) -> Result<PathBuf, String> {
        self.cfg.invite_codes.as_ref().map(|p| self.p.at(&p.to_string_lossy())).ok_or_else(|| "this door has no inviteCodes file".to_owned())
    }

    /// The codes file, after the checks a root secret needs: a regular file (not a link), no
    /// group or other access, and (on the real root) owned by root.
    fn load_codes(&self) -> Result<Vec<CodeLine>, String> {
        use std::os::unix::fs::MetadataExt;
        let path = self.codes_path()?;
        let meta = std::fs::symlink_metadata(&path).map_err(|e| format!("inviteCodes {}: {e}", path.display()))?;
        if !meta.file_type().is_file() {
            return Err(format!("inviteCodes {} is not a regular file", path.display()));
        }
        if meta.mode() & 0o077 != 0 {
            return Err(format!("inviteCodes {} must be mode 0600 (it is {:o})", path.display(), meta.mode() & 0o7777));
        }
        if self.p.root == Path::new("/") && meta.uid() != 0 {
            return Err(format!("inviteCodes {} must be owned by root", path.display()));
        }
        parse_codes(&std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?).map_err(|e| format!("inviteCodes {}: {e}", path.display()))
    }

    fn save_codes(&self, lines: &[CodeLine]) -> Result<(), String> {
        write_atomic(&self.codes_path()?, render_codes(lines).as_bytes(), 0o600)
    }

    fn invite_state(&self, code: &str, request: &str) -> Result<InviteState, String> {
        Ok(match self.load_codes()?.iter().find_map(|l| match l { CodeLine::Code { serial, code: c, used } if c == code => Some((*serial, used.clone())), _ => None }) {
            None => InviteState::Unknown,
            Some((serial, None)) => InviteState::Unspent(serial),
            Some((serial, Some(u))) if u.split(' ').nth(1) == Some(request) => InviteState::Mine(serial),
            Some(_) => InviteState::Spent,
        })
    }

    /// Strike the code for this request: the file is rewritten whole and atomically (temp, fsync,
    /// rename), BEFORE the request's first world effect, so a code never admits two people. Striking
    /// again for the same request is a no-op.
    fn strike_invite(&self, serial: u32, name: &str, request: &str) -> Result<(), String> {
        let mut lines = self.load_codes()?;
        for l in lines.iter_mut() {
            if let CodeLine::Code { serial: s, used, .. } = l {
                if *s == serial {
                    match used {
                        None => *used = Some(format!("{name} {request} {}", self.now)),
                        Some(u) if u.split(' ').nth(1) == Some(request) => return Ok(()),
                        Some(_) => return Err(format!("invite serial {serial} was struck by another request")),
                    }
                }
            }
        }
        self.save_codes(&lines)
    }

    /// A request refused after it struck a code never enrolled: the code goes back.
    fn release_invite(&self, request: &str) -> Result<(), String> {
        let mut lines = self.load_codes()?;
        let mut changed = false;
        for l in lines.iter_mut() {
            if let CodeLine::Code { used, .. } = l {
                if used.as_ref().is_some_and(|u| u.split(' ').nth(1) == Some(request)) {
                    *used = None;
                    changed = true;
                }
            }
        }
        if changed { self.save_codes(&lines) } else { Ok(()) }
    }

    // ── intake ─────────────────────────────────────────────────────────────────────────────

    fn intake(&mut self) -> Result<(), String> {
        let Some(owner) = self.ops.uid(DOOR_USER) else { return Err(format!("no account {DOOR_USER}")) };
        let files = door::spool_list(&self.p.queue())?;
        for file in files {
            let bytes = match door::spool_read(&file, owner) {
                Ok(b) => b,
                Err(e) => { self.reject_file(&file, &e); continue; }
            };
            let request = match Request::parse(&bytes) {
                Ok(r) => r,
                Err(e) => { self.reject_file(&file, &e); continue; }
            };
            if file.file_name().and_then(|n| n.to_str()) != Some(request.file_name().as_str()) {
                self.reject_file(&file, "the file name does not match its request");
                continue;
            }
            self.admit(request, &file)?;
        }
        Ok(())
    }

    fn admit(&mut self, request: Request, file: &Path) -> Result<(), String> {
        let existing = read_json(&self.request_path(request.id()));
        match request {
            Request::Join { id, at, name, ssh_key, discord, route, research, invite } => {
                if existing.is_some() {
                    self.reject_file(file, "a request with this id exists");
                    return Ok(());
                }
                let mut r = json!({"id":id,"at":at,"day":self.day(),"name":name,"sshKey":ssh_key,"discord":discord,"route":route.word(),"research":research,"invite":invite,"phase":"queued"});
                std::fs::remove_file(file).map_err(|e| e.to_string())?;
                let keys = self.roster_keys();
                let blob = ssh_key.split(' ').nth(1).unwrap_or("").to_owned();
                let taken_by_request = self.requests().iter().any(|o| o["name"] == name && o["phase"] != "refused");
                if keys.contains_key(&format!("name:{name}")) || taken_by_request || self.ops.uid(&format!("mini-s-{name}")).is_some() {
                    return self.refuse(&mut r, "that name is taken; ask again with another");
                }
                if keys.contains_key(&blob) {
                    return self.refuse(&mut r, "that ssh key already has an account on this box");
                }
                if route == Route::Paid && self.cfg.pay.is_none() {
                    return self.refuse(&mut r, "this box does not take payments");
                }
                if self.counted(None, true, None) >= self.cfg.daily_cap {
                    return self.refuse(&mut r, &format!("today's {} accounts are taken; try tomorrow", self.cfg.daily_cap));
                }
                self.say(format!("request {id} accepted for {name} ({})", route.word()));
                self.save(&mut r)
            }
            Request::Sign { id, signature, .. } => {
                std::fs::remove_file(file).map_err(|e| e.to_string())?;
                match existing {
                    Some(mut r) if r["phase"] == "sign" => {
                        r["signature"] = json!(signature);
                        r["phase"] = json!("signed");
                        r["detail"] = Value::Null;
                        self.save(&mut r)
                    }
                    _ => { self.say(format!("sign for {id} ignored: not waiting for a signature")); Ok(()) }
                }
            }
            Request::Paid { id, transaction, .. } => {
                std::fs::remove_file(file).map_err(|e| e.to_string())?;
                match existing {
                    Some(mut r) if r["phase"] == "awaiting-payment" => {
                        r["transaction"] = json!(transaction);
                        r["phase"] = json!("paid");
                        r["detail"] = json!("payment reported; waiting for the box's payment watcher to see it final");
                        self.save(&mut r)
                    }
                    _ => { self.say(format!("paid for {id} ignored: not waiting for a payment")); Ok(()) }
                }
            }
        }
    }

    // ── progress ───────────────────────────────────────────────────────────────────────────

    fn progress(&mut self) -> Result<(), String> {
        let mut done = 0;
        for mut r in self.requests() {
            if done >= self.cfg.per_run {
                break;
            }
            let phase = r["phase"].as_str().unwrap_or("").to_owned();
            if matches!(phase.as_str(), "refused" | "enrolled") {
                continue;
            }
            if matches!(phase.as_str(), "sign" | "awaiting-payment") {
                if self.now.saturating_sub(r["at"].as_u64().unwrap_or(0)) > PAID_TTL_S {
                    self.refuse(&mut r, "the payment was not finished within 7 days; the account stays, unfunded")?;
                }
                continue;
            }
            done += 1;
            // Steps until the request waits for the stranger, finishes, or a step fails.
            for _ in 0..8 {
                let before = r["phase"].clone();
                if let Err(e) = self.step(&mut r) {
                    r["detail"] = json!(format!("the box will retry: {e}"));
                    self.say(format!("request {}: {e}", r["id"].as_str().unwrap_or("")));
                    self.save(&mut r)?;
                    break;
                }
                if r["phase"] == before || matches!(r["phase"].as_str(), Some("refused" | "enrolled" | "sign" | "awaiting-payment")) {
                    break;
                }
            }
        }
        Ok(())
    }

    fn step(&mut self, r: &mut Value) -> Result<(), String> {
        let name = r["name"].as_str().ok_or("request without name")?.to_owned();
        let home = self.p.home(&name);
        match r["phase"].as_str().unwrap_or("") {
            "queued" => {
                if r["route"] == "free" {
                    let id = r["id"].as_str().unwrap_or("").to_owned();
                    let invite = r["invite"].as_str().map(str::to_owned);
                    let mut serial = None;
                    if let Some(code) = &invite {
                        if self.cfg.invite_reserve == 0 {
                            return self.refuse(r, "invite-unknown: this door takes no invite codes");
                        }
                        match self.invite_state(code, &id)? {
                            InviteState::Unknown => return self.refuse(r, "invite-unknown: that invite code is not one this door issued"),
                            InviteState::Spent => return self.refuse(r, "invite-spent: that invite code has already been used"),
                            InviteState::Mine(s) | InviteState::Unspent(s) => serial = Some(s),
                        }
                    }
                    // The seat check comes before the strike: a refusal for seats burns no code.
                    if let Some(why) = self.free_closed(Some(&id), serial.is_some()) {
                        return self.refuse(r, &why);
                    }
                    if let Some(s) = serial {
                        // Struck before the first world effect (the roster entry below); a crash
                        // after this line finds the request's own strike on the retry.
                        self.strike_invite(s, &name, &id)?;
                        r["inviteSerial"] = json!(s);
                        r["invite"] = Value::Null;
                    }
                }
                if r["sshKey"].as_str().unwrap_or("").is_empty() {
                    // Browser-only: the roster line is a key nobody holds; the account has no ssh login.
                    r["sshKey"] = json!(self.ops.throwaway_key()?);
                    r["webOnly"] = json!(true);
                }
                let entry = self.p.door_friends().join(format!("{name}.pub"));
                let text = format!("# door request {}{}\n{} {name}\n", r["id"].as_str().unwrap_or(""), if r["webOnly"] == true { " (web-only: the secret of this login key was destroyed)" } else { "" }, r["sshKey"].as_str().unwrap_or(""));
                std::fs::create_dir_all(self.p.door_friends()).map_err(|e| e.to_string())?;
                write_atomic(&entry, text.as_bytes(), 0o644)?;
                let ran = self.ops.render();
                if !ran.ok {
                    return Err(format!("render-authorized-keys.sh: {}", ran.why()));
                }
                if self.ops.uid(&format!("mini-s-{name}")).is_none() || !home.is_dir() {
                    return Err(format!("the render did not create mini-s-{name} and its home"));
                }
                r["phase"] = json!("account");
                self.save(r)
            }
            "account" => {
                if !home.join("keys/mini.key").exists() {
                    let ran = self.ops.tenant_line(&name, "keygen mini.key");
                    if !ran.ok {
                        return Err(format!("keygen: {}", ran.why()));
                    }
                }
                if !home.join("keys/mini.key.pub").exists() {
                    return Err("keygen left no keys/mini.key.pub".into());
                }
                r["phase"] = json!("keyed");
                self.save(r)
            }
            "keyed" if r["route"] == "free" => {
                // The caps are checked again at the one step that spends the sponsor's credit.
                let id = r["id"].as_str().unwrap_or("").to_owned();
                if let Some(why) = self.free_closed(Some(&id), !r["inviteSerial"].is_null()) {
                    return self.refuse(r, &why);
                }
                let ran = self.ops.reenroll(&name, self.cfg.funding);
                let subject = ran.stdout.lines().find_map(|l| {
                    let mut w = l.split_whitespace();
                    (w.next() == Some(name.as_str())).then(|| w.next().map(str::to_owned)).flatten()
                });
                let Some(subject) = subject.filter(|s| ran.ok && !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit())) else {
                    return Err(format!("mini-reenroll: {}", ran.why()));
                };
                // What the box funded this account with, for the stranger's status page.
                r["funding"] = json!(self.cfg.funding.to_string());
                if !home.join("workspace/workspace.json").exists() {
                    let ran = self.ops.tenant_line(&name, &format!("init mini.key {subject}"));
                    if !ran.ok {
                        return Err(format!("init: {}", ran.why()));
                    }
                }
                self.sponsor = None; // the balance moved
                r["subject"] = json!(subject);
                self.enrolled(r)
            }
            "keyed" => {
                let pay = self.cfg.pay.clone().ok_or("this box no longer takes payments")?;
                self.ops.give(&name, &home.join("door/ssh.pub"), format!("{}\n", r["sshKey"].as_str().unwrap_or("")).as_bytes())?;
                let ran = self.ops.tenant_mini(&name, &self.join_args(&name, &pay, None));
                if !ran.ok {
                    return Err(format!("join --solana: {}", ran.why()));
                }
                let quote = read_json(&home.join("detached-quote.json")).ok_or("join left no detached quote")?;
                let message = std::fs::read(home.join("sshsig-message.bin")).map_err(|e| format!("statement: {e}"))?;
                r["sign"] = json!({"message":b64(&message),"namespace":"dregg-enrol@v2","expiryHour":quote["expiryHour"].as_str().and_then(|h| h.parse::<u64>().ok())});
                r["phase"] = json!("sign");
                r["detail"] = Value::Null;
                self.save(r)
            }
            "signed" => {
                let pay = self.cfg.pay.clone().ok_or("this box no longer takes payments")?;
                let signature = r["signature"].as_str().unwrap_or("").to_owned();
                self.ops.give(&name, &home.join("door/ssh.sig"), signature.as_bytes())?;
                let ran = self.ops.tenant_mini(&name, &self.join_args(&name, &pay, Some(&home.join("door/ssh.sig"))));
                r["signature"] = Value::Null;
                if !ran.ok {
                    let why = ran.why();
                    // An expired quote is requoted; a signature that does not verify is asked for again.
                    r["phase"] = json!(if why.contains("expired") { "keyed" } else { "sign" });
                    r["detail"] = json!(format!("not accepted: {why}"));
                    return self.save(r);
                }
                let payment = read_json(&home.join("latest-payment.json")).ok_or("join left no payment record")?;
                let recipient = payment["enrolAddress"].as_str().and_then(unhex).map(|b| b58(&b)).ok_or("payment record lacks its recipient")?;
                // The wallet page builds the transfer from these: the mint and token program the pin
                // names (base58, as the cluster spells them), the token's decimals, and the RPC the
                // browser sends to. The paste path reads the same recipient, amount and memo.
                let mint = payment["mint"].as_str().and_then(unhex).map(|b| b58(&b)).ok_or("payment record lacks its mint")?;
                let token_program = payment["tokenProgram"].as_str().and_then(unhex).map(|b| b58(&b)).ok_or("payment record lacks its token program")?;
                let decimals = match &payment["quote"]["decimals"] { Value::String(s) => s.clone(), Value::Number(n) => n.to_string(), _ => return Err("payment record lacks the token's decimals".into()) };
                let tokens = payment["amountAtomic"].as_str().and_then(|a| decimal_tokens(a, decimals.parse().ok()?)).map(|t| format!("{t} {}", pay.symbol));
                // The quote's processing-chain hour when `mini join` checked it, and when that was:
                // the page refuses to send once the expiry hour has passed (a late memo is a pending
                // claim, not an enrolment).
                r["payment"] = json!({"recipient":recipient,"amountAtomic":payment["amountAtomic"],"amountTokens":tokens,"memo":payment["memo"],
                    "expiryHour":r["sign"]["expiryHour"],"asOfHour":payment["asOfHour"],"quotedAt":self.now,"network":pay.network,
                    "mint":mint,"tokenProgram":token_program,"decimals":decimals,"rpc":pay.rpc});
                r["phase"] = json!("awaiting-payment");
                r["detail"] = Value::Null;
                self.save(r)
            }
            "paid" => {
                let pay = self.cfg.pay.clone().ok_or("this box no longer takes payments")?;
                let mut args = self.common_args(&name, &pay);
                args.extend(["--wait".into(), "--signature".into(), r["transaction"].as_str().unwrap_or("").into(),
                    "--timeout".into(), "5".into()]);
                if let Some(context) = &pay.birth_context {
                    args.extend(["--birth-context".into(), context.display().to_string()]);
                }
                let ran = self.ops.tenant_mini(&name, &args);
                if ran.ok {
                    return self.enrolled(r);
                }
                let why = ran.why();
                if why.contains("negative journal") || why.contains("differs from retained") || why.contains("obtain a new renewal quote") {
                    return self.refuse(r, &format!("the payment did not enrol this account: {why}. Ember can comp a journalled payment."));
                }
                if self.now.saturating_sub(r["at"].as_u64().unwrap_or(0)) > PAID_TTL_S {
                    return self.refuse(r, &format!("the payment was not seen within 7 days: {why}"));
                }
                r["detail"] = json!(format!("waiting: {why}"));
                self.save(r)
            }
            other => Err(format!("unknown phase {other}")),
        }
    }

    fn common_args(&self, name: &str, _pay: &PayConfig) -> Vec<String> {
        let c = self.p.candidate();
        vec!["--socket".into(), self.p.socket().display().to_string(), "join".into(), "--memo-version".into(), "v2".into(),
            "--host".into(), c.join("bin/minidregg-host").display().to_string(), "--config".into(), self.p.config().display().to_string(),
            "--dir".into(), self.p.home(name).display().to_string()]
    }

    fn join_args(&self, name: &str, pay: &PayConfig, signature: Option<&Path>) -> Vec<String> {
        let home = self.p.home(name);
        let mut args = self.common_args(name, pay);
        // --enrol (the published pin) is for --solana only.
        args.extend(["--solana".into(), "--enrol".into(), pay.enrol_pin.display().to_string(), "--key".into(), home.join("keys/mini.key").display().to_string(),
            "--next-public".into(), home.join("keys/mini.key.next.pub").display().to_string(),
            "--ssh-public".into(), home.join("door/ssh.pub").display().to_string(), "--name".into(), name.into()]);
        if let Some(sig) = signature {
            args.extend(["--ssh-signature".into(), sig.display().to_string()]);
        }
        args
    }

    /// One declared-open cell with one scalar, as the member's own turns. A retried tick resumes:
    /// the cell exists, or the attempt was sealed (then `retry` sends the exact call again and
    /// reads its decided outcome, never a second write).
    fn write_fact(&mut self, name: &str, reference: &str, attempt: &str, lines: [String; 3]) -> Result<(), String> {
        let ws = self.p.home(name).join("workspace");
        let [create, invoke, submit] = lines;
        let mut steps: Vec<String> = Vec::new();
        if ws.join("attempts").join(attempt).exists() {
            steps.push(format!("retry {attempt}"));
        } else {
            if !ws.join("refs").join(format!("{reference}.json")).exists() {
                steps.push(create);
            }
            steps.push(invoke);
            steps.push(submit);
        }
        for line in &steps {
            let ran = self.ops.tenant_line(name, line);
            if !ran.ok {
                return Err(format!("{reference} fact ({line}): {}", ran.why()));
            }
        }
        Ok(())
    }

    fn enrolled(&mut self, r: &mut Value) -> Result<(), String> {
        let name = r["name"].as_str().unwrap_or("").to_owned();
        if r["researchConsent"].is_null() {
            // The member's research-consent fact, written as the member's own turns (the tenant
            // path every enrolment step uses): `research-consent` field 1 = 1 (CC0) or 0 (none).
            let cc0 = r["research"] == true;
            self.write_fact(&name, door::RESEARCH_CONSENT_REF, door::RESEARCH_CONSENT_ATTEMPT, door::research_consent_lines(cc0))?;
            r["researchConsent"] = json!(if cc0 { "cc0" } else { "none" });
        }
        if let (Some(serial), true) = (r["inviteSerial"].as_u64(), r["inviteFact"].is_null()) {
            // A member admitted with an invite code carries `invite` field 1 = the code's serial
            // (never the code). An uncoded member has no `invite` reference.
            self.write_fact(&name, door::INVITE_REF, door::INVITE_ATTEMPT, door::invite_lines(serial as u32))?;
            r["inviteFact"] = json!(serial);
        }
        if r["discord"] == true && r["linkCode"].is_null() {
            let code = door::new_link_code()?;
            let mut links = self.links();
            links["codes"][&code] = json!({"name":r["name"],"request":r["id"],"expires":self.now + self.cfg.link_ttl_s});
            self.save_links(&links)?;
            r["linkCode"] = json!(code);
        }
        if r["webLogin"].is_null() {
            // The browser session's one-time code: the processor is the only writer of identities,
            // so the gateway can only exchange what was written here (never mint one itself).
            let code = web_login_code()?;
            let dir = self.p.web_logins();
            std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
            if self.p.root == Path::new("/") {
                std::fs::set_permissions(&dir, std::os::unix::fs::PermissionsExt::from_mode(0o700)).map_err(|e| e.to_string())?;
                if let Some(parent) = dir.parent() {
                    let _ = std::fs::set_permissions(parent, std::os::unix::fs::PermissionsExt::from_mode(0o700));
                }
            }
            let record = json!({"name": r["name"], "request": r["id"], "expires": self.now + self.cfg.link_ttl_s});
            write_atomic(&dir.join(format!("{}.json", sha256_hex(code.as_bytes()))), &serde_json::to_vec(&record).map_err(|e| e.to_string())?, 0o600)?;
            r["webLogin"] = json!(format!("https://{}/login/{code}", self.cfg.login_host));
        }
        r["phase"] = json!("enrolled");
        r["detail"] = json!("your account is ready");
        r["transaction"] = Value::Null;
        self.say(format!("request {} enrolled {}", r["id"].as_str().unwrap_or(""), r["name"].as_str().unwrap_or("")));
        self.save(r)
    }

    // ── Discord links ──────────────────────────────────────────────────────────────────────

    fn links(&self) -> Value {
        read_json(&self.p.state().join("links.json")).unwrap_or_else(|| json!({"codes":{},"applied":{}}))
    }

    fn save_links(&self, v: &Value) -> Result<(), String> {
        write_atomic(&self.p.state().join("links.json"), &serde_json::to_vec_pretty(v).map_err(|e| e.to_string())?, 0o600)
    }

    fn apply_links(&mut self) -> Result<(), String> {
        let dir = self.p.links();
        if !dir.exists() {
            return Ok(());
        }
        let Some(owner) = self.ops.uid(DISCORD_USER) else { return Ok(()) };
        for file in door::spool_list(&dir)? {
            let link = match door::spool_read(&file, owner).and_then(|b| Link::parse(&b)) {
                Ok(l) if file.file_name().and_then(|n| n.to_str()) == Some(l.file_name().as_str()) => l,
                Ok(_) => { self.reject_file(&file, "the file name does not match its link"); continue; }
                Err(e) => { self.reject_file(&file, &e); continue; }
            };
            let result = self.link(&link);
            let mut links = self.links();
            links["applied"][&link.interaction] = json!({"user":link.user,"result":result.clone(),"at":self.now});
            if result.starts_with("linked") {
                if let Some(codes) = links["codes"].as_object_mut() {
                    codes.remove(&link.code);
                }
            }
            self.save_links(&links)?;
            let _ = std::fs::remove_file(&file);
            self.say(format!("discord {}: {result}", link.user));
        }
        Ok(())
    }

    fn link(&mut self, link: &Link) -> String {
        let links = self.links();
        let Some(entry) = links["codes"].get(&link.code) else { return "refused: unknown or used code".into() };
        if entry["expires"].as_u64().unwrap_or(0) < self.now {
            return "refused: the code expired".into();
        }
        let name = entry["name"].as_str().unwrap_or("");
        if !door::is_door_name(name) {
            return "refused: the code names no door account".into();
        }
        let path = self.p.etc().join("discord-roster.json");
        let mut roster = read_json(&path).unwrap_or_else(|| json!({"version":1,"users":{}}));
        if roster["version"] != 1 || !roster["users"].is_object() {
            return "refused: the Discord roster is malformed; nothing changed".into();
        }
        if roster["users"].get(&link.user).is_some() {
            return "refused: this Discord user is already linked".into();
        }
        roster["users"][&link.user] = json!(name);
        match write_atomic(&path, &serde_json::to_vec_pretty(&roster).unwrap_or_default(), 0o644) {
            Ok(()) => format!("linked to {name}"),
            Err(e) => format!("error: {e}"),
        }
    }

    // ── the form's view of the door ────────────────────────────────────────────────────────

    fn door_state(&mut self) -> Result<(), String> {
        let free_reason = self.free_closed(None, true);
        let made = self.counted(Some("free"), false, None);
        let open_seats = (self.cfg.free_cap - self.cfg.invite_reserve).saturating_sub(made);
        let reserved_seats = self.cfg.free_cap.saturating_sub(made).saturating_sub(open_seats);
        let address = self.cfg.pay.as_ref().and_then(|p| read_json(&p.enrol_pin)).and_then(|v| v["enrolAddress"].as_str().map(str::to_owned));
        let paid = self.cfg.pay.is_some() && address.is_some() && self.counted(None, true, None) < self.cfg.daily_cap;
        let v = json!({"type":door::STATE_TYPE,"free":free_reason.is_none(),"freeReason":free_reason,"paid":paid,
            "enrolAddress":address,"network":self.cfg.pay.as_ref().map(|p| p.network.clone()),"at":self.now,
            "funding":self.cfg.funding.to_string(),
            "inviteReserve":self.cfg.invite_reserve,"openSeats":open_seats,"reservedSeats":reserved_seats});
        self.publish("door-state.json", &v)
    }

    /// Every enrolled member joins the built-in story, and the house's shared room, once per world:
    /// the founding account runs `story invite NAME SUBJECT` (`chat invite NAME SUBJECT MEMBER`
    /// for the room), the invitation is handed to the member's HOME/requests, and the member runs
    /// `story join NAME @NAME-invite.json` (`chat join ...`). The world is named by `world_id` (the
    /// node's state.json createdUtc, else the config digest), so a re-genesis (a new world, where
    /// nobody has joined yet) invites every member again and an in-place upgrade does not. The invitation is recorded before the join, so a failed join retries
    /// only the join (a second invite would find the member's cell already born). A failure is
    /// recorded on the request and its status and never touches enrolment; the next run retries.
    fn welcome(&mut self, key: &'static str) -> Result<(), String> {
        let wanted = if key == "story" { self.cfg.story.clone() } else { self.cfg.room.clone() };
        let Some(place) = wanted else { return Ok(()) };
        let world = match std::fs::read(self.p.config()).map(|config| world_id(&config, std::fs::read(self.p.node_state()).ok().as_deref())) {
            Ok(id) => id,
            Err(e) => {
                self.say(format!("{key} {}: no world to join ({}: {e})", place.name, self.p.config().display()));
                return Ok(());
            }
        };
        let mut done = 0;
        for mut r in self.requests() {
            if done >= self.cfg.per_run {
                break;
            }
            if r["phase"] != "enrolled" || (r[key]["world"] == world.as_str() && r[key]["joined"] == true) {
                continue;
            }
            done += 1;
            let name = r["name"].as_str().unwrap_or("").to_owned();
            if let Err(e) = self.join_place(key, &place, &world, &name, &mut r) {
                self.say(format!("request {}: {key} {}: {e}", r["id"].as_str().unwrap_or(""), place.name));
                r[key]["error"] = json!(e);
            }
            self.save(&mut r)?;
        }
        Ok(())
    }

    /// The member's subject: retained on the request, else the member's own `whoami`.
    fn subject_of(&self, name: &str, r: &Value) -> Result<String, String> {
        let subject = match r["subject"].as_str() {
            Some(s) => s.to_owned(),
            None => {
                let ran = self.ops.tenant_line(name, "whoami");
                let v: Value = serde_json::from_str(ran.stdout.trim()).unwrap_or(Value::Null);
                match v["subject"].as_str() {
                    Some(s) if ran.ok => s.to_owned(),
                    _ => return Err(format!("whoami: {}", ran.why())),
                }
            }
        };
        if subject.is_empty() || !subject.bytes().all(|b| b.is_ascii_digit()) {
            return Err(format!("the member's subject {subject:?} is not a decimal"));
        }
        Ok(subject)
    }

    /// The house publications (`/etc/mini/house-publications`, the file `mini-web-spawn` reads: one
    /// `NAME MEMBER` per line, the document NAME the house member MEMBER publishes as the box's own,
    /// the front page's `welcome` among them). A malformed line names nothing.
    fn house_publications(&self) -> Vec<(String, String)> {
        let word = |w: &str| !w.is_empty() && w.len() <= 64 && w.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-');
        std::fs::read_to_string(self.p.etc().join("house-publications")).unwrap_or_default().lines().filter_map(|line| {
            let mut words = line.split_whitespace();
            match (words.next(), words.next(), words.next()) {
                (Some(doc), Some(author), None) if word(doc) && word(author) => Some((doc.to_owned(), author.to_owned())),
                _ => None,
            }
        }).collect()
    }

    /// Every enrolled member holds a reference to each house publication under its own name, once per
    /// world, as the public reader does: the house member delegates `observe` on DOC to the member's
    /// subject (`delegate ID DOC SUBJECT observe MAX`, MAX the public reader's read bound), submits and
    /// publishes it (`submit ID`, `publish ID`), the recipient reference is handed to the member's
    /// HOME/requests, and the member imports it (`import DOC @DOC-reference.json`). So `doc show welcome`
    /// and `/doc/welcome` read the document the lobby points a newcomer to. Each step is recorded on the
    /// request before the next; a rerun resumes (an undecided submit is the exact `retry ID`).
    fn hand_publications(&mut self) -> Result<(), String> {
        let publications = self.house_publications();
        if publications.is_empty() {
            return Ok(());
        }
        let Ok(world) = std::fs::read(self.p.config()).map(|config| world_id(&config, std::fs::read(self.p.node_state()).ok().as_deref())) else {
            return Ok(());
        };
        let mut done = 0;
        for mut r in self.requests() {
            if done >= self.cfg.per_run {
                break;
            }
            let name = r["name"].as_str().unwrap_or("").to_owned();
            let owed: Vec<(String, String)> = publications.iter()
                .filter(|(doc, author)| *author != name && !(r["publications"][doc.as_str()]["world"] == world.as_str() && r["publications"][doc.as_str()]["joined"] == true))
                .cloned().collect();
            if r["phase"] != "enrolled" || owed.is_empty() {
                continue;
            }
            done += 1;
            for (doc, author) in owed {
                if let Err(e) = self.hand_publication(&doc, &author, &world, &name, &mut r) {
                    self.say(format!("request {}: publication {doc}: {e}", r["id"].as_str().unwrap_or("")));
                    r["publications"][doc.as_str()]["error"] = json!(e);
                }
                self.save(&mut r)?;
            }
        }
        Ok(())
    }

    fn hand_publication(&mut self, doc: &str, author: &str, world: &str, name: &str, r: &mut Value) -> Result<(), String> {
        if !r["publications"].is_object() {
            r["publications"] = json!({});
        }
        let subject = self.subject_of(name, r)?;
        r["subject"] = json!(subject);
        if r["publications"][doc]["world"] != world {
            let id = format!("hp-{}", &sha256_hex(format!("minidregg-house-publication-v1\n{world}\n{doc}\n{subject}").as_bytes())[..16]);
            r["publications"][doc] = json!({"world": world, "id": id, "from": author});
            self.save(r)?;
        }
        let id = r["publications"][doc]["id"].as_str().ok_or("no publication id")?.to_owned();
        let house = self.p.home(author).join("workspace");
        if !house.join("proposals").join(&id).exists() {
            let ran = self.ops.tenant_line(author, &format!("delegate {id} {doc} {subject} observe {}", PUBLIC_READ_MAX_COST.trim()));
            if !ran.ok {
                return Err(format!("delegate: {}", ran.why()));
            }
        }
        let reference = house.join("proposals").join(&id).join("recipient-reference.json");
        if !reference.is_file() {
            // An attempt that already reached the Host is retried exactly (its retained bytes), never re-signed.
            let line = if house.join("attempts").join(&id).exists() { format!("retry {id}") } else { format!("submit {id}") };
            let ran = self.ops.tenant_line(author, &line);
            if !ran.ok {
                return Err(format!("{line}: {}", ran.why()));
            }
            let ran = self.ops.tenant_line(author, &format!("publish {id}"));
            if !ran.ok {
                return Err(format!("publish: {}", ran.why()));
            }
        }
        let bytes = std::fs::read(&reference).map_err(|e| format!("{}: {e}", reference.display()))?;
        let file = format!("{doc}-reference.json");
        self.ops.give(name, &self.p.home(name).join("requests").join(&file), &bytes)?;
        let ran = self.ops.tenant_line(name, &format!("import {doc} @{file}"));
        if !ran.ok {
            return Err(format!("import: {}", ran.why()));
        }
        r["publications"][doc] = json!({"world": world, "id": id, "from": author, "joined": true});
        self.say(format!("request {} holds {doc} from {author}", r["id"].as_str().unwrap_or("")));
        Ok(())
    }

    fn join_place(&mut self, key: &str, place: &StoryConfig, world: &str, name: &str, r: &mut Value) -> Result<(), String> {
        let verb = if key == "story" { "story" } else { "chat" };
        let file = format!("{}-invite.json", place.name);
        if r[key]["invited"] != world {
            let subject = self.subject_of(name, r)?;
            let invite = if key == "story" {
                format!("story invite {} {subject}", place.name)
            } else {
                format!("chat invite {} {subject} {name}", place.name)
            };
            let ran = self.ops.tenant_line(&place.author, &invite);
            let prefix = format!("{verb} join {} ", place.name);
            let invitation = ran.stdout.lines().filter_map(|l| l.strip_prefix(prefix.as_str())).last().map(str::to_owned);
            let Some(invitation) = invitation.filter(|_| ran.ok) else {
                return Err(format!("{verb} invite: {}", ran.why()));
            };
            self.ops.give(name, &self.p.home(name).join("requests").join(&file), format!("{invitation}\n").as_bytes())?;
            r["subject"] = json!(subject);
            r[key] = json!({"name": place.name, "invited": world});
            self.save(r)?;
        }
        let ran = self.ops.tenant_line(name, &format!("{verb} join {} @{file}", place.name));
        if !ran.ok {
            return Err(format!("{verb} join: {}", ran.why()));
        }
        r[key] = json!({"name": place.name, "invited": world, "world": world, "joined": true});
        self.say(format!("request {} joined {key} {}", r["id"].as_str().unwrap_or(""), place.name));
        Ok(())
    }

    fn run_once(&mut self) -> Result<(), String> {
        for dir in [self.p.state().join("requests"), self.p.status()] {
            std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        }
        self.intake()?;
        self.progress()?;
        self.welcome("story")?;
        self.welcome("room")?;
        self.hand_publications()?;
        self.apply_links()?;
        self.door_state()
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let root = match args.as_slice() {
        [] => PathBuf::from("/"),
        [flag, dir] if flag == "--root" && dir.starts_with('/') => PathBuf::from(dir),
        _ => {
            eprintln!("usage: mini-door-process [--root ABS-DIR]");
            std::process::exit(64);
        }
    };
    let p = Paths { root };
    let refuse = |why: String| -> ! {
        eprintln!("mini-door-process: REFUSED — {why}");
        std::process::exit(78);
    };
    if p.root == Path::new("/") && unsafe { libc::geteuid() } != 0 {
        refuse("must run as root".into());
    }
    let tenancy = std::fs::read_to_string(p.etc().join("tenancy")).unwrap_or_default();
    if tenancy.trim() != "split" {
        refuse("the door runs only under split tenancy (/etc/mini/tenancy = split)".into());
    }
    let cfg = DoorConfig::load(&p.etc().join("door.json")).unwrap_or_else(|e| refuse(e));
    let state = p.state();
    if let Err(e) = std::fs::create_dir_all(&state).and_then(|_| std::fs::set_permissions(&state, std::fs::Permissions::from_mode(0o700))) {
        refuse(format!("{}: {e}", state.display()));
    }
    // One processor at a time.
    let lock = std::fs::OpenOptions::new().write(true).create(true).mode(0o600).open(state.join(".lock"))
        .unwrap_or_else(|e| refuse(format!("lock: {e}")));
    if unsafe { libc::flock(std::os::fd::AsRawFd::as_raw_fd(&lock), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
        eprintln!("mini-door-process: another run holds the lock");
        return;
    }
    let mut processor = Processor { ops: RealBox { p: p.clone() }, p, cfg, now: now_s(), sponsor: None, log: Vec::new() };
    if let Err(e) = processor.run_once() {
        eprintln!("mini-door-process: {e}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    const KEY: &str = "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIOMqqnkVzrm0SdG6UOoqKLsabgH5C9okWi0dh2l9GKJl";
    const KEY2: &str = "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIEJCQkJCQkJCQkJCQkJCQkJCQkJCQkJCQkJCQkJCQkJC";

    /// A box: accounts appear when the roster is rendered, keys when keygen runs.
    struct Fake {
        p: Paths,
        me: u32,
        balance: RefCell<u128>,
        calls: RefCell<Vec<String>>,
        fail_reenroll: RefCell<bool>,
    }

    impl BoxOps for Fake {
        fn uid(&self, user: &str) -> Option<u32> {
            match user {
                DOOR_USER | DISCORD_USER => Some(self.me),
                u => u.strip_prefix("mini-s-").filter(|n| self.p.home(n).is_dir()).map(|_| self.me + 1000),
            }
        }
        fn gid(&self, _: &str) -> Option<u32> { None }
        fn render(&self) -> Ran {
            self.calls.borrow_mut().push("render".into());
            for e in std::fs::read_dir(self.p.door_friends()).unwrap().flatten() {
                let name = e.file_name().into_string().unwrap().trim_end_matches(".pub").to_owned();
                std::fs::create_dir_all(self.p.home(&name)).unwrap();
            }
            Ran { ok: true, stdout: String::new(), stderr: String::new() }
        }
        fn throwaway_key(&self) -> Result<String, String> {
            self.calls.borrow_mut().push("throwaway-key".into());
            Ok(KEY2.into())
        }
        fn tenant_line(&self, name: &str, line: &str) -> Ran {
            self.calls.borrow_mut().push(format!("{name}: {line}"));
            let home = self.p.home(name);
            if line == "keygen mini.key" {
                std::fs::create_dir_all(home.join("keys")).unwrap();
                for f in ["mini.key", "mini.key.pub", "mini.key.next.pub"] {
                    std::fs::write(home.join("keys").join(f), [7u8; 32]).unwrap();
                }
            } else if line.starts_with("init ") {
                std::fs::create_dir_all(home.join("workspace")).unwrap();
                std::fs::write(home.join("workspace/workspace.json"), "{}").unwrap();
            } else if let Some(subject) = line.strip_prefix("story invite tale ") {
                let invitation = json!({"type":"mini-story-invitation-v1","story":"tale","role":"player","grant":{"recipient":subject}});
                return Ran { ok: true, stdout: format!("invited {subject} to tale as player; give them this line:\nstory join tale {invitation}\n"), stderr: String::new() };
            } else if let Some(rest) = line.strip_prefix("chat invite lobby ") {
                let subject = rest.split(' ').next().unwrap_or("");
                let invitation = json!({"type":"mini-chat-invitation-v1","room":"lobby","grant":{"recipient":subject}});
                return Ran { ok: true, stdout: format!("invited {subject} to lobby; give them this line:\nchat join lobby {invitation}\n"), stderr: String::new() };
            } else if let Some(id) = line.strip_prefix("delegate ").and_then(|r| r.split(' ').next()) {
                std::fs::create_dir_all(home.join("workspace/proposals").join(id)).unwrap();
            } else if let Some(id) = line.strip_prefix("submit ") {
                std::fs::create_dir_all(home.join("workspace/attempts").join(id)).unwrap();
            } else if let Some(id) = line.strip_prefix("publish ") {
                if self.p.root.join("fail-publish").exists() {
                    return Ran { ok: false, stdout: String::new(), stderr: "undecided: the Host did not answer".into() };
                }
                std::fs::write(home.join("workspace/proposals").join(id).join("recipient-reference.json"),
                    json!({"type":"minidregg-delegated-reference-v1","target":"77","capability":"88","proposal":id}).to_string()).unwrap();
            } else if line.starts_with("story join ") && self.p.root.join("fail-story-join").exists() {
                return Ran { ok: false, stdout: String::new(), stderr: "refused: the Host was busy".into() };
            }
            Ran { ok: true, stdout: String::new(), stderr: String::new() }
        }
        fn tenant_mini(&self, name: &str, args: &[String]) -> Ran {
            self.calls.borrow_mut().push(format!("{name}: mini {}", args.iter().skip(2).take(1).cloned().collect::<String>()));
            let home = self.p.home(name);
            let ok = Ran { ok: true, stdout: String::new(), stderr: String::new() };
            if args.contains(&"--wait".to_string()) {
                return ok;
            }
            if let Some(i) = args.iter().position(|a| a == "--ssh-signature") {
                let sig = std::fs::read_to_string(&args[i + 1]).unwrap();
                if !sig.contains("GOOD") {
                    return Ran { ok: false, stdout: String::new(), stderr: "error: sshSigInvalid".into() };
                }
                std::fs::write(home.join("latest-payment.json"), json!({"enrolAddress":"0a".repeat(32),"amountAtomic":"50000007","memo":"enrol:v2:AAAA","asOfHour":"1000",
                    "mint":"08".repeat(32),"tokenProgram":"06ddf6e1d765a193d9cbe146ceeb79ac1cb485ed5f5b37913a8cf5857eff00a9","quote":{"decimals":"6"}}).to_string()).unwrap();
                return ok;
            }
            std::fs::write(home.join("detached-quote.json"), r#"{"expiryHour":"1001"}"#).unwrap();
            std::fs::write(home.join("sshsig-message.bin"), b"statement").unwrap();
            ok
        }
        fn reenroll(&self, name: &str, funding: u128) -> Ran {
            self.calls.borrow_mut().push(format!("reenroll {name} {funding}"));
            if *self.fail_reenroll.borrow() {
                return Ran { ok: false, stdout: String::new(), stderr: format!("{name} FAILED at `enroll seal {name}`: refused: x") };
            }
            *self.balance.borrow_mut() -= funding;
            Ran { ok: true, stdout: format!("{name} 4100\n"), stderr: String::new() }
        }
        fn sponsor_credit(&self) -> Ran {
            Ran { ok: true, stdout: format!("credit {}  (asset 0, account 5, signed read at height 9)\n", self.balance.borrow()), stderr: String::new() }
        }
        fn give(&self, _name: &str, path: &Path, bytes: &[u8]) -> Result<(), String> {
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, bytes).map_err(|e| e.to_string())
        }
    }

    fn world(tag: &str, pay: bool) -> Processor<Fake> {
        let root = std::env::temp_dir().join(format!("door-process-{tag}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        let p = Paths { root: root.clone() };
        for d in [p.queue(), p.links(), p.status(), p.door_friends(), p.sessions(), p.etc()] {
            std::fs::create_dir_all(d).unwrap();
        }
        std::fs::write(p.friends().join("ember.pub"), format!("{KEY2} ember\n")).unwrap();
        let pin = root.join("enrol-v2.json");
        std::fs::write(&pin, r#"{"enrolAddress":"Fresh1111111111111111111111111111111111111"}"#).unwrap();
        let me = std::fs::metadata(&root).map(|m| std::os::unix::fs::MetadataExt::uid(&m)).unwrap();
        let cfg = DoorConfig { funding: 1000, free_cap: 2, invite_reserve: 0, invite_codes: None, daily_cap: 10, per_run: 4, sponsor_floor: 500, link_ttl_s: 3600,
            login_host: "demo.example".into(), story: None, room: None, pay: pay.then(|| PayConfig { enrol_pin: pin, birth_context: None, network: "devnet".into(), symbol: "DREGG".into(), rpc: "https://api.devnet.solana.com".into() }) };
        Processor { ops: Fake { p: p.clone(), me, balance: RefCell::new(3000), calls: RefCell::new(Vec::new()), fail_reenroll: RefCell::new(false) },
            p, cfg, now: 1_000_000, sponsor: None, log: Vec::new() }
    }

    fn submit(w: &Processor<Fake>, r: &Request) {
        door::spool_write(&w.p.queue(), &r.file_name(), &r.to_json()).unwrap();
    }

    fn join(name: &str, key: &str, route: Route, discord: bool) -> Request {
        Request::Join { id: door::new_request_id().unwrap(), at: 999_000, name: name.into(), ssh_key: key.into(), discord, route, research: name == "bea", invite: None }
    }

    fn status(w: &Processor<Fake>, id: &str) -> Value {
        read_json(&w.p.status().join(format!("{id}.json"))).unwrap()
    }

    fn run(w: &mut Processor<Fake>) {
        w.sponsor = None;
        w.run_once().unwrap();
    }

    #[test]
    fn a_world_survives_an_in_place_upgrade_and_changes_at_a_regenesis() {
        let state = |stamp: &str| format!(r#"{{"type":"minidregg-candidate-state-v1","pinnedConfigSha256":"x","createdUtc":"{stamp}"}}"#);
        let one = world_id(b"config before upgrade", Some(state("2026-10-28T01:00:00Z").as_bytes()));
        // upgrade: config rewritten, createdUtc and the rest of the state kept
        assert_eq!(one, world_id(b"config AFTER upgrade", Some(state("2026-10-28T01:00:00Z").as_bytes())));
        // re-genesis: a new stamp
        assert_ne!(one, world_id(b"config before upgrade", Some(state("2026-10-28T09:00:00Z").as_bytes())));
        // no readable state: the config digest, as before
        assert_eq!(world_id(b"c", None), sha256_hex(b"c"));
        assert_ne!(world_id(b"c", None), world_id(b"d", None));
        assert_eq!(world_id(b"c", Some(b"not json")), sha256_hex(b"c"));
    }

    #[test]
    fn why_keeps_the_whole_diagnostic_line_and_the_childs_last_words() {
        let long = format!("error: local process /var/lib/mini/candidate/bin/minidregg-client-consent ended before {}", "x".repeat(900));
        let r = Ran { ok: false, stdout: String::new(), stderr: format!("noise\n{long}\nconsent closed\n") };
        let w = r.why();
        assert!(w.starts_with(&long), "the whole error line, not its first 300 bytes");
        assert!(w.ends_with("last stderr line: consent closed"), "{w}");
        let only = Ran { ok: false, stdout: String::new(), stderr: format!("{long}\n") };
        assert_eq!(only.why(), long);
    }

    #[test]
    fn a_browser_only_join_gets_a_throwaway_login_key_and_only_the_web_link() {
        let mut w = world("webonly", false);
        let r = join("bea", "", Route::Free, false);
        submit(&w, &r);
        run(&mut w);
        let s = status(&w, r.id());
        assert_eq!(s["phase"], "enrolled", "{s}");
        assert!(s["login"].is_null(), "no ssh login line: {s}");
        assert_eq!(s["webOnly"], true);
        assert!(w.ops.calls.borrow().iter().any(|c| c.contains("create research-consent declared open 1")), "{:?}", w.ops.calls.borrow());
        assert!(w.ops.calls.borrow().iter().any(|c| c.contains("invoke research-consent-0 research-consent create 1 1")), "bea ticked the box: field 1 = 1 (CC0)");
        assert!(w.ops.calls.borrow().iter().any(|c| c.contains("submit research-consent-0")));
        assert_eq!(s["funding"], w.cfg.funding.to_string(), "the status names what the box funded");
        let state = read_json(&w.p.status().join("door-state.json")).unwrap();
        assert_eq!(state["funding"], w.cfg.funding.to_string(), "the form reads the configured funding, never a literal");
        assert!(s["webLogin"].as_str().unwrap().starts_with("https://demo.example/login/"));
        assert!(w.ops.calls.borrow().contains(&"throwaway-key".to_string()));
        let entry = std::fs::read_to_string(w.p.door_friends().join("bea.pub")).unwrap();
        assert!(entry.contains("web-only") && entry.ends_with(&format!("{KEY2} bea\n")), "{entry}");
        // The schema: an empty sshKey round-trips as a free join, never as a paid one.
        let bytes = r.to_json().to_string();
        assert!(matches!(Request::parse(bytes.as_bytes()).unwrap(), Request::Join { ssh_key, .. } if ssh_key.is_empty()));
        let paid = Request::Join { id: door::new_request_id().unwrap(), at: 1, name: "cy".into(), ssh_key: String::new(), discord: false, route: Route::Paid, research: false, invite: None };
        assert!(Request::parse(paid.to_json().to_string().as_bytes()).is_err());
    }

    #[test]
    fn every_enrolled_member_joins_the_story_once_per_world_and_a_failed_join_retries_only_the_join() {
        let mut w = world("story", false);
        w.cfg.story = Some(StoryConfig { author: "box".into(), name: "tale".into() });
        std::fs::create_dir_all(w.p.config().parent().unwrap()).unwrap();
        std::fs::write(w.p.config(), b"world one").unwrap();
        let r = join("alice", KEY, Route::Free, false);
        std::fs::write(w.p.root.join("fail-story-join"), b"").unwrap();
        submit(&w, &r);
        run(&mut w);
        let count = |w: &Processor<Fake>, prefix: &str| w.ops.calls.borrow().iter().filter(|c| c.starts_with(prefix)).count();
        let s = status(&w, r.id());
        assert_eq!(s["phase"], "enrolled", "a failed story step never touches enrolment: {s}");
        assert!(s["story"]["error"].as_str().unwrap().contains("the Host was busy"), "{s}");
        assert_eq!((count(&w, "box: story invite tale 4100"), count(&w, "alice: story join tale @tale-invite.json")), (1, 1));
        let handed = std::fs::read_to_string(w.p.home("alice").join("requests/tale-invite.json")).unwrap();
        assert_eq!(serde_json::from_str::<Value>(&handed).unwrap()["grant"]["recipient"], "4100", "the member's own invitation, in HOME/requests");
        // The next run retries the join alone: a second invite would find the member's cell born.
        std::fs::remove_file(w.p.root.join("fail-story-join")).unwrap();
        run(&mut w);
        assert_eq!((count(&w, "box: story invite"), count(&w, "alice: story join")), (1, 2));
        let s = status(&w, r.id());
        assert_eq!(s["story"]["joined"], true, "{s}");
        assert!(s["story"]["error"].is_null());
        // Joined in this world: nothing more.
        run(&mut w);
        assert_eq!((count(&w, "box: story invite"), count(&w, "alice: story join")), (1, 2));
        // A re-genesis is a new world, where nobody has joined: invited and joined again.
        std::fs::write(w.p.config(), b"world two").unwrap();
        run(&mut w);
        assert_eq!((count(&w, "box: story invite"), count(&w, "alice: story join")), (2, 3));
        assert_eq!(status(&w, r.id())["story"]["joined"], true);
    }

    #[test]
    fn every_enrolled_member_joins_the_house_room_once_per_world() {
        let mut w = world("room", false);
        w.cfg.room = Some(StoryConfig { author: "box".into(), name: "lobby".into() });
        std::fs::create_dir_all(w.p.config().parent().unwrap()).unwrap();
        std::fs::write(w.p.config(), b"world one").unwrap();
        let r = join("alice", KEY, Route::Free, false);
        submit(&w, &r);
        run(&mut w);
        run(&mut w);
        let count = |w: &Processor<Fake>, prefix: &str| w.ops.calls.borrow().iter().filter(|c| c.starts_with(prefix)).count();
        let s = status(&w, r.id());
        assert_eq!(s["room"]["joined"], true, "{s}");
        assert_eq!((count(&w, "box: chat invite lobby 4100 alice"), count(&w, "alice: chat join lobby @lobby-invite.json")), (1, 1));
        assert!(!w.ops.calls.borrow().iter().any(|c| c.contains("story")), "{:?}", w.ops.calls.borrow());
        let cfg = w.p.etc().join("door-room.json");
        std::fs::write(&cfg, r#"{"version":1,"room":{"founder":"box","name":"lobby"}}"#).unwrap();
        assert_eq!(DoorConfig::load(&cfg).unwrap().room.map(|s| (s.author, s.name)), Some(("box".into(), "lobby".into())));
        std::fs::write(&cfg, r#"{"version":1,"room":{"founder":"box","name":"Lobby!"}}"#).unwrap();
        assert!(DoorConfig::load(&cfg).unwrap_err().contains("room is"));
    }

    #[test]
    fn every_enrolled_member_holds_the_house_publications_once_per_world() {
        let mut w = world("pubs", false);
        std::fs::create_dir_all(w.p.config().parent().unwrap()).unwrap();
        std::fs::write(w.p.config(), b"world one").unwrap();
        std::fs::write(w.p.etc().join("house-publications"), "welcome box\nbad line here\nhouse-rules box\n").unwrap();
        std::fs::write(w.p.root.join("fail-publish"), b"").unwrap();
        let r = join("alice", KEY, Route::Free, false);
        submit(&w, &r);
        run(&mut w);
        let count = |w: &Processor<Fake>, prefix: &str| w.ops.calls.borrow().iter().filter(|c| c.starts_with(prefix)).count();
        let s = read_json(&w.request_path(r.id())).unwrap();
        assert!(s["publications"]["welcome"]["error"].as_str().unwrap().starts_with("publish:"), "{s}");
        assert_eq!(count(&w, "alice: import"), 0, "nothing imported before the publication is decided");
        // the next run resumes: the delegation is not made again, the submit that reached the Host is retried exactly
        std::fs::remove_file(w.p.root.join("fail-publish")).unwrap();
        run(&mut w);
        run(&mut w);
        let s = read_json(&w.request_path(r.id())).unwrap();
        assert_eq!((s["publications"]["welcome"]["joined"].as_bool(), s["publications"]["house-rules"]["joined"].as_bool()), (Some(true), Some(true)), "{s}");
        let id = s["publications"]["welcome"]["id"].as_str().unwrap().to_owned();
        assert_eq!(count(&w, &format!("box: delegate {id} welcome 4100 observe {}", PUBLIC_READ_MAX_COST.trim())), 1);
        assert_eq!((count(&w, &format!("box: submit {id}")), count(&w, &format!("box: retry {id}")), count(&w, &format!("box: publish {id}"))), (1, 1, 2));
        assert_eq!(count(&w, "alice: import welcome @welcome-reference.json"), 1);
        let given = std::fs::read_to_string(w.p.home("alice").join("requests/welcome-reference.json")).unwrap();
        assert!(given.contains(&id), "the member is handed the house's recipient reference: {given}");
        // a re-genesis is a new world: handed again under a new id
        std::fs::write(w.p.node_state(), r#"{"createdUtc":"2026-11-01T00:00:00Z"}"#).unwrap();
        run(&mut w);
        let s = read_json(&w.request_path(r.id())).unwrap();
        assert_ne!(s["publications"]["welcome"]["id"].as_str().unwrap(), id);
        assert_eq!(count(&w, "alice: import welcome"), 2);
    }

    #[test]
    fn without_a_story_configured_no_member_is_invited_and_a_bad_story_name_is_refused() {
        let mut w = world("nostory", false);
        std::fs::create_dir_all(w.p.config().parent().unwrap()).unwrap();
        std::fs::write(w.p.config(), b"world one").unwrap();
        submit(&w, &join("alice", KEY, Route::Free, false));
        run(&mut w);
        assert!(!w.ops.calls.borrow().iter().any(|c| c.contains("story")), "{:?}", w.ops.calls.borrow());
        let cfg = w.p.etc().join("door-story.json");
        std::fs::write(&cfg, r#"{"version":1,"story":{"author":"box","name":"tale"}}"#).unwrap();
        assert_eq!(DoorConfig::load(&cfg).unwrap().story.map(|s| (s.author, s.name)), Some(("box".into(), "tale".into())));
        std::fs::write(&cfg, r#"{"version":1,"story":{"author":"box; rm","name":"tale"}}"#).unwrap();
        assert!(DoorConfig::load(&cfg).unwrap_err().contains("story is"));
    }

    #[test]
    fn a_free_join_goes_through_the_roster_render_keygen_reenroll_and_init_once() {
        let mut w = world("free", false);
        let r = join("alice", KEY, Route::Free, true);
        submit(&w, &r);
        run(&mut w);
        let s = status(&w, r.id());
        assert_eq!(s["phase"], "enrolled", "{s}");
        assert_eq!(s["login"], "mini-s-alice@demo.example");
        let code = s["linkCode"].as_str().unwrap().to_owned();
        assert!(door::is_link_code(&code));
        // The browser login: one record under the helper's logins, named by the code's SHA-256.
        let web = s["webLogin"].as_str().unwrap().to_owned();
        let web_code = web.strip_prefix("https://demo.example/login/").unwrap();
        assert_eq!(web_code.len(), 43, "{web}");
        let record = read_json(&w.p.web_logins().join(format!("{}.json", sha256_hex(web_code.as_bytes())))).unwrap();
        assert_eq!(record["name"], "alice");
        assert_eq!(record["expires"], json!(w.now + 3600));
        // Enrolment ends with the member's research-consent fact, as the member: alice did not tick
        // the box, so field 1 = 0 (none); the status says so.
        assert_eq!(*w.ops.calls.borrow(), ["render", "alice: keygen mini.key", "reenroll alice 1000", "alice: init mini.key 4100",
            "alice: create research-consent declared open 1", "alice: invoke research-consent-0 research-consent create 1 0", "alice: submit research-consent-0"]);
        assert_eq!(s["researchConsent"], "none");
        let entry = std::fs::read_to_string(w.p.door_friends().join("alice.pub")).unwrap();
        assert!(entry.ends_with(&format!("{KEY} alice\n")), "{entry}");
        assert!(!w.p.queue().join(r.file_name()).exists(), "the queue file is consumed");
        // Idempotent: another tick does nothing more.
        run(&mut w);
        assert_eq!(w.ops.calls.borrow().len(), 7);
        // The Discord link: the processor alone writes the roster, once per code.
        let link = Link { interaction: "777".into(), user: "4242".into(), code: code.clone(), at: 1 };
        door::spool_write(&w.p.links(), &link.file_name(), &link.to_json()).unwrap();
        run(&mut w);
        let roster = read_json(&w.p.etc().join("discord-roster.json")).unwrap();
        assert_eq!(roster, json!({"version":1,"users":{"4242":"alice"}}));
        let again = Link { interaction: "778".into(), user: "4343".into(), code, at: 2 };
        door::spool_write(&w.p.links(), &again.file_name(), &again.to_json()).unwrap();
        run(&mut w);
        assert_eq!(read_json(&w.p.etc().join("discord-roster.json")).unwrap()["users"].as_object().unwrap().len(), 1, "a used code links nobody");
    }

    #[test]
    fn names_keys_caps_and_the_sponsor_floor_refuse_with_a_reason() {
        let mut w = world("caps", false);
        let taken = join("ember", KEY, Route::Free, false); // reserved: the form and schema refuse it already
        assert!(Request::parse(&serde_json::to_vec(&taken.to_json()).unwrap()).is_err());
        let dup_key = join("bob", KEY2, Route::Free, false); // the sponsor's key
        submit(&w, &dup_key);
        let a = join("alice", KEY, Route::Free, false);
        submit(&w, &a);
        run(&mut w);
        assert!(status(&w, dup_key.id())["detail"].as_str().unwrap().contains("already has an account"));
        assert_eq!(status(&w, a.id())["phase"], "enrolled");
        let same_name = join("alice", "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIENDQ0NDQ0NDQ0NDQ0NDQ0NDQ0NDQ0NDQ0NDQ0NDQ0ND", Route::Free, false);
        submit(&w, &same_name);
        run(&mut w);
        assert!(status(&w, same_name.id())["detail"].as_str().unwrap().contains("name is taken"));
        // Balance 2000 now: one more 1000 would leave the floor 500 + 1000 unmet after it, so
        // the next free account is the last; the one after is refused by name.
        let c = join("carol", "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIERERERERERERERERERERERERERERERERERERERERERE", Route::Free, false);
        submit(&w, &c);
        run(&mut w);
        assert_eq!(status(&w, c.id())["phase"], "enrolled");
        let d = join("dave", "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIEVFRUVFRUVFRUVFRUVFRUVFRUVFRUVFRUVFRUVFRUVF", Route::Free, false);
        submit(&w, &d);
        run(&mut w);
        let s = status(&w, d.id());
        assert_eq!(s["phase"], "refused");
        assert!(s["detail"].as_str().unwrap().contains("free accounts are taken") || s["detail"].as_str().unwrap().contains("sponsorBelowFloor"), "{s}");
        let state = read_json(&w.p.status().join("door-state.json")).unwrap();
        assert_eq!(state["free"], false, "the form stops offering the free route");
    }

    #[test]
    fn atomic_amounts_read_as_tokens() {
        assert_eq!(decimal_tokens("50000007", 6).as_deref(), Some("50.000007"));
        assert_eq!(decimal_tokens("50000000", 6).as_deref(), Some("50"));
        assert_eq!(decimal_tokens("7", 6).as_deref(), Some("0.000007"));
        assert_eq!(decimal_tokens("12", 0).as_deref(), Some("12"));
        assert_eq!(decimal_tokens("x", 6), None);
    }

    #[test]
    fn a_failed_step_is_retried_next_tick_and_never_redone_before_it() {
        let mut w = world("retry", false);
        *w.ops.fail_reenroll.borrow_mut() = true;
        let a = join("alice", KEY, Route::Free, false);
        submit(&w, &a);
        run(&mut w);
        let s = status(&w, a.id());
        assert_eq!(s["phase"], "keyed");
        assert!(s["detail"].as_str().unwrap().contains("retry"), "{s}");
        *w.ops.fail_reenroll.borrow_mut() = false;
        run(&mut w);
        assert_eq!(status(&w, a.id())["phase"], "enrolled");
        let calls = w.ops.calls.borrow();
        assert_eq!(calls.iter().filter(|c| *c == "render").count(), 1);
        assert_eq!(calls.iter().filter(|c| c.contains("keygen")).count(), 1);
    }

    #[test]
    fn a_paid_join_lands_on_the_hosted_key_through_sign_pay_and_wait() {
        let mut w = world("paid", true);
        let a = join("alice", KEY, Route::Paid, false);
        submit(&w, &a);
        run(&mut w);
        let s = status(&w, a.id());
        assert_eq!(s["phase"], "sign", "{s}");
        assert_eq!(s["sign"]["message"], b64(b"statement"));
        assert_eq!(s["sign"]["expiryHour"], 1001);
        assert!(!w.ops.calls.borrow().iter().any(|c| c.starts_with("reenroll")), "the sponsor funds nothing");
        // A bad signature is asked for again; a good one yields the payment material.
        let armour = |body: &str| format!("-----BEGIN SSH SIGNATURE-----\n{body}\n-----END SSH SIGNATURE-----\n");
        submit(&w, &Request::Sign { id: a.id().into(), at: 1, signature: armour("BAD") });
        run(&mut w);
        let s = status(&w, a.id());
        assert_eq!(s["phase"], "sign");
        assert!(s["detail"].as_str().unwrap().contains("sshSigInvalid"));
        submit(&w, &Request::Sign { id: a.id().into(), at: 2, signature: armour("GOOD") });
        run(&mut w);
        let s = status(&w, a.id());
        assert_eq!(s["phase"], "awaiting-payment", "{s}");
        assert_eq!(s["payment"]["recipient"], b58(&[10u8; 32]));
        assert_eq!(s["payment"]["memo"], "enrol:v2:AAAA");
        assert_eq!(s["payment"]["mint"], b58(&[8u8; 32]));
        assert_eq!(s["payment"]["tokenProgram"], "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA");
        assert_eq!(s["payment"]["decimals"], "6");
        assert_eq!(s["payment"]["amountTokens"], "50.000007 DREGG");
        assert_eq!(s["payment"]["asOfHour"], "1000");
        assert!(s["payment"]["quotedAt"].is_u64());
        assert_eq!(s["payment"]["rpc"], "https://api.devnet.solana.com");
        let tx = "2Ana1pUpv2ZbMVkwF5FXapYeBEjdxDatLn7nvJkhgTSXbs59SyZSx866bXirPgj8QQVB57uxHJBG1YFvkRbFj4T";
        submit(&w, &Request::Paid { id: a.id().into(), at: 3, transaction: tx.into() });
        run(&mut w);
        assert_eq!(status(&w, a.id())["phase"], "enrolled");
        let state = read_json(&w.p.status().join("door-state.json")).unwrap();
        assert_eq!(state["paid"], true);
        assert_eq!(state["network"], "devnet");
    }

    #[test]
    fn a_spool_file_not_of_the_schema_or_not_its_writers_is_rejected_and_never_acted_on() {
        let mut w = world("reject", false);
        std::fs::write(w.p.queue().join("join-x.json"), r#"{"kind":"join","name":"alice"}"#).unwrap();
        let a = join("alice", KEY, Route::Free, false);
        // A valid request under another file name.
        door::spool_write(&w.p.queue(), "join-other.json", &a.to_json()).unwrap();
        run(&mut w);
        assert!(w.ops.calls.borrow().is_empty());
        assert_eq!(std::fs::read_dir(w.p.queue()).unwrap().count(), 0);
        assert_eq!(std::fs::read_dir(w.p.state().join("rejected")).unwrap().count(), 2);
        assert!(!w.p.door_friends().join("alice.pub").exists());
    }

    #[test]
    fn config_refuses_unknown_keys_and_reads_defaults() {
        let dir = std::env::temp_dir().join(format!("door-config-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let p = dir.join("door.json");
        std::fs::write(&p, r#"{"version":1}"#).unwrap();
        let c = DoorConfig::load(&p).unwrap();
        assert_eq!((c.funding, c.free_cap, c.daily_cap, c.sponsor_floor), (1000, 50, 20, 20_000));
        std::fs::write(&p, r#"{"version":1,"comp":true}"#).unwrap();
        assert!(DoorConfig::load(&p).is_err());
        std::fs::write(&p, r#"{"version":1,"pay":{"enrolPin":"/x","network":"testnet"}}"#).unwrap();
        assert!(DoorConfig::load(&p).is_err());
        std::fs::remove_dir_all(&dir).unwrap();
    }

    // ── invite reserve ─────────────────────────────────────────────────────────────────────

    fn invite_world(tag: &str) -> Processor<Fake> {
        let mut w = world(tag, false);
        w.cfg.free_cap = 50;
        w.cfg.invite_reserve = 20;
        w.cfg.invite_codes = Some(PathBuf::from("/etc/mini/invite-codes"));
        w.cfg.daily_cap = 1000;
        w.cfg.per_run = 100;
        *w.ops.balance.borrow_mut() = 1_000_000_000;
        let text: String = std::iter::once("# operator-issued, one use each\n".to_owned()).chain((1..=21).map(|n| format!("{n} INVITE{n:03}-abcdef\n"))).collect();
        write_atomic(&w.codes_path().unwrap(), text.as_bytes(), 0o600).unwrap();
        w
    }

    fn code(n: u32) -> String { format!("INVITE{n:03}-abcdef") }

    /// One stranger (browser-only, free route), one tick; the request's status.
    fn stranger(w: &mut Processor<Fake>, name: &str, invite: Option<String>) -> Value {
        let r = Request::Join { id: door::new_request_id().unwrap(), at: 999_000, name: name.into(), ssh_key: String::new(), discord: false, route: Route::Free, research: false, invite };
        submit(w, &r);
        run(w);
        status(w, r.id())
    }

    fn invite_calls(w: &Processor<Fake>) -> Vec<String> {
        w.ops.calls.borrow().iter().filter(|c| c.contains("invite")).cloned().collect()
    }

    #[test]
    fn invite_reserve_holds_twenty_of_fifty_seats_for_codes() {
        let mut w = invite_world("invite-seats");
        for i in 1..=30 {
            let s = stranger(&mut w, &format!("m{i}"), None);
            assert_eq!(s["phase"], "enrolled", "uncoded stranger {i} takes an open seat: {s}");
        }
        assert!(invite_calls(&w).is_empty(), "an uncoded member has no invite fact");
        let state = read_json(&w.p.status().join("door-state.json")).unwrap();
        assert_eq!((state["openSeats"].as_u64(), state["reservedSeats"].as_u64(), state["free"].as_bool()), (Some(0), Some(20), Some(true)), "{state}");
        // The 31st uncoded stranger is refused by name, and told what remains.
        let s = stranger(&mut w, "m31", None);
        assert_eq!(s["phase"], "refused", "{s}");
        let detail = s["detail"].as_str().unwrap();
        assert!(detail.starts_with("open-seats-gone:") && detail.contains("20 remain for people with an invite code"), "{detail}");
        // An unknown code, by name; nothing is struck.
        let s = stranger(&mut w, "m32", Some("NOSUCHCODE-1234".into()));
        assert!(s["detail"].as_str().unwrap().starts_with("invite-unknown:"), "{s}");
        // A coded stranger is admitted on a reserved seat; the code is struck with the request, and
        // the member's own turns write `invite` field 1 = the serial (never the code).
        let s = stranger(&mut w, "m33", Some(code(7)));
        assert_eq!(s["phase"], "enrolled", "{s}");
        assert!(!s.to_string().contains(&code(7)), "the status never carries the code");
        assert_eq!(invite_calls(&w), ["m33: create invite declared open", "m33: invoke invite-0 invite create 1 7", "m33: submit invite-0"]);
        assert!(!w.ops.calls.borrow().iter().any(|c| c.contains(&code(7))), "no world line carries the code");
        let file = std::fs::read_to_string(w.codes_path().unwrap()).unwrap();
        let line = file.lines().find(|l| l.starts_with("7 ")).unwrap();
        assert!(line.starts_with(&format!("7 {} used m33 {} ", code(7), s["id"].as_str().unwrap())), "{line}");
        assert!(file.starts_with("# operator-issued"), "comments survive the rewrite");
        // The same code again: spent.
        let s = stranger(&mut w, "m34", Some(code(7)));
        assert!(s["detail"].as_str().unwrap().starts_with("invite-spent:"), "{s}");
        // Coded strangers fill the reserve (m33 is the first of 20) ...
        for (k, n) in (1..=21u32).filter(|n| *n != 7).take(19).enumerate() {
            let s = stranger(&mut w, &format!("c{k}"), Some(code(n)));
            assert_eq!(s["phase"], "enrolled", "coded stranger {k}: {s}");
        }
        // ... and the 51st, even with a valid unspent code, is refused at freeCap and keeps the code.
        let s = stranger(&mut w, "late", Some(code(21)));
        assert_eq!(s["phase"], "refused", "{s}");
        assert_eq!(s["detail"], "all 50 free accounts are taken");
        assert!(std::fs::read_to_string(w.codes_path().unwrap()).unwrap().lines().any(|l| l == format!("21 {}", code(21))), "a seat refusal burns no code");
    }

    #[test]
    fn a_retry_by_the_same_request_reuses_its_own_strike_and_a_refusal_after_it_returns_the_code() {
        let mut w = invite_world("invite-crash");
        let r = Request::Join { id: door::new_request_id().unwrap(), at: 999_000, name: "zed".into(), ssh_key: String::new(), discord: false, route: Route::Free, research: false, invite: Some(code(3)) };
        // The crash: the strike landed, the request's own record did not.
        w.strike_invite(3, "zed", r.id()).unwrap();
        submit(&w, &r);
        run(&mut w);
        assert_eq!(status(&w, r.id())["phase"], "enrolled", "the request finds its own strike, not 'spent'");
        assert!(invite_calls(&w).contains(&"zed: invoke invite-0 invite create 1 3".to_owned()));
        // Another request cannot take it.
        assert_eq!(w.invite_state(&code(3), "someone-else").unwrap(), InviteState::Spent);
        // A request refused after its strike hands the code back.
        let r2 = door::new_request_id().unwrap();
        w.strike_invite(4, "yan", &r2).unwrap();
        assert_eq!(w.invite_state(&code(4), "x").unwrap(), InviteState::Spent);
        w.release_invite(&r2).unwrap();
        assert_eq!(w.invite_state(&code(4), "x").unwrap(), InviteState::Unspent(4));
    }

    #[test]
    fn the_codes_file_must_be_private_and_well_formed() {
        let mut w = invite_world("invite-file");
        std::fs::set_permissions(w.codes_path().unwrap(), std::fs::Permissions::from_mode(0o644)).unwrap();
        let s = stranger(&mut w, "kay", Some(code(1)));
        assert_ne!(s["phase"], "enrolled", "{s}");
        assert!(s["detail"].as_str().unwrap().contains("0600"), "{s}");
        std::fs::set_permissions(w.codes_path().unwrap(), std::fs::Permissions::from_mode(0o600)).unwrap();
        for bad in ["1 SHORT\n", "0 INVITE001-abcdef\n", "1 INVITE001-abcdef\n2 INVITE001-abcdef\n", "1 INVITE001-abcdef used\n"] {
            assert!(parse_codes(bad).is_err(), "{bad:?}");
        }
        let text = "# c\n1 INVITE001-abcdef used kay 0123456789abcdef0123456789abcdef 5\n\n2 INVITE002-abcdef\n";
        assert_eq!(render_codes(&parse_codes(text).unwrap()), text);
    }

    #[test]
    fn door_json_reads_the_invite_fields_and_refuses_a_reserve_beyond_the_cap() {
        let dir = std::env::temp_dir().join(format!("door-json-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let load = |body: &str| { let f = dir.join("door.json"); std::fs::write(&f, body).unwrap(); DoorConfig::load(&f) };
        let ok = load(r#"{"version":1,"freeCap":50,"inviteReserve":20,"inviteCodes":"/etc/mini/invite-codes","dailyCap":20}"#).unwrap();
        assert_eq!((ok.free_cap, ok.invite_reserve, ok.daily_cap), (50, 20, 20));
        assert_eq!(ok.invite_codes, Some(PathBuf::from("/etc/mini/invite-codes")));
        let plain = load(r#"{"version":1}"#).unwrap();
        assert_eq!((plain.invite_reserve, plain.invite_codes), (0, None), "today's door");
        assert!(load(r#"{"version":1,"freeCap":50,"inviteReserve":51,"inviteCodes":"/x"}"#).unwrap_err().contains("exceeds freeCap"));
        assert!(load(r#"{"version":1,"freeCap":50,"inviteReserve":20}"#).unwrap_err().contains("inviteCodes"));
        assert!(load(r#"{"version":1,"inviteCodes":"relative"}"#).is_err());
        assert!(load(r#"{"version":1,"inviteReserv":20}"#).unwrap_err().contains("unknown key"));
    }

    #[test]
    fn a_request_with_an_invite_round_trips_and_is_free_route_only() {
        let r = Request::Join { id: door::new_request_id().unwrap(), at: 1, name: "ab".into(), ssh_key: String::new(), discord: false, route: Route::Free, research: false, invite: Some(code(1)) };
        assert_eq!(Request::parse(r.to_json().to_string().as_bytes()).unwrap(), r);
        let mut v = r.to_json();
        v["invite"] = json!("short");
        assert!(Request::parse(v.to_string().as_bytes()).is_err());
        let mut v = Request::Join { id: door::new_request_id().unwrap(), at: 1, name: "ab".into(), ssh_key: KEY.into(), discord: false, route: Route::Paid, research: false, invite: None }.to_json();
        v["invite"] = json!(code(1));
        assert!(Request::parse(v.to_string().as_bytes()).is_err(), "a paid request carries no code");
    }
}
