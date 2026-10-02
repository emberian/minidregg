//! `mini-discord-mirror`: a RUNNER that bridges one Mini room and one Discord channel,
//! both ways.
//!
//! It is not part of the interactions endpoint. It holds its OWN session: its own key, its
//! own workspace, its own membership of the room (the founder invited it like anyone else,
//! so it has its own stream). Every Mini step is one `mini shell --line` through the same
//! forced command as ssh and Discord, so every read and every append is signed by the
//! bridge's key, metered and refusable like anyone's.
//!
//! Room -> channel: `tail --in ROOM --json --since H` (the merged, digest-checked feed);
//! each new `say` is posted to the channel webhook as `name: text`.
//! Channel -> room: the channel's messages after the last one seen (Discord REST, the bot
//! token); each human message becomes `say --in ROOM --via discord --via-id ID --via-name NAME
//! --file F`: the BRIDGE says it, and the payload names the Discord author. It never signs as
//! a friend; a reader sees `bridge via discord NAME#ID: text`.
//!
//! Loop prevention, both directions:
//! * a room entry that carries `via` (anything a bridge said), or that the bridge's own
//!   subject signed, is never posted to the channel;
//! * a channel message from a webhook (`webhook_id`: what this mirror posted) or from a bot
//!   is never said into the room.
//!
//! Configuration is the environment (`EnvironmentFile`, 0600; the webhook URL and the bot
//! token are secrets): `MINI_MIRROR_ROOM`, `MINI_MIRROR_WEBHOOK_URL`, `MINI_MIRROR_CHANNEL_URL`
//! (`https://discord.com/api/v10/channels/ID/messages`), `MINI_MIRROR_BOT_TOKEN`,
//! `MINI_MIRROR_HOME`, `MINI_MIRROR_WORKSPACE`, `MINI_MIRROR_INTERVAL_S` (default 30),
//! `MINI_DISCORD_SPOOL`, and the deployment variables of `mini-discord` (`MINI_SHELL_WRAPPER`
//! `MINI_CLIENT` `MINI_HOST` `MINI_CONFIG` `MINI_SOCKET`). One argument is accepted: `--once`.

use std::path::{Path, PathBuf};
use std::time::Duration;

use minidregg_discord_entrance::curl::Poster;
use minidregg_discord_entrance::interaction::{followup, is_snowflake};
use minidregg_discord_entrance::reply::DISCORD_LIMIT;
use minidregg_discord_entrance::session::{append_log, Deployment, Session};
use minidregg_discord_entrance::{env_path, env_required, env_u64, now_s};
use serde_json::{json, Value};

const LOG_FILE: &str = "discord-mirror.log";
/// At most this many entries or messages cross per direction per poll.
const BATCH: usize = 20;

fn fail(msg: impl std::fmt::Display) -> ! {
    eprintln!("mini-discord-mirror: {msg}");
    std::process::exit(78);
}

fn is_room_name(s: &str) -> bool {
    !s.is_empty() && s.len() <= 40 && s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
}

/// What has crossed: the room height posted up to, and the last channel message said.
#[derive(Debug, Default, Clone, PartialEq)]
pub struct State {
    pub height: Option<u64>,
    pub message: Option<String>,
}

fn load_state(p: &Path) -> State {
    let v: Value = std::fs::read(p).ok().and_then(|b| serde_json::from_slice(&b).ok()).unwrap_or(Value::Null);
    State {
        height: v.get("height").and_then(Value::as_u64),
        message: v.get("message").and_then(Value::as_str).map(str::to_owned),
    }
}

fn save_state(p: &Path, s: &State) -> std::io::Result<()> {
    let tmp = p.with_extension("tmp");
    std::fs::write(&tmp, serde_json::to_vec(&json!({"height":s.height,"message":s.message}))?)?;
    std::fs::rename(tmp, p)
}

/// The room's feed from `tail --json`: (bridge-relevant state line, entries).
pub fn feed_of(stdout: &str) -> (Value, Vec<Value>) {
    let mut docs = serde_json::Deserializer::from_str(stdout).into_iter::<Value>().flatten();
    let state = docs.next().unwrap_or(Value::Null);
    (state, docs.collect())
}

/// The channel lines for room entries above `height`: `say` and raw text only, never an
/// entry a bridge said (`via`) or one the bridge itself signed (`me`).
pub fn outbound(entries: &[Value], height: Option<u64>, me: &str) -> Vec<(u64, String)> {
    let mut out: Vec<(u64, String)> = entries
        .iter()
        .filter_map(|e| {
            let h = e.get("height")?.as_u64()?;
            if height.is_some_and(|seen| h <= seen) {
                return None;
            }
            if !matches!(e.get("kind")?.as_str()?, "say" | "raw") || !e.get("via").is_none_or(Value::is_null) {
                return None;
            }
            if e.get("author")?.as_str()? == me {
                return None;
            }
            let name = e.get("name").and_then(Value::as_str).unwrap_or("?");
            let text = e.get("text")?.as_str()?;
            let line = format!("**{}**: {}", name.replace(['*', '`', '@'], ""), text.replace('@', "@\u{200b}"));
            Some((h, line.chars().take(DISCORD_LIMIT).collect()))
        })
        .collect();
    let skip = out.len().saturating_sub(BATCH);
    out.drain(..skip);
    out
}

/// The channel messages to say into the room, oldest first: humans only (no webhook, no
/// bot), with text, after `after`.
pub fn inbound(messages: &Value, after: Option<&str>) -> Vec<(String, String, String, String)> {
    let newer = |id: &str| match after {
        None => true,
        Some(a) => (id.len(), id) > (a.len(), a),
    };
    let mut out: Vec<(String, String, String, String)> = messages
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|m| {
            let id = m.get("id")?.as_str()?;
            if !is_snowflake(id) || !newer(id) {
                return None;
            }
            if m.get("webhook_id").is_some_and(|w| !w.is_null()) || m.pointer("/author/bot").and_then(Value::as_bool) == Some(true) {
                return Some((id.to_owned(), String::new(), String::new(), String::new()));
            }
            let author = m.get("author")?;
            let author_id = author.get("id")?.as_str()?;
            if !is_snowflake(author_id) {
                return None;
            }
            let name: String = author
                .get("username")
                .and_then(Value::as_str)
                .unwrap_or("someone")
                .chars()
                .filter(|c| c.is_alphanumeric() || matches!(c, '_' | '.' | '-'))
                .take(32)
                .collect();
            let text = m.get("content")?.as_str()?.to_owned();
            Some((id.to_owned(), author_id.to_owned(), if name.is_empty() { "someone".into() } else { name }, text))
        })
        .collect();
    out.sort_by(|a, b| (a.0.len(), &a.0).cmp(&(b.0.len(), &b.0)));
    out
}

struct Mirror {
    deployment: Deployment,
    session: Session,
    room: String,
    webhook: String,
    channel: String,
    token: String,
    poster: Poster,
    state: PathBuf,
}

impl Mirror {
    fn log(&self, value: Value) {
        let _ = append_log(&self.session.home, LOG_FILE, &value);
    }

    fn me(&self) -> String {
        std::fs::read(self.session.workspace.join("workspace.json"))
            .ok()
            .and_then(|b| serde_json::from_slice::<Value>(&b).ok())
            .and_then(|v| v.get("subject").and_then(Value::as_str).map(str::to_owned))
            .unwrap_or_default()
    }

    /// Room -> channel. Ok(n posted).
    fn up(&self, state: &mut State) -> Result<usize, String> {
        let since = state.height.map(|h| format!(" --since {h}")).unwrap_or_default();
        let line = format!("tail --in {} --json -n 100000{since}", self.room);
        let outcome = self.deployment.run(&self.session, &line);
        if outcome.ending.word != "ok" {
            return Err(format!("{line}: {}", outcome.ending.line));
        }
        let (_, entries) = feed_of(&outcome.stdout);
        let posts = outbound(&entries, state.height, &self.me());
        let url = if self.webhook.contains('?') { format!("{}&wait=true", self.webhook) } else { format!("{}?wait=true", self.webhook) };
        for (height, text) in &posts {
            let code = self.poster.send("POST", &url, followup(text).to_string().as_bytes())?;
            if !(200..300).contains(&code) {
                return Err(format!("channel webhook answered HTTP {code}"));
            }
            state.height = Some(*height);
            save_state(&self.state, state).map_err(|e| format!("state {}: {e}", self.state.display()))?;
        }
        // Entries the bridge does not post still move the mark.
        if let Some(top) = entries.iter().filter_map(|e| e.get("height").and_then(Value::as_u64)).max() {
            if state.height.is_none_or(|h| top > h) {
                state.height = Some(top);
                save_state(&self.state, state).map_err(|e| format!("state {}: {e}", self.state.display()))?;
            }
        }
        if !posts.is_empty() {
            self.log(json!({"at":now_s(),"room":self.room,"direction":"room->channel","posted":posts.len()}));
        }
        Ok(posts.len())
    }

    /// Channel -> room. Ok(n said).
    fn down(&self, state: &mut State) -> Result<usize, String> {
        let url = match &state.message {
            Some(after) => format!("{}?after={after}&limit=50", self.channel),
            None => format!("{}?limit=50", self.channel),
        };
        let (code, body) = self.poster.get(&url, &[("Authorization", &format!("Bot {}", self.token))])?;
        if !(200..300).contains(&code) {
            return Err(format!("channel read answered HTTP {code}"));
        }
        let messages: Value = serde_json::from_slice(&body).map_err(|e| format!("channel read is not JSON: {e}"))?;
        let mut said = 0;
        let todo = inbound(&messages, state.message.as_deref());
        let skip = todo.len().saturating_sub(BATCH);
        for (id, author, name, text) in todo.into_iter().skip(skip) {
            if !author.is_empty() && !text.trim().is_empty() {
                let file = format!("discord-{id}.txt");
                let dir = self.session.home.join("requests");
                std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
                let text: String = text.chars().take(3500).collect();
                std::fs::write(dir.join(&file), text.as_bytes()).map_err(|e| format!("{file}: {e}"))?;
                let line = format!("say --in {} --via discord --via-id {author} --via-name {name} --file {file}", self.room);
                let outcome = self.deployment.run(&self.session, &line);
                let _ = std::fs::remove_file(dir.join(&file));
                if outcome.ending.word != "ok" {
                    self.log(json!({"at":now_s(),"room":self.room,"direction":"channel->room","message":id,"ending":outcome.ending.line}));
                    return Err(format!("say for message {id}: {}", outcome.ending.line));
                }
                said += 1;
            }
            state.message = Some(id);
            save_state(&self.state, state).map_err(|e| format!("state {}: {e}", self.state.display()))?;
        }
        if said > 0 {
            self.log(json!({"at":now_s(),"room":self.room,"direction":"channel->room","said":said}));
        }
        Ok(said)
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let once = match args.as_slice() {
        [] => false,
        [a] if a == "--once" => true,
        _ => fail("usage: mini-discord-mirror [--once]; configuration is the environment"),
    };
    let room = env_required("MINI_MIRROR_ROOM").unwrap_or_else(|e| fail(e));
    if !is_room_name(&room) {
        fail("MINI_MIRROR_ROOM must be a room name (letters, digits, hyphens)");
    }
    let webhook = env_required("MINI_MIRROR_WEBHOOK_URL").unwrap_or_else(|e| fail(e));
    let channel = env_required("MINI_MIRROR_CHANNEL_URL").unwrap_or_else(|e| fail(e));
    for url in [&webhook, &channel] {
        if !minidregg_discord_entrance::curl::is_plain_url(url) {
            fail("MINI_MIRROR_WEBHOOK_URL and MINI_MIRROR_CHANNEL_URL must be plain URLs");
        }
    }
    let token = env_required("MINI_MIRROR_BOT_TOKEN").unwrap_or_else(|e| fail(e));
    if !token.bytes().all(|b| b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_' | b'-')) {
        fail("MINI_MIRROR_BOT_TOKEN has characters a Discord token does not");
    }
    let home = env_path("MINI_MIRROR_HOME").unwrap_or_else(|e| fail(e));
    let workspace = env_path("MINI_MIRROR_WORKSPACE").unwrap_or_else(|e| fail(e));
    let interval = env_u64("MINI_MIRROR_INTERVAL_S", 30).unwrap_or_else(|e| fail(e)).max(5);
    let spool = match std::env::var("MINI_DISCORD_SPOOL") {
        Ok(v) if !v.is_empty() => env_path("MINI_DISCORD_SPOOL").unwrap_or_else(|e| fail(e)),
        _ => PathBuf::from("/run/mini-discord"),
    };
    let state_dir = home.join("mirror");
    if let Err(e) = std::fs::create_dir_all(&state_dir) {
        fail(format!("{}: {e}", state_dir.display()));
    }
    let mirror = Mirror {
        deployment: Deployment::from_env().unwrap_or_else(|e| fail(e)),
        session: Session { name: "mirror".into(), home, workspace },
        state: state_dir.join(format!("{room}.json")),
        room,
        webhook,
        channel,
        token,
        poster: Poster { curl: PathBuf::from(minidregg_discord_entrance::curl::CURL), spool, max_time_s: 20 },
    };
    loop {
        let mut state = load_state(&mirror.state);
        let up = mirror.up(&mut state);
        let down = mirror.down(&mut state);
        match (&up, &down) {
            (Ok(u), Ok(d)) => eprintln!("mini-discord-mirror: {}: posted {u}, said {d}", mirror.room),
            _ => {
                eprintln!("mini-discord-mirror: {}: up {up:?}, down {down:?}", mirror.room);
                if once {
                    std::process::exit(1);
                }
            }
        }
        if once {
            return;
        }
        std::thread::sleep(Duration::from_secs(interval));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn room_to_channel_skips_bridged_and_own_entries() {
        let out = r#"{"type":"mini-chat-room-v1","room":"commons"}
{"n":1,"height":10,"author":"1","name":"alice","kind":"say","text":"hi @everyone","via":null}
{"n":2,"height":11,"author":"9","name":"bridge","kind":"say","text":"from discord","via":{"network":"discord","id":"4","name":"zed"}}
{"n":3,"height":12,"author":"9","name":"bridge","kind":"say","text":"the bridge itself","via":null}
{"n":4,"height":13,"author":"2","name":"bob","kind":"react","text":"+1","via":null}
{"n":5,"height":14,"author":"2","name":"b*ob","kind":"say","text":"yo","via":null}"#;
        let (state, entries) = feed_of(out);
        assert_eq!(state["room"], "commons");
        let posts = outbound(&entries, None, "9");
        assert_eq!(posts, vec![(10, "**alice**: hi @\u{200b}everyone".to_owned()), (14, "**bob**: yo".to_owned())]);
        assert_eq!(outbound(&entries, Some(10), "9"), vec![(14, "**bob**: yo".to_owned())]);
    }

    #[test]
    fn channel_to_room_takes_humans_only_oldest_first() {
        let messages = json!([
            {"id":"1003","content":"third","author":{"id":"77","username":"zed one"}},
            {"id":"1002","content":"**alice**: hi","webhook_id":"5","author":{"id":"5","username":"mirror","bot":true}},
            {"id":"1001","content":"first","author":{"id":"77","username":"zed"}},
            {"id":"999","content":"old","author":{"id":"77","username":"zed"}}
        ]);
        let todo = inbound(&messages, Some("999"));
        assert_eq!(todo.len(), 3);
        assert_eq!(todo[0], ("1001".into(), "77".into(), "zed".into(), "first".into()));
        assert_eq!(todo[1].0, "1002");
        assert!(todo[1].1.is_empty(), "a webhook message is passed over, never said");
        assert_eq!(todo[2], ("1003".into(), "77".into(), "zedone".into(), "third".into()));
    }

    #[test]
    fn room_names() {
        assert!(is_room_name("commons"));
        assert!(!is_room_name("../x"));
        assert!(!is_room_name(""));
    }
}
