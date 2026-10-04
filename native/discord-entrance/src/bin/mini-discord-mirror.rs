//! `mini-discord-mirror`: a RUNNER that bridges one Mini room and one Discord channel,
//! both ways.
//!
//! It is not part of the interactions endpoint. It holds its OWN session: its own key, its
//! own workspace, its own membership of the room (the founder invited it like anyone else,
//! so it has its own stream). Every Mini step is one `mini shell --line` through the same
//! forced command as ssh and Discord, so every read and every append is signed by the
//! bridge's key, metered and refusable like anyone's.
//!
//! Room -> channel: `tail --in ROOM --json --discover FILE` (signed per-stream pages);
//! each new `say` is posted to the channel webhook as `name: text`.
//! Channel -> room: the channel's messages after the last one seen (Discord REST, the bot
//! token); each human message becomes `say --in ROOM --via discord --via-id ID --via-name NAME
//! --file F`: the BRIDGE says it, and the payload names the Discord author. It never signs as
//! a friend; a reader sees `bridge via discord NAME#ID: text`.
//!
//! A PRIVATE room is never mirrored. Opened text from a sealed room reaches this process
//! only inside a `tail --json` feed whose header and entries say `"private": true` (the
//! native client stamps both); `PublicFeed` is the only way into `outbound`, and it refuses
//! a feed that says private, says nothing, or mixes the two. There is no setting that
//! lifts this: re-publishing opened text outside the sealed room is exactly what the room
//! key exists to prevent. DEVNET QUALITY; PRIVACY NOT AUDITED.
//!
//! Loop prevention, both directions:
//! * a room entry that carries `via` (anything a bridge said), or that the bridge's own
//!   subject signed, is never posted to the channel;
//! * a channel message from a webhook (`webhook_id`: what this mirror posted) or from a bot
//!   is never said into the room.
//!
//! The webhook URL and the bot token are never this process's: the key broker
//! (native/mini-keys) holds them and posts to the one configured webhook / reads the one
//! configured channel on its behalf (`discord-post`, `discord-read`; this account must hold
//! the broker's `discord` role). Under split tenancy the mirror runs as its own session's
//! account, so it reads and writes only its own session home.
//!
//! Configuration is the environment, and holds no secret: `MINI_MIRROR_ROOM`,
//! `MINI_MIRROR_BROKER` (the broker client config, default `/etc/mini/keys-client.json`),
//! `MINI_MIRROR_PUBLISH_ROOM_TO_CHANNEL=yes` (authorized disclosure mapping),
//! `MINI_MIRROR_HOME`, `MINI_MIRROR_WORKSPACE`, `MINI_MIRROR_INTERVAL_S` (default 30),
//! and the deployment variables of `mini-discord` (`MINI_SHELL_WRAPPER`
//! `MINI_CLIENT` `MINI_HOST` `MINI_CONFIG` `MINI_SOCKET`). One argument is accepted: `--once`.
//! `MINI_MIRROR_WEBHOOK_URL`, `MINI_MIRROR_CHANNEL_URL` and `MINI_MIRROR_BOT_TOKEN` refuse
//! to start the mirror: a secret in a session's environment is the shape this replaced.

use std::path::{Path, PathBuf};
use mini_sdk::custody::{Delivery, DeliveryState};
use mini_sdk::store::{self as custody, Record};
use std::time::Duration;

use mini_keys::client::Broker;
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

/// Durable page/cursor state. A malformed state is a stop, never a fresh start.
#[derive(Debug, Default, Clone, PartialEq)]
pub struct State { pub height: Option<u64>, pub message: Option<String>, pub cursors: serde_json::Map<String,Value>, pub scan: Value }
fn load_state(p:&Path)->Result<State,String>{
    let v=custody::read_json(p)?.unwrap_or(json!({}));
    if !v.is_object() || (!v["height"].is_null() && !v["height"].is_u64()) || (!v["message"].is_null() && !v["message"].as_str().is_some_and(is_snowflake)) || (!v["cursors"].is_null() && !v["cursors"].is_object()) || (!v["scan"].is_null() && !v["scan"].is_object()) {return Err("invalid mirror state schema".into())}
    if v["cursors"].as_object().is_some_and(|m|m.iter().any(|(k,v)|!is_snowflake(k)||!v.is_u64())){return Err("invalid stream cursor".into())}
    Ok(State{height:v["height"].as_u64(),message:v["message"].as_str().map(str::to_owned),
        cursors:v["cursors"].as_object().cloned().unwrap_or_default(),scan:v["scan"].clone()})
}
fn save_state(p:&Path,s:&State)->Result<(),String>{Ok(custody::atomic_json(p,&json!({"version":2,"height":s.height,"message":s.message,"cursors":s.cursors,"scan":s.scan}))?)}

/// The refusal a private room gets. `main` stops the bridge on it (it is configuration, not
/// a transient failure, so it is never retried and never skipped past).
pub const PRIVATE_ROOM_REFUSAL: &str = "room is private";

/// A room entry that came out of a room the native client stated is PUBLIC. The inner value
/// is private to this constructor: `outbound` cannot be handed an entry of unknown privacy.
#[derive(Debug, Clone, PartialEq)]
pub struct PublicEntry(Value);

impl PublicEntry {
    pub fn get(&self, key: &str) -> Option<&Value> {
        self.0.get(key)
    }
}

/// The feed of a PUBLIC room. The only constructor refuses (a) a header that says
/// `"private": true`, (b) a header or entry with no boolean `private` (an older client that
/// cannot say is not a client that says "public"), (c) an entry that disagrees with its
/// header, and (d) an entry that carries the `sealed` mark of an opened private line.
#[derive(Debug, Clone, PartialEq)]
pub struct PublicFeed {
    pub header: Value,
    pub entries: Vec<PublicEntry>,
}

impl PublicFeed {
    pub fn from_docs(docs: &[Value]) -> Result<Self, String> {
        let header = docs.first().ok_or("empty source page")?;
        match header.get("private").and_then(Value::as_bool) {
            Some(false) => {}
            Some(true) => {
                return Err(format!(
                    "{PRIVATE_ROOM_REFUSAL}: its opened text is never published to a Discord channel (not configurable); a bridge mirrors public rooms only"
                ))
            }
            None => {
                return Err(format!(
                    "{PRIVATE_ROOM_REFUSAL} or unknowable: the native client does not state whether this room is private, and an unstated room is not treated as public"
                ))
            }
        }
        let mut entries = Vec::new();
        for entry in &docs[1..] {
            match entry.get("private").and_then(Value::as_bool) {
                Some(false) => {}
                Some(true) => return Err(format!("{PRIVATE_ROOM_REFUSAL}: an entry of a public-looking feed is marked private")),
                None => return Err(format!("{PRIVATE_ROOM_REFUSAL} or unknowable: an entry does not state whether it is private")),
            }
            if entry.get("sealed").is_some_and(|sealed| !sealed.is_null() && sealed != &Value::Bool(false)) {
                return Err(format!("{PRIVATE_ROOM_REFUSAL}: an entry carries the sealed mark of an opened private line"));
            }
            entries.push(PublicEntry(entry.clone()));
        }
        Ok(Self { header: header.clone(), entries })
    }
}

/// The room's feed from `tail --json`: (header line, entries), refusing a private room.
pub fn feed_of(stdout: &str) -> Result<PublicFeed, String> {
    let docs: Vec<Value> = serde_json::Deserializer::from_str(stdout)
        .into_iter::<Value>()
        .collect::<Result<_, _>>()
        .map_err(|e| format!("incomplete source page: {e}"))?;
    PublicFeed::from_docs(&docs)
}

/// The channel lines for room entries above `height`: `say` and raw text only, never an
/// entry a bridge said (`via`) or one the bridge itself signed (`me`). Entries are
/// `PublicEntry`: there is no way to pass one that was not stated public.
pub fn outbound(entries: &[PublicEntry], height: Option<u64>, me: &str) -> Vec<(u64, String)> {
    let mut out: Vec<(u64, String)> = entries
        .iter()
        .map(|entry| &entry.0)
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
            let source=match (e["cell"].as_str(),e["sequence"].as_u64()) { (Some(cell),Some(seq))=>format!("\n[Mini source {cell}:{seq}]"),_=>String::new()};
            let budget=DISCORD_LIMIT-source.chars().count();
            let line=if line.chars().count()>budget {format!("{}… [text truncated; open Mini source]",line.chars().take(budget-42).collect::<String>())}else{line};
            Some((h, format!("{line}{source}")))
        })
        .collect();
    out.sort_by_key(|entry|entry.0);
    out.truncate(BATCH);
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
    /// The mirrored channel's API URL, as the broker reports it (not a secret);
    /// part of the bridge's custody binding.
    channel: String,
    broker: Broker,
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

    fn custody_root(&self)->PathBuf {self.state.parent().unwrap().join(format!("{}-operations",self.room))}
    fn binding(&self)->Value {json!({"room":self.room,"channel":self.channel,"subject":self.me(),"workspace":self.session.workspace})}

    /// Bounded signed source pages; advance only entries actually examined/published.
    fn up(&self,state:&mut State)->Result<usize,String>{
        let requests=self.session.home.join("requests");custody::private_dir(&requests)?;
        let file=format!("mirror-{}-discovery.json",self.room);
        custody::atomic_json(&requests.join(&file),&json!({"type":"mini-resident-discovery-v1","cursors":state.cursors,"retained":[]}))?;
        let line=format!("tail --in {} --json -n {} --discover {}",self.room,BATCH,requests.join(&file).display());
        let result=self.deployment.run(&self.session,&line);
        if result.ending.word!="ok" {return Err(result.ending.line)}
        // Parsing must be complete; silently flattening a truncated JSON stream loses events.
        let docs:Vec<Value>=serde_json::Deserializer::from_str(&result.stdout).into_iter::<Value>().collect::<Result<_,_>>().map_err(|e|format!("incomplete source page: {e}"))?;
        // BEFORE anything else reads an entry: a private room ends the page here.
        let public=PublicFeed::from_docs(&docs)?;
        let header=&public.header;
        if header["type"]!="mini-chat-room-v1" || !header["discoveryCursors"].is_object() || header["selectedEntries"].as_u64()!=Some((docs.len()-1) as u64) {return Err("native client lacks signed discovery pages".into())}
        if header["unreadable"].as_array().is_none_or(|v|!v.is_empty()) {return Err("source streams unreadable; cursor retained".into())}
        let mut posted=0;
        for pe in public.entries.iter().take(BATCH){
            let e=&pe.0;
            let cell=e["cell"].as_str().filter(|s|is_snowflake(s)).ok_or("invalid source cell")?;
            let seq=e["sequence"].as_u64().filter(|n|*n>0).ok_or("invalid source sequence")?;
            if state.cursors.get(cell).and_then(Value::as_u64).is_some_and(|seen|seq<=seen){continue}
            let posts=outbound(std::slice::from_ref(pe),state.height,&self.me());
            if let Some((_,text))=posts.first(){
                let key=format!("up-{cell}-{seq}");
                let mut record=Record::lock(&self.custody_root(),&key)?.ok_or("publication record busy")?;
                let binding=json!({"bridge":self.binding(),"source":{"cell":cell,"sequence":seq,"author":e["author"],"kind":e["kind"],"text":e["text"],"via":e["via"]}});
                let delivery=Delivery::open(binding,record.value.clone()).map_err(|e|format!("publication {cell}:{seq}: {e}"))?;
                match delivery.state() {
                    DeliveryState::Completed(_)=>{}
                    DeliveryState::Unknown=>return Err(format!("publication {cell}:{seq} UNKNOWN; inspect Discord and resolve before continuing")),
                    DeliveryState::Fresh=>{
                        record.save(delivery.start(now_s())?)?;
                        let answer=self.broker.call(&json!({"op":"discord-post","body":followup(text)}),Duration::from_secs(40)).map_err(|r|format!("publication {cell}:{seq} UNKNOWN ({r}); no automatic repost"))?;
                        let code=answer["status"].as_u64().unwrap_or(0) as u16;
                        if !(200..300).contains(&code){return Err(format!("publication {cell}:{seq} UNKNOWN (HTTP {code}); no automatic repost"))}
                        record.save(Delivery::open(delivery.binding,record.value.clone())?.complete(json!({"http":code}),now_s())?)?;
                        posted+=1;
                    }
                }
            }
            state.cursors.insert(cell.into(),json!(seq));save_state(&self.state,state)?;
        }
        Ok(posted)
    }

    fn page_path(&self,n:u64)->PathBuf{self.custody_root().join(format!("page-{n}.json"))}
    /// Scan backwards from a fixed head to the old watermark, retaining bounded
    /// pages. Drain oldest first. This does not assume `after` selects oldest N.
    fn down(&self,state:&mut State)->Result<usize,String>{
        custody::private_dir(&self.custody_root())?;
        if state.scan.is_null(){state.scan=json!({"phase":"scan","pages":0,"before":null,"boundary":state.message,"offset":0});save_state(&self.state,state)?;}
        if state.scan["phase"]=="scan" {
            let page=self.broker.call(&json!({"op":"discord-read","before":state.scan["before"],"limit":50}),Duration::from_secs(40)).map_err(|r|format!("channel read: {r}"))?;
            let code=page["status"].as_u64().unwrap_or(0) as u16;
            let body=page["body"].as_str().unwrap_or("").as_bytes().to_vec();
            if !(200..300).contains(&code){return Err(format!("channel read HTTP {code}"))}
            let v:Value=serde_json::from_slice(&body).map_err(|e|e.to_string())?;
            let rows=v.as_array().ok_or("channel response is not an array")?;
            if rows.len()>50{return Err("channel exceeded page bound".into())}
            let mut ids=Vec::new();for row in rows {ids.push(row["id"].as_str().filter(|s|is_snowflake(s)).ok_or("channel message lacks valid source id")?);}
            ids.sort_by(|a,b|(a.len(),a).cmp(&(b.len(),b)));
            let oldest=ids.first().copied();
            if let (Some(old),Some(before))=(oldest,state.scan["before"].as_str()){if (old.len(),old)>=(before.len(),before){return Err("channel pagination made no progress".into())}}
            let boundary=state.scan["boundary"].as_str();
            let reached=rows.len()<50 || oldest.is_some_and(|old|boundary.is_some_and(|b|(old.len(),old)<=(b.len(),b)));
            let todo=inbound(&v,boundary);
            // Malformed non-bot records cannot silently move the source watermark.
            let expected=ids.iter().filter(|id|boundary.is_none_or(|b|(id.len(),**id)>(b.len(),b))).count();
            if todo.len()!=expected{return Err("channel page contains unreadable source messages; cursor retained".into())}
            let n=state.scan["pages"].as_u64().ok_or("invalid page count")?;
            custody::atomic_json(&self.page_path(n),&json!(todo))?;
            state.scan["pages"]=json!(n+1);state.scan["before"]=json!(oldest);
            if reached {state.scan["phase"]=json!("drain");}
            save_state(&self.state,state)?;
            return Ok(0)
        }
        let n=state.scan["pages"].as_u64().filter(|n|*n>0).ok_or("invalid retained scan")?-1;
        let page=custody::read_json(&self.page_path(n))?.ok_or("retained channel page missing")?;
        let todo:Vec<(String,String,String,String)>=serde_json::from_value(page).map_err(|e|e.to_string())?;
        let offset=state.scan["offset"].as_u64().ok_or("invalid page offset")? as usize;
        let mut said=0;
        for (i,(id,author,name,text)) in todo.iter().enumerate().skip(offset).take(BATCH){
            if !author.is_empty() && !text.trim().is_empty(){
                let dir=self.session.home.join("requests");custody::private_dir(&dir)?;
                let file=format!("discord-{id}.txt");
                // Keep the exact first observed source bytes, not a later message edit.
                let path=dir.join(&file);
                use std::io::Write;use std::os::unix::fs::OpenOptionsExt;
                let mut f=std::fs::OpenOptions::new().write(true).create_new(true).mode(0o600).open(&path);
                match &mut f {Ok(f)=>{f.write_all(text.as_bytes()).and_then(|_|f.sync_all()).map_err(|e|e.to_string())?},Err(e) if e.kind()==std::io::ErrorKind::AlreadyExists=>{},Err(e)=>return Err(e.to_string())}
                let operation=dir.join(format!("discord-{}-{id}.operation.json",self.room));
                let line=format!("say --in {} --via discord --via-id {author} --via-name {name} --operation-record {} --file {file}",self.room,operation.display());
                let outcome=self.deployment.run(&self.session,&line);
                if outcome.ending.word!="ok" {self.log(json!({"at":now_s(),"sourceMessage":id,"operation":operation,"ending":outcome.ending.line}));return Err(format!("message {id}: {}; exact operation retained",outcome.ending.line))}
                said+=1;
            }
            state.message=Some(id.clone());state.scan["offset"]=json!(i+1);save_state(&self.state,state)?;
        }
        if state.scan["offset"].as_u64().unwrap_or(0) as usize>=todo.len(){
            if n==0 {state.scan=Value::Null;}else{state.scan["pages"]=json!(n);state.scan["offset"]=json!(0);}
            save_state(&self.state,state)?;
        }
        Ok(said)
    }

}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let resolution = match args.as_slice() {
        [a,cell,seq,message] if a=="--resolve-up" && is_snowflake(cell) && seq.parse::<u64>().is_ok_and(|n|n>0) && is_snowflake(message) => Some((cell.clone(),seq.clone(),message.clone())),
        _=>None,
    };
    let once = match args.as_slice() {
        [] => false,
        [a] if a == "--once" => true,
        _ if resolution.is_some()=>true,
        _ => fail("usage: mini-discord-mirror [--once | --resolve-up CELL SEQUENCE DISCORD_MESSAGE_ID]; configuration is the environment"),
    };
    if env_required("MINI_MIRROR_PUBLISH_ROOM_TO_CHANNEL").as_deref()!=Ok("yes") {fail("set MINI_MIRROR_PUBLISH_ROOM_TO_CHANNEL=yes only for an authorized room-to-channel publication mapping")}
    let room = env_required("MINI_MIRROR_ROOM").unwrap_or_else(|e| fail(e));
    if !is_room_name(&room) {
        fail("MINI_MIRROR_ROOM must be a room name (letters, digits, hyphens)");
    }
    for gone in ["MINI_MIRROR_WEBHOOK_URL", "MINI_MIRROR_CHANNEL_URL", "MINI_MIRROR_BOT_TOKEN"] {
        if std::env::var_os(gone).is_some() {
            fail(format!("{gone} is set: the mirror no longer takes Discord secrets; the key broker holds the webhook, channel and bot token (mini-keys discord-mirror secrets). Remove it from the environment."));
        }
    }
    let broker_config = match std::env::var("MINI_MIRROR_BROKER") {
        Ok(v) if !v.is_empty() => env_path("MINI_MIRROR_BROKER").unwrap_or_else(|e| fail(e)),
        _ => PathBuf::from(mini_keys::client::CLIENT_CONFIG),
    };
    let broker = Broker::load(&broker_config, unsafe { libc::geteuid() }).unwrap_or_else(|e| fail(e));
    let hello = mini_keys::client::hello(&broker).unwrap_or_else(|e| fail(e));
    let channel = hello["discordChannel"].as_str().map(str::to_owned)
        .unwrap_or_else(|| fail("this account holds no discord role at the key broker, or the broker holds no mirror secrets"));
    let home = env_path("MINI_MIRROR_HOME").unwrap_or_else(|e| fail(e));
    let workspace = env_path("MINI_MIRROR_WORKSPACE").unwrap_or_else(|e| fail(e));
    if home.to_string_lossy().chars().any(char::is_whitespace) {fail("MINI_MIRROR_HOME cannot contain whitespace: native chat path options use whitespace-separated words")}

    let interval = env_u64("MINI_MIRROR_INTERVAL_S", 30).unwrap_or_else(|e| fail(e)).max(5);
    let state_dir = home.join("mirror");
    if let Err(e) = custody::private_dir(&state_dir) {
        fail(format!("{}: {e}", state_dir.display()));
    }
    let mirror = Mirror {
        deployment: Deployment::from_env().unwrap_or_else(|e| fail(e)),
        session: Session { name: "mirror".into(), home, workspace },
        state: state_dir.join(format!("{room}.json")),
        room,
        channel,
        broker,
    };
    // One process owns this bridge configuration and all its page files.
    let mut lease=Record::lock(&state_dir,&format!("{}-bridge",mirror.room)).unwrap_or_else(|e|fail(e)).unwrap_or_else(||fail("bridge already running"));
    let binding=mirror.binding();
    if binding["subject"].as_str().is_none_or(str::is_empty){fail("bridge workspace subject unavailable")}
    if let Some(v)=&lease.value {if v!=&binding{fail("bridge identity/destination changed; use separate custody")}}else{lease.save(binding).unwrap_or_else(|e|fail(e));}
    if let Some((cell,seq,message))=resolution {
        let mut record=Record::lock(&mirror.custody_root(),&format!("up-{cell}-{seq}")).unwrap_or_else(|e|fail(e)).unwrap_or_else(||fail("publication record busy"));
        let v=record.value.clone().unwrap_or_else(||fail("no retained publication to resolve"));
        if v["binding"]["bridge"]!=mirror.binding(){fail("publication bridge binding differs")}
        let resolved=Delivery::open(v["binding"].clone(),Some(v)).and_then(|d|d.complete(json!({"operatorConfirmedDiscordMessage":message}),now_s()))
            .unwrap_or_else(|e|fail(e));
        record.save(resolved).unwrap_or_else(|e|fail(e));
        eprintln!("retained publication resolved from operator-supplied destination evidence; no message sent");return;
    }
    loop {
        let mut state = load_state(&mirror.state).unwrap_or_else(|e|fail(e));
        let up = mirror.up(&mut state);
        // A private room is a configuration error, not a transient one: stop, do not
        // retry, and do not run the channel-to-room direction into a sealed room either.
        if let Err(why) = &up { if why.starts_with(PRIVATE_ROOM_REFUSAL) { fail(format!("{}: {why}", mirror.room)) } }
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
        let out = r#"{"type":"mini-chat-room-v1","room":"commons","private":false}
{"n":1,"height":10,"author":"1","name":"alice","kind":"say","text":"hi @everyone","via":null,"private":false}
{"n":2,"height":11,"author":"9","name":"bridge","kind":"say","text":"from discord","via":{"network":"discord","id":"4","name":"zed"},"private":false}
{"n":3,"height":12,"author":"9","name":"bridge","kind":"say","text":"the bridge itself","via":null,"private":false}
{"n":4,"height":13,"author":"2","name":"bob","kind":"react","text":"+1","via":null,"private":false}
{"n":5,"height":14,"author":"2","name":"b*ob","kind":"say","text":"yo","via":null,"private":false}"#;
        let PublicFeed { header: state, entries } = feed_of(out).unwrap();
        assert_eq!(state["room"], "commons");
        let posts = outbound(&entries, None, "9");
        assert_eq!(posts, vec![(10, "**alice**: hi @\u{200b}everyone".to_owned()), (14, "**bob**: yo".to_owned())]);
        assert_eq!(outbound(&entries, Some(10), "9"), vec![(14, "**bob**: yo".to_owned())]);
    }

    // ---- a private room's opened text can never reach the channel ----

    fn feed(header: Value, entries: Vec<Value>) -> String {
        std::iter::once(header).chain(entries).map(|v| v.to_string()).collect::<Vec<_>>().join("\n")
    }
    fn say(private: Value) -> Value {
        json!({"n":1,"height":10,"author":"1","name":"alice","kind":"say","text":"the lab is at seven","via":null,"private":private})
    }

    #[test]
    fn a_private_room_feed_is_refused_by_name_and_yields_no_entry_to_publish() {
        let sealed = feed(json!({"type":"mini-chat-room-v1","room":"hush","private":true}), vec![say(json!(true))]);
        let refusal = feed_of(&sealed).unwrap_err();
        assert!(refusal.starts_with(PRIVATE_ROOM_REFUSAL) && refusal.contains("never published"), "{refusal}");
        // A forged header cannot launder a private entry, nor an entry its header.
        let laundered = feed(json!({"type":"mini-chat-room-v1","room":"hush","private":false}), vec![say(json!(true))]);
        assert!(feed_of(&laundered).unwrap_err().contains("marked private"));
        let mixed = feed(json!({"type":"mini-chat-room-v1","room":"hush","private":true}), vec![say(json!(false))]);
        assert!(feed_of(&mixed).is_err());
        // The opened-line mark of a sealed read refuses even under a "public" stamp.
        let mut marked = say(json!(false));
        marked["sealed"] = json!(true);
        let opened = feed(json!({"type":"mini-chat-room-v1","room":"hush","private":false}), vec![marked]);
        assert!(feed_of(&opened).unwrap_err().contains("sealed mark"));
    }

    #[test]
    fn a_feed_that_does_not_state_privacy_is_not_treated_as_public() {
        // The client before the stamp, a string "false", null, a number: none is a boolean false.
        for header in [json!({"type":"mini-chat-room-v1"}), json!({"private":"false"}), json!({"private":null}), json!({"private":0})] {
            let refusal = feed_of(&feed(header.clone(), vec![])).unwrap_err();
            assert!(refusal.contains("does not state"), "{header}: {refusal}");
        }
        let unstated_entry = feed(json!({"type":"mini-chat-room-v1","private":false}), vec![say(Value::Null)]);
        assert!(feed_of(&unstated_entry).unwrap_err().contains("does not state"));
        let missing_entry = feed(json!({"type":"mini-chat-room-v1","private":false}),
            vec![json!({"n":1,"height":10,"author":"1","kind":"say","text":"x","via":null})]);
        assert!(feed_of(&missing_entry).is_err());
        assert!(feed_of("").unwrap_err().contains("empty"));
        assert!(feed_of("{\"private\":false}\n{").unwrap_err().contains("incomplete"));
    }

    #[test]
    fn the_mirror_makes_no_request_and_moves_no_cursor_for_a_private_room() {
        use minidregg_discord_entrance::http::{read_request, write_response};
        use std::sync::{atomic::{AtomicUsize, Ordering}, Arc};
        let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = format!("http://{}", listener.local_addr().unwrap());
        let count = Arc::new(AtomicUsize::new(0));
        let remote = count.clone();
        std::thread::spawn(move || {
            for stream in listener.incoming() {
                let mut stream = stream.unwrap();
                let _ = read_request(&mut stream);
                remote.fetch_add(1, Ordering::SeqCst);
                let _ = write_response(&mut stream, 204, "No Content", "application/json", b"");
            }
        });
        let m = test_mirror("private", addr);
        let mut s = json!({"type":"mini-chat-room-v1","private":true,"selectedEntries":1,"discoveryCursors":{"42":1},"unreadable":[]}).to_string() + "\n";
        s += &(json!({"height":1,"cell":"42","sequence":1,"author":"7","name":"alice","kind":"say","via":null,"private":true,"text":"PRIVATE-OPENED-TEXT"}).to_string() + "\n");
        std::fs::write(m.session.home.join("feed.json"), s).unwrap();
        let mut state = State::default();
        let refusal = m.up(&mut state).unwrap_err();
        assert!(refusal.starts_with(PRIVATE_ROOM_REFUSAL), "{refusal}");
        assert_eq!(count.load(Ordering::SeqCst), 0, "no webhook request for a private room");
        assert!(state.cursors.is_empty() && !m.state.exists(), "no cursor or state is written for it");
        assert!(!m.custody_root().join("up-42-1.json").exists());
        // The same bridge on a public page still publishes (the control: the refusal is about privacy, not breakage).
        page(&m, 1, 2);
        assert_eq!(m.up(&mut state).unwrap(), 1);
        assert_eq!(count.load(Ordering::SeqCst), 1);
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
    /// A real key broker (same account, singleAccount) holding the mirror's
    /// secrets for the fake Discord at `api`.
    fn test_broker(home:&Path, api:&str)->(Broker,String) {
        use std::os::unix::fs::PermissionsExt;
        let keys=home.join("keys");custody::private_dir(&keys).unwrap();
        for sub in ["run","state"] {custody::private_dir(&keys.join(sub)).unwrap();}
        let channel=format!("{api}/channel");
        let secrets=keys.join("discord-mirror.json");
        std::fs::write(&secrets,json!({"type":"mini-discord-mirror-secrets-v1","webhookUrl":format!("{api}/webhook"),"channelUrl":channel,"botToken":"fake.token"}).to_string()).unwrap();
        std::fs::set_permissions(&secrets,std::fs::Permissions::from_mode(0o600)).unwrap();
        let me=unsafe{libc::geteuid()};
        let config=json!({"type":"mini-keys-broker-v1","socket":keys.join("run/b.sock"),"audit":keys.join("state/audit.jsonl"),
            "spool":keys.join("state/spool"),"singleAccount":true,"peers":[{"role":"discord","uids":[me]}],"discord":{"mirror":secrets}});
        std::fs::write(keys.join("broker.json"),config.to_string()).unwrap();
        std::fs::set_permissions(keys.join("broker.json"),std::fs::Permissions::from_mode(0o644)).unwrap();
        let (server,listener)=mini_keys::server::Broker::start(mini_keys::server::Config::load(&keys.join("broker.json"),me).unwrap()).unwrap();
        std::thread::spawn(move||server.serve(listener));
        let broker=Broker::new(keys.join("run/b.sock"),me);
        assert_eq!(mini_keys::client::hello(&broker).unwrap()["discordChannel"],channel.as_str());
        (broker,channel)
    }
    fn test_mirror(tag:&str, api:String)->Mirror {
        use std::os::unix::fs::PermissionsExt;
        let home=std::env::temp_dir().join(format!("mirror-{tag}-{}",std::process::id()));
        let _=std::fs::remove_dir_all(&home);std::fs::create_dir_all(&home).unwrap();
        std::fs::set_permissions(&home,std::fs::Permissions::from_mode(0o700)).unwrap();
        let home=home.canonicalize().unwrap();
        for sub in ["workspace","requests","mirror"] {custody::private_dir(&home.join(sub)).unwrap();}
        std::fs::write(home.join("workspace/workspace.json"),r#"{"subject":"9"}"#).unwrap();
        let wrapper=home.join("wrapper");
        std::fs::write(&wrapper,"#!/bin/sh\ncase \"$SSH_ORIGINAL_COMMAND\" in\n tail*) cat \"$6/feed.json\" ;;\n *) printf '%s\\n' \"$SSH_ORIGINAL_COMMAND\" >> \"$6/says.log\" ;;\nesac\n").unwrap();
        std::fs::set_permissions(&wrapper,std::fs::Permissions::from_mode(0o700)).unwrap();
        let (broker,channel)=test_broker(&home,&api);
        Mirror{deployment:Deployment{wrapper,mini:"/fixed/mini".into(),host:"/fixed/host".into(),config:"/fixed/config".into(),socket:"/fixed/socket".into(),timeout:Duration::from_secs(2),runner:None},session:Session{name:"mirror".into(),workspace:home.join("workspace"),home:home.clone()},room:"commons".into(),channel,broker,state:home.join("mirror/commons.json")}
    }
    fn page(m:&Mirror,start:u64,end:u64){
        let mut s=json!({"type":"mini-chat-room-v1","private":false,"selectedEntries":end-start,"discoveryCursors":{"42":end-1},"unreadable":[]}).to_string()+"\n";
        for n in start..end{s+=&(json!({"height":n,"cell":"42","sequence":n,"author":"7","name":"alice","kind":"say","via":null,"private":false,"text":format!("entry-{n}")}).to_string()+"\n");}
        std::fs::write(m.session.home.join("feed.json"),s).unwrap();
    }
    #[test] fn outbound_pages_restart_and_unknown_never_repost(){
        use minidregg_discord_entrance::http::{read_request,write_response};
        use std::sync::{Arc,atomic::{AtomicUsize,Ordering}};
        let listener=std::net::TcpListener::bind("127.0.0.1:0").unwrap();let addr=format!("http://{}",listener.local_addr().unwrap());
        let count=Arc::new(AtomicUsize::new(0));let remote=count.clone();
        std::thread::spawn(move||{for stream in listener.incoming(){let mut stream=stream.unwrap();let _=read_request(&mut stream).unwrap();let n=remote.fetch_add(1,Ordering::SeqCst);if n!=45{let _=write_response(&mut stream,204,"No Content","application/json",b"");}}});
        let m=test_mirror("up",addr);let mut state=State::default();
        for (start,end) in [(1,21),(21,41),(41,46)]{page(&m,start,end);assert_eq!(m.up(&mut state).unwrap(),(end-start) as usize);state=load_state(&m.state).unwrap();}
        assert_eq!(count.load(Ordering::SeqCst),45);assert_eq!(state.cursors["42"],45);
        // A crash after durable success but before the cursor write reuses success.
        state.cursors.insert("42".into(),json!(44));page(&m,45,46);assert_eq!(m.up(&mut state).unwrap(),0);assert_eq!(count.load(Ordering::SeqCst),45);
        page(&m,46,47);assert!(m.up(&mut state).is_err());assert_eq!(count.load(Ordering::SeqCst),46);
        state=load_state(&m.state).unwrap();assert!(m.up(&mut state).unwrap_err().contains("UNKNOWN"));assert_eq!(count.load(Ordering::SeqCst),46);
    }
    #[test] fn channel_backfill_retains_all_115_across_restart_and_small_drains(){
        use minidregg_discord_entrance::http::{read_request,write_response};
        let listener=std::net::TcpListener::bind("127.0.0.1:0").unwrap();let addr=format!("http://{}",listener.local_addr().unwrap());
        std::thread::spawn(move||{for stream in listener.incoming(){let mut stream=stream.unwrap();let req=read_request(&mut stream).unwrap();let before=req.query.split("before=").nth(1).and_then(|x|x.split('&').next()).and_then(|x|x.parse::<u64>().ok()).unwrap_or(1116);let rows:Vec<_>=(1001..=1115).rev().filter(|id|*id<before).take(50).map(|id|json!({"id":id.to_string(),"content":format!("message-{id}"),"author":{"id":"77","username":"alice"}})).collect();let body=json!(rows).to_string();let _=write_response(&mut stream,200,"OK","application/json",body.as_bytes());}});
        let m=test_mirror("down",addr);let mut state=State::default();let mut said=0;
        for _ in 0..20{said+=m.down(&mut state).unwrap();state=load_state(&m.state).unwrap();if state.scan.is_null(){break}}
        assert_eq!(said,115);assert_eq!(state.message.as_deref(),Some("1115"));assert!(state.scan.is_null());
        let log=std::fs::read_to_string(m.session.home.join("says.log")).unwrap();let rows:Vec<_>=log.lines().collect();assert_eq!(rows.len(),115);
        assert!(rows[0].contains("discord-commons-1001.operation.json"));assert!(rows[114].contains("discord-commons-1115.operation.json"));
        assert!(rows.iter().all(|l|l.contains("--via discord --via-id 77 --via-name alice --operation-record")));
    }

}
