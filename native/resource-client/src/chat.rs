//! Chat in a room (PLACE §2.3): `say`, `tail`, `topic`, `pin`/`unpin`, `react`,
//! and the room template `chat new|invite|join|enter|rooms|name`.
//!
//! A room `R` is a declared cell whose law lets only its founder write it. It
//! holds the ROSTER: field 2 is the founder's subject, and member `k` (from 1)
//! is field `2k+1` (subject) and field `2k+2` (that member's stream cell); field
//! 1 is the one every declared cell is born with. Every
//! member has ONE stream, a `stream` cell born `--in R` under the member's
//! author law (every write is signed by that member). The founder births every
//! stream, owns it and pays for it (K-STREAM: workspaces without a birth
//! context cannot birth; a birth into a room is owned by its creator,
//! `RoomBirthGate.room_birth_owner_is_creator`). A member speaks with its room
//! grant (`observe`+`append` `under R`), which the Host accepts on its own
//! stream and the author law refuses on anyone else's; a kick revokes that
//! grant, and the member holds nothing else on the stream.
//!
//! Every utterance is one append to the speaker's own stream. The entry's
//! kernel fields are the room topic (`topic`), an optional recipient (`to`) and
//! an optional reference to another entry (`ref` = cell, sequence). The text is
//! a typed JSON payload, so control entries are ordinary appends under the same
//! author law:
//!   {"type":"say","text":T[,"via":"discord","author":{"id","name"}]}
//!   {"type":"topic","text":T}          ref: none
//!   {"type":"pin"}                     ref: the pinned entry
//!   {"type":"unpin"}
//!   {"type":"react","emoji":E}         ref: the entry reacted to
//! A payload that is not one of these is shown as raw text.
//!
//! MERGE ORDER. `tail` reads every stream on the roster and orders all entries
//! by (height, author, cell, sequence), numerically. Height is the admission
//! height the receiver recorded; on one node each accepted record has its own
//! height, so height alone orders entries of different transactions, and the
//! rest only orders entries one transaction wrote to several streams. The key
//! is a function of what the Host signed into each record, never of when or
//! by whom it was read, so every reader that observes the same streams gets
//! the same order, before and after a restart. An entry can only be added at a
//! height above every existing one, so an entry's number in the merged feed
//! (`#N`, from 1) never changes once it is assigned; `pin N`, `react N` and
//! `say --re N` name entries by it.
//!
//! WHO MAY SET THE TOPIC AND PIN: the founder only. The kernel's author law
//! says who may write whose stream; it says nothing about rooms. Any member may
//! append a topic or pin entry to their own stream, and `tail` shows it, marked
//! ignored with the reason; the room's topic and pin are the last such entries,
//! in merge order, whose author is the founder (roster field 2). Reactions and
//! replies are open to every member.
//!
//! TEXT. The stream cell holds only a digest of each payload. The Host's tail
//! view (STREAM-TAIL/v2) returns the bytes from the accepted signed command of
//! the entry's transaction, only when they reproduce the committed digest
//! (`NativeObservationController.streamPayload_sound`), and the Host's own
//! renderer re-checks the digest over the bytes this reader holds
//! (`payloadState`). Anything else prints `[payload unavailable]`.

use crate::shell::{Session, Verb, EXIT_CLIENT, EXIT_OK, EXIT_REFUSED, EXIT_USAGE};
use crate::workspace::{bounded_json, member, member_path, private_file, random_nonce};
use serde_json::{json, Value};
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{OsStr, OsString};
use std::fs;
use std::io::Write;
use std::os::unix::fs::DirBuilderExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// The verbs this module adds to the shell (rows for `help`).
pub(crate) const VERBS: &[Verb] = &[
    Verb { name: "say", usage: "say [--to NAME] [--re N] [--in ROOM] TEXT", operation: "append {\"type\":\"say\",\"text\":TEXT} to my stream in the current room (propose + submit)" },
    Verb { name: "tail", usage: "tail [-n N] [--since HEIGHT] [--follow] [--json] [--held] [--in ROOM]", operation: "a signed tail of every member stream in the current room, merged by (height, author, cell, sequence)" },
    Verb { name: "topic", usage: "topic [TEXT]", operation: "show the room topic, or append {\"type\":\"topic\"} (the founder's counts)" },
    Verb { name: "pin", usage: "pin N | unpin", operation: "append {\"type\":\"pin\"} with ref = entry #N, or {\"type\":\"unpin\"} (the founder's count)" },
    Verb { name: "unpin", usage: "unpin", operation: "append {\"type\":\"unpin\"} in the current room (the founder's counts)" },
    Verb { name: "react", usage: "react N EMOJI", operation: "append {\"type\":\"react\",\"emoji\":EMOJI} with ref = entry #N" },
    Verb { name: "chat", usage: "chat new ROOM [--private] | chat invite ROOM SUBJECT [NAME] [--enc ENC-PUB|@FILE] | chat join ROOM INVITE-JSON|@FILE | chat enter ROOM | chat rooms | chat name SUBJECT NAME", operation: "the room template: a founder-written roster cell, one stream per member born by the founder; `help chat`" },
];

pub(crate) const HELP: &str = "\
chat: talk in a room. Each of you speaks into your own stream; the room is the merge.

  say hello everyone              append to your stream in the current room
  say --to bob are you there?     addressed to bob (everyone in the room still sees it)
  say --re 12 yes, agreed         a reply to entry #12
  tail                            the last 20 entries, oldest first
  tail -n 100 --since 340         entries above height 340
  tail --follow                   keep printing new entries (polls every 3 s; ctrl-c stops)
  tail --held                     what you last read, re-checked, without asking the Host
  topic                           show the topic;  topic release planning  sets it
  pin 12 / unpin                  pin entry #12 for the room
  react 12 +1                     a reaction to entry #12

  chat rooms                      the rooms this session knows; * marks the current one
  chat enter commons              make commons the current room
  chat name 1279008242 bob        your petname for a subject (names are yours alone)

A room's founder:
  chat new commons                create the room, its roster and your stream
  chat invite commons SUBJECT bob grant bob the room, birth bob's stream (you pay), add bob
                                  to the roster; prints the invitation to give bob
  chat new den --private          a private room (K-ROOM's keys cell; needs MINI_KEYCACHE_PASSPHRASE):
                                  every say is sealed under the room key; the Host stores ciphertext
  chat invite den SUBJECT bob --enc HEX   wrap the room key for bob too (bob's `whoami` prints HEX)
A member:
  chat join commons INVITATION    take the invitation (JSON, or @FILE in requests/)

Each line is #N (its number in the room, never renumbered), hHEIGHT (when the Host
admitted it) and the speaker. Only the founder's topic and pin count; anyone else's
are shown as ignored. You can only ever write your own stream: the Host refuses a
write to someone else's. Text you see was checked against the digest the Host
committed; text that does not match prints [payload unavailable].
";

/// How long `tail --follow` waits between polls.
pub(crate) const FOLLOW_INTERVAL_S: u64 = 3;
/// Entries per signed tail window.
const WINDOW: u64 = 256;

/// What `chat invite` grants under the room by default: read the room and its
/// streams, and append to one's own stream (the author law refuses any other).
const MEMBER_GRANT: &[&str] = &["observe", "append"];
/// The verbs `chat invite --verbs` may name under a room (`place` bears cells into it).
const ROOM_VERBS: &[&str] = &["observe", "place", "append"];
pub(crate) const LS_USAGE: &str = "room ls [ROOM] [--since HEIGHT] [--import] [--json]";
/// The kernel's topic and payload limits (`StreamCell.maxTopicBytes`, `maxPayloadBytes`).
const MAX_TOPIC: usize = 64;
const MAX_PAYLOAD: usize = 4096;

/// The room template's per-author law (`deploy/shell/templates/room/chat/law.author.json`):
/// every write (mutate 2, append 7) is signed by `@SUBJECT`; reads and grants pass.
const AUTHOR_LAW: &str = include_str!("../../../deploy/shell/templates/room/chat/law.author.json");

pub(crate) fn author_law(subject: &str) -> Value {
    let text = AUTHOR_LAW.replace("@SUBJECT", subject);
    serde_json::from_str(&text).expect("the template law is JSON")
}

// ---------------------------------------------------------------- lines

#[derive(Debug, PartialEq, Clone)]
pub(crate) struct Via {
    pub network: String,
    pub id: String,
    pub name: String,
}

#[derive(Debug, PartialEq, Clone)]
pub(crate) enum Text {
    Inline(String),
    /// HOME/requests/FILE (a bridge passes multi-line text this way).
    File(String),
}

#[derive(Debug, PartialEq)]
pub(crate) enum Line {
    Say { room: Option<String>, to: Option<String>, re: Option<u64>, text: Text, via: Option<Via> },
    Tail { room: Option<String>, count: usize, since: Option<u64>, follow: bool, json: bool, held: bool, entry: Option<(String, u64)>, discovery: Option<String> },
    Topic(Option<String>),
    Pin(u64),
    Unpin,
    React { number: u64, emoji: String },
    New { room: String, private: bool },
    Invite { room: String, subject: String, name: Option<String>, enc: Option<String>, verbs: Vec<String> },
    /// `room ls [--in ROOM] [--since H] [--import] [--json]`: the cells under
    /// the room the Host's signed `since` view names, with the roster's streams.
    Ls { room: Option<String>, since: u64, import: bool, json: bool },
    /// `summon`, `ask`, `dismiss` (PLACE §2.7): `crate::hermes`.
    Hermes(crate::hermes::Line),
    Join { room: String, invitation: String },
    Enter(String),
    Rooms,
    Name { subject: String, name: String },
}

pub(crate) fn ref_name(value: &str, label: &str) -> Result<(), String> {
    if value.is_empty()
        || value.len() > 40
        || !value.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
    {
        return Err(format!("{label} must be 1..40 ASCII letters, digits or hyphens"));
    }
    Ok(())
}

pub(crate) fn decimal(value: &str, label: &str) -> Result<(), String> {
    if value.is_empty() || value.len() > 40 || !value.bytes().all(|b| b.is_ascii_digit()) {
        return Err(format!("{label} must be a decimal number"));
    }
    Ok(())
}

fn number(value: &str, label: &str) -> Result<u64, String> {
    let value = value.strip_prefix('#').unwrap_or(value);
    value.parse::<u64>().ok().filter(|n| *n > 0).ok_or_else(|| format!("{label} must be an entry number (#N, from 1)"))
}

/// The first whitespace-separated word and the rest of the line, untouched.
pub(crate) fn split(text: &str) -> Option<(&str, &str)> {
    let text = text.trim_start();
    if text.is_empty() {
        return None;
    }
    let end = text.find(char::is_whitespace).unwrap_or(text.len());
    Some((&text[..end], &text[end..]))
}

/// The free text at the end of a line: trimmed; one pair of matching outer
/// quotes is removed, so `say 'hi'` and `say hi` say the same thing.
pub(crate) fn free_text(rest: &str) -> String {
    let t = rest.trim();
    for q in ['\'', '"'] {
        if t.len() >= 2 && t.starts_with(q) && t.ends_with(q) {
            return t[1..t.len() - 1].to_owned();
        }
    }
    t.to_owned()
}

fn emoji(value: &str) -> Result<String, String> {
    if value.is_empty() || value.len() > 32 || value.chars().any(|c| c.is_whitespace() || c.is_control()) {
        return Err("a reaction is 1..32 bytes with no spaces".into());
    }
    Ok(value.to_owned())
}

/// Map a raw shell line to a chat line. `None`: not a chat verb. Chat verbs
/// take the rest of the line as text, so apostrophes and `#` need no quoting.
pub(crate) fn plan(line: &str) -> Option<Result<Line, String>> {
    let (verb, rest) = split(line)?;
    if verb == "room" && split(rest).is_some_and(|(action, _)| action == "ls") {
        let (_, after) = split(rest)?;
        return Some(parse_ls(after));
    }
    if let Some(hermes) = crate::hermes::plan(verb, rest) {
        return Some(hermes.map(Line::Hermes));
    }
    let usage = |name: &str| VERBS.iter().find(|v| v.name == name).map(|v| v.usage).unwrap_or("");
    let parsed = match verb {
        "say" => parse_say(rest).map_err(|e| if e.is_empty() { usage("say").to_owned() } else { e }),
        "tail" => parse_tail(rest).map_err(|e| if e.is_empty() { usage("tail").to_owned() } else { e }),
        "topic" => {
            let text = free_text(rest);
            if text.is_empty() {
                Ok(Line::Topic(None))
            } else if text.len() > MAX_TOPIC {
                Err(format!("a topic is at most {MAX_TOPIC} bytes"))
            } else {
                Ok(Line::Topic(Some(text)))
            }
        }
        "pin" => match split(rest) {
            Some((n, more)) if more.trim().is_empty() => number(n, "pin").map(Line::Pin),
            _ => Err(usage("pin").to_owned()),
        },
        "unpin" if rest.trim().is_empty() => Ok(Line::Unpin),
        "unpin" => Err(usage("pin").to_owned()),
        "react" => match split(rest).and_then(|(n, more)| split(more).map(|(e, tail)| (n, e, tail))) {
            Some((n, e, tail)) if tail.trim().is_empty() => {
                number(n, "react").and_then(|number| emoji(e).map(|emoji| Line::React { number, emoji }))
            }
            _ => Err(usage("react").to_owned()),
        },
        "chat" => parse_chat(rest).map_err(|e| if e.is_empty() { usage("chat").to_owned() } else { e }),
        _ => return None,
    };
    Some(parsed)
}

fn parse_say(mut rest: &str) -> Result<Line, String> {
    let mut room = None;
    let mut to = None;
    let mut re = None;
    let mut file = None;
    let (mut network, mut id, mut name) = (None, None, None);
    while let Some((word, after)) = split(rest) {
        if !word.starts_with("--") {
            break;
        }
        let (value, next) = split(after).ok_or_else(|| format!("{word} needs a value"))?;
        match word {
            "--in" => {
                ref_name(value, "room name")?;
                room = Some(value.to_owned());
            }
            "--to" => to = Some(value.trim_start_matches('@').to_owned()),
            "--re" => re = Some(number(value, "--re")?),
            "--file" => file = Some(value.to_owned()),
            "--via" => network = Some(value.to_owned()),
            "--via-id" => id = Some(value.to_owned()),
            "--via-name" => name = Some(value.to_owned()),
            _ => return Err(format!("unknown say option {word}")),
        }
        rest = next;
    }
    let via = match (network, id, name) {
        (None, None, None) => None,
        (Some(network), Some(id), Some(name)) => {
            if network != "discord" {
                return Err("--via names a bridge network: discord".into());
            }
            decimal(&id, "--via-id")?;
            if name.is_empty() || name.len() > 64 {
                return Err("--via-name is 1..64 bytes".into());
            }
            Some(Via { network, id, name })
        }
        _ => return Err("--via, --via-id and --via-name go together".into()),
    };
    if let Some(to) = &to {
        if to.is_empty() || to.len() > 64 {
            return Err("--to names a member: a petname or a subject".into());
        }
    }
    let text = match file {
        Some(file) => {
            if !rest.trim().is_empty() {
                return Err("say --file FILE takes no other text".into());
            }
            if file.is_empty() || file.starts_with('.') || file.contains('/') || file.len() > 64 {
                return Err("--file is a plain file name in HOME/requests".into());
            }
            Text::File(file)
        }
        None => {
            let text = free_text(rest);
            if text.is_empty() {
                return Err(String::new());
            }
            Text::Inline(text)
        }
    };
    Ok(Line::Say { room, to, re, text, via })
}

fn parse_tail(rest: &str) -> Result<Line, String> {
    let words: Vec<&str> = rest.split_whitespace().collect();
    let (mut count, mut since, mut follow, mut json, mut held) = (20usize, None, false, false, false);
    let mut room = None;
    let mut entry = None;
    let mut discovery = None;
    let mut i = 0;
    while i < words.len() {
        match words[i] {
            "--discover" => {
                let file=words.get(i+1).ok_or("--discover takes a cursor file")?;
                if discovery.replace((*file).to_owned()).is_some() {return Err("duplicate --discover".into());}
                i+=1;
            }
            "--entry" => {
                let value = words.get(i + 1).ok_or("--entry takes CELL:SEQUENCE")?;
                let (cell, sequence) = value.split_once(':').ok_or("--entry takes CELL:SEQUENCE")?;
                decimal(cell, "entry cell")?;
                let sequence = sequence.parse::<u64>().ok().filter(|n| *n > 0).ok_or("entry sequence must be positive")?;
                if entry.replace((cell.to_owned(), sequence)).is_some() { return Err("duplicate --entry".into()); }
                i += 1;
            }
            "-n" => {
                count = words
                    .get(i + 1)
                    .and_then(|v| v.parse::<usize>().ok())
                    .filter(|n| (1..=100_000).contains(n))
                    .ok_or("-n takes 1..100000")?;
                i += 1;
            }
            "--since" => {
                since = Some(words.get(i + 1).and_then(|v| v.parse::<u64>().ok()).ok_or("--since takes a height")?);
                i += 1;
            }
            "--in" => {
                let value = words.get(i + 1).ok_or("--in names a room")?;
                ref_name(value, "room name")?;
                room = Some((*value).to_owned());
                i += 1;
            }
            "--follow" | "-f" => follow = true,
            "--held" => held = true,
            "--json" => json = true,
            _ => return Err(String::new()),
        }
        i += 1;
    }
    if follow && held {
        return Err("--held renders what this session already holds; it cannot --follow".into());
    }
    if entry.is_some() && (follow || held || since.is_some()) { return Err("--entry requires a fresh finite signed read without --since".into()); }
    if discovery.is_some() && (entry.is_some() || follow || held || since.is_some() || count>256) {return Err("--discover requires finite fresh pages of at most256 entries per stream".into());}
    Ok(Line::Tail { room, count, since, follow, json, held, entry, discovery })
}

fn parse_ls(rest: &str) -> Result<Line, String> {
    let words: Vec<&str> = rest.split_whitespace().collect();
    let (mut room, mut since, mut import, mut json) = (None, 0u64, false, false);
    let mut i = 0;
    while i < words.len() {
        match words[i] {
            "--in" => {
                let value = words.get(i + 1).ok_or("--in names a room")?;
                ref_name(value, "room name")?;
                room = Some((*value).to_owned());
                i += 1;
            }
            "--since" => {
                since = words.get(i + 1).and_then(|v| v.parse::<u64>().ok()).ok_or("--since takes a height")?;
                i += 1;
            }
            "--import" => import = true,
            "--json" => json = true,
            word if room.is_none() && !word.starts_with("--") => {
                ref_name(word, "room name")?;
                room = Some(word.to_owned());
            }
            _ => return Err(LS_USAGE.to_owned()),
        }
        i += 1;
    }
    Ok(Line::Ls { room, since, import, json })
}

fn parse_chat(rest: &str) -> Result<Line, String> {
    let mut words: Vec<&str> = rest.split_whitespace().collect();
    // `--enc ENC-PUB|@FILE` (chat invite into a private room): taken out first.
    let mut enc = None;
    if words.first() == Some(&"invite") {
        if let Some(i) = words.iter().position(|w| *w == "--enc") {
            let value = words.get(i + 1).ok_or("--enc names the invitee's encryption key (64 hex digits, or @FILE)")?;
            enc = Some((*value).to_owned());
            words.drain(i..i + 2);
        }
    }
    match words.as_slice() {
        ["new", room] => ref_name(room, "room name").map(|()| Line::New { room: (*room).to_owned(), private: false }),
        ["new", room, "--private"] => ref_name(room, "room name").map(|()| Line::New { room: (*room).to_owned(), private: true }),
        ["invite", room, subject, more @ ..] if more.len() <= 3 => {
            ref_name(room, "room name")?;
            decimal(subject, "subject")?;
            let (mut name, mut verbs) = (None, MEMBER_GRANT.iter().map(|v| (*v).to_owned()).collect::<Vec<_>>());
            let mut rest = more.iter();
            while let Some(word) = rest.next() {
                if *word == "--verbs" {
                    let list = rest.next().ok_or("--verbs takes V,V,…")?;
                    verbs = list.split(',').map(str::to_owned).collect();
                    if !verbs.iter().all(|v| ROOM_VERBS.contains(&v.as_str())) || !verbs.iter().any(|v| v == "observe") {
                        return Err(format!("--verbs: observe and any of {} under the room", ROOM_VERBS.join(", ")));
                    }
                } else if name.is_none() {
                    petname_ok(word)?;
                    name = Some((*word).to_owned());
                } else {
                    return Err(String::new());
                }
            }
            Ok(Line::Invite { room: (*room).to_owned(), subject: (*subject).to_owned(), name, enc, verbs })
        }
        ["join", room, ..] if words.len() >= 3 => {
            ref_name(room, "room name")?;
            let (_, after) = split(rest).and_then(|(_, r)| split(r)).ok_or("")?;
            Ok(Line::Join { room: (*room).to_owned(), invitation: after.trim().to_owned() })
        }
        ["enter", room] => ref_name(room, "room name").map(|()| Line::Enter((*room).to_owned())),
        ["rooms"] => Ok(Line::Rooms),
        ["name", subject, name] => {
            decimal(subject, "subject")?;
            petname_ok(name)?;
            Ok(Line::Name { subject: (*subject).to_owned(), name: (*name).to_owned() })
        }
        _ => Err(String::new()),
    }
}

fn petname_ok(name: &str) -> Result<(), String> {
    if name.is_empty()
        || name.len() > 24
        || name.bytes().all(|b| b.is_ascii_digit())
        || !name.bytes().all(|b| b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.'))
    {
        return Err("a petname is 1..24 letters, digits, '-', '_' or '.', not all digits".into());
    }
    Ok(())
}

// ---------------------------------------------------------------- endings

/// (exit code, stderr text). stdout is printed as the verb goes.
pub(crate) type Done = (i32, String);

pub(crate) fn usage(message: impl Into<String>) -> Done {
    (EXIT_USAGE, format!("usage: {}\n", message.into()))
}

pub(crate) fn error(message: impl std::fmt::Display) -> Done {
    (EXIT_CLIENT, format!("error: {message}\n"))
}

/// The ending of a client run in a child process: the child's own `refused:`
/// block verbatim (the Host's decoding, exit 3), or its error as `error:`.
fn child_ending(code: Option<i32>, stderr: &str) -> Done {
    let lines: Vec<&str> = stderr.lines().collect();
    if let Some(at) = lines.iter().position(|l| l.starts_with("refused: ")) {
        let mut text = lines[at..].join("\n");
        text.push('\n');
        return (EXIT_REFUSED, text);
    }
    let last = lines
        .iter()
        .rev()
        .find(|l| l.starts_with("mini: "))
        .map(|l| l.trim_start_matches("mini: ").to_owned())
        .unwrap_or_else(|| format!("the client exited {code:?}: {}", lines.last().unwrap_or(&"")));
    error(last)
}

// ---------------------------------------------------------------- files

pub(crate) fn chat_dir(session: &Session) -> PathBuf {
    session.home.join("chat")
}

pub(crate) fn private_dirs(path: &Path) -> Result<(), String> {
    fs::DirBuilder::new()
        .recursive(true)
        .mode(0o700)
        .create(path)
        .map_err(|e| format!("cannot create {}: {e}", path.display()))
}

/// Replace a small private JSON file (write a sibling, rename over).
pub(crate) fn put_json(path: &Path, value: &Value) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        private_dirs(parent)?;
    }
    let mut bytes=serde_json::to_vec_pretty(value).map_err(|e|e.to_string())?;
    bytes.push(b'\n');
    crate::workspace::replace_private_file(path,&bytes)
}

pub(crate) fn get_json(path: &Path) -> Option<Value> {
    serde_json::from_slice(&fs::read(path).ok()?).ok()
}

/// What this session knows about one room. `room` names the workspace
/// reference of the room cell; `grant` the reference whose observe capability
/// reads the room and its streams (`under R`); `stream` my own stream.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Room {
    pub(crate) name: String,
    pub(crate) grant: String,
    pub(crate) stream: Option<String>,
}

fn room_path(session: &Session, room: &str) -> PathBuf {
    chat_dir(session).join("rooms").join(format!("{room}.json"))
}

pub(crate) fn load_room(session: &Session, room: &str) -> Result<Room, String> {
    let value = get_json(&room_path(session, room)).ok_or_else(|| {
        format!("this session has no room {room} (chat new {room}, or chat join {room} INVITATION)")
    })?;
    let field = |k: &str| value.get(k).and_then(Value::as_str).map(str::to_owned);
    Ok(Room {
        name: room.to_owned(),
        grant: field("grant").ok_or("room record lacks grant")?,
        stream: field("stream"),
    })
}

fn save_room(session: &Session, room: &Room) -> Result<(), String> {
    put_json(
        &room_path(session, &room.name),
        &json!({"type":"mini-chat-room-v1","room":room.name,"grant":room.grant,"stream":room.stream}),
    )
}

pub(crate) fn current_room(session: &Session) -> Result<Room, String> {
    let name = fs::read_to_string(chat_dir(session).join("current"))
        .map(|s| s.trim().to_owned())
        .map_err(|_| "no current room: chat enter ROOM (chat rooms lists yours)".to_owned())?;
    load_room(session, &name)
}

fn set_current(session: &Session, room: &str) -> Result<(), String> {
    private_dirs(&chat_dir(session))?;
    let path = chat_dir(session).join("current");
    let tmp = chat_dir(session).join(format!("current.tmp-{}", std::process::id()));
    let _ = fs::remove_file(&tmp);
    private_file(&tmp, format!("{room}\n").as_bytes())?;
    fs::rename(&tmp, &path).map_err(|e| e.to_string())
}

fn petnames(session: &Session) -> BTreeMap<String, String> {
    get_json(&chat_dir(session).join("petnames.json"))
        .and_then(|v| v.as_object().cloned())
        .map(|o| o.into_iter().filter_map(|(k, v)| v.as_str().map(|s| (k, s.to_owned()))).collect())
        .unwrap_or_default()
}

fn set_petname(session: &Session, subject: &str, name: &str) -> Result<(), String> {
    let mut names = petnames(session);
    names.retain(|_, v| v != name);
    names.insert(subject.to_owned(), name.to_owned());
    put_json(&chat_dir(session).join("petnames.json"), &json!(names))
}

pub(crate) fn workspace_record(session: &Session) -> Result<Value, String> {
    bounded_json(&session.workspace.join("workspace.json"))
        .map_err(|_| "this session has no workspace yet (init first)".to_owned())
}

pub(crate) fn reference(session: &Session, name: &str) -> Result<Value, String> {
    crate::workspace::reference(&session.workspace, name)
}

// ---------------------------------------------------------------- client calls

/// One client operation in a child `mini` (the same binary), so its JSON does
/// not reach the friend's terminal. Ok: the child's stdout.
pub(crate) fn client(command: &str, flags: &[(&str, OsString)]) -> Result<String, Done> {
    let exe = std::env::current_exe().map_err(|e| error(format!("cannot locate the mini client: {e}")))?;
    let mut cmd = Command::new(exe);
    cmd.arg(command);
    for (name, value) in flags {
        cmd.arg(format!("--{name}")).arg(value);
    }
    if let Some(socket) = crate::SOCKET.get() {
        cmd.arg("--socket").arg(socket);
    }
    let out = cmd
        .stdin(Stdio::null())
        .output()
        .map_err(|e| error(format!("cannot run the mini client: {e}")))?;
    if out.status.success() {
        Ok(String::from_utf8_lossy(&out.stdout).into_owned())
    } else {
        Err(child_ending(out.status.code(), &String::from_utf8_lossy(&out.stderr)))
    }
}

pub(crate) fn os(value: impl AsRef<OsStr>) -> OsString {
    value.as_ref().to_owned()
}

fn fresh_id(prefix: &str) -> Result<String, Done> {
    let nonce = random_nonce().map_err(error)?;
    Ok(format!("{prefix}-{}", &nonce[nonce.len().saturating_sub(12)..]))
}

/// How many times a signed exchange is repeated when the Host answers
/// `stale-root`: its challenge named a world root that another admission has
/// since moved, so nothing was decided and the same request is signed again
/// over a fresh challenge.
const FRESH_CHALLENGES: u32 = 10;

fn stale_root(done: &Done) -> bool {
    done.0 == EXIT_REFUSED && done.1.starts_with("refused: stale-root")
}

/// A short pause before a fresh challenge, longer each time and different per
/// process, so racing writers do not keep meeting.
fn backoff(attempt: u32) {
    let jitter = random_nonce().ok().and_then(|n| n.get(n.len() - 3..).and_then(|t| t.parse::<u64>().ok())).unwrap_or(0);
    std::thread::sleep(std::time::Duration::from_millis(150 * u64::from(attempt) + jitter % 250));
}

/// Propose and submit one request; Ok: `{id, outcome, resigned}`. A
/// `stale-root` answer at either step is not a decision about the request:
/// the plan is made again from a fresh signed read (propose), or the same
/// intent is signed again over a fresh challenge (submit, a new attempt).
pub(crate) fn propose_submit(session: &Session, prefix: &str, request: &Value) -> Result<Value, Done> {
    propose_submit_in(session, prefix, request, None)
}

/// `propose_submit`, sealed under the private room `sealed` (PRIVATE-ROOMS:
/// `workspace propose --private ROOM` seals every append's text under the
/// room's current key, bound to the stream and the sequence it read).
fn propose_submit_in(session: &Session, prefix: &str, request: &Value, sealed: Option<&str>) -> Result<Value, Done> {
    private_dirs(&session.home.join("requests")).map_err(error)?;
    let ws = session.workspace.clone();
    let mut resigned = 0u32;
    let mut tries = 0u32;
    let id = loop {
        let id = fresh_id(prefix)?;
        let path = session.home.join("requests").join(format!("{id}.json"));
        let mut bytes = serde_json::to_vec(request).expect("JSON values serialise");
        bytes.push(b'\n');
        private_file(&path, &bytes).map_err(error)?;
        let mut flags = vec![("action", os("propose")), ("dir", os(&ws)), ("request", os(&path)), ("proposal-id", os(&id))];
        if let Some(room) = sealed {
            flags.push(("private", os(room)));
        }
        match client("workspace", &flags) {
            Ok(_) => break id,
            Err(done) if stale_root(&done) && tries + 1 < FRESH_CHALLENGES => {
                tries += 1;
                resigned += 1;
                backoff(tries);
            }
            Err(done) => return Err(done),
        }
    };
    let mut attempt = 0u32;
    let out = loop {
        let name = if attempt == 0 { id.clone() } else { format!("{id}-r{attempt}") };
        match client(
            "workspace",
            &[
                ("action", os("submit")),
                ("dir", os(&ws)),
                ("intent", os(ws.join("proposals").join(&id).join("intent.json"))),
                ("attempt", os(ws.join("attempts").join(&name))),
            ],
        ) {
            Ok(out) => break out,
            Err(done) if stale_root(&done) && attempt + 1 < FRESH_CHALLENGES => {
                attempt += 1;
                resigned += 1;
                backoff(attempt);
            }
            Err(done) => return Err(done),
        }
    };
    let mut outcome = Value::Null;
    for doc in serde_json::Deserializer::from_str(&out).into_iter::<Value>().flatten() {
        outcome = doc;
    }
    Ok(json!({"id":id,"outcome":outcome,"resigned":resigned}))
}

/// A signed read in this process (no JSON on the terminal). The attempt is
/// retained under HOME/chat/reads/ROOM/LABEL.NONCE; older reads of the same
/// label are removed once this one answered, so the newest is always kept.
pub(crate) fn signed_read(
    session: &Session,
    ws: &Value,
    room: &str,
    label: &str,
    reference: &Value,
    view: &str,
    extra: &[(&str, String)],
) -> Result<Value, Done> {
    let folder = chat_dir(session).join("reads").join(room);
    private_dirs(&folder).map_err(error)?;
    let nonce = random_nonce().map_err(error)?;
    let field = |k: &str| member(reference, k).map(str::to_owned).map_err(error);
    let (kind, target, capability) = (field("kind")?, field("target")?, field("observeCapability")?);
    let mut intent = json!({"subject":member(ws,"subject").map_err(error)?,"nonce":nonce,
        "purpose":{"type":"query","kind":kind,"target":target,"view":view},
        "grants":[{"kind":kind,"target":target,"capability":capability}]});
    for (k, v) in extra {
        intent["purpose"][*k] = json!(v);
    }
    let path = |k| member_path(ws, k).map_err(error);
    let (host, config, key) = (path("host")?, path("config")?, path("key")?);
    let mut attempt = 0u32;
    let (dir, result, refusal) = loop {
        let nonce = if attempt == 0 { nonce.clone() } else { random_nonce().map_err(error)? };
        intent["nonce"] = json!(nonce);
        let source = folder.join(format!("q-{nonce}.json"));
        private_file(&source, &serde_json::to_vec(&intent).expect("JSON")).map_err(error)?;
        let dir = folder.join(format!("{label}.{nonce}"));
        let _ = crate::take_host_decision();
        let result = crate::query_retained(&host, &config, &source, OsStr::new("intent"), &key, &format!("view-{view}"), &dir);
        let _ = fs::remove_file(&source);
        let refusal = match &result {
            Ok(_) => None,
            Err(_) => crate::take_host_decision().as_ref().and_then(crate::host_refusal_ending),
        };
        // A read whose challenge went stale decided nothing: read again.
        if refusal.as_deref().is_some_and(|l| l.starts_with("refused: stale-root")) && attempt + 1 < FRESH_CHALLENGES {
            let _ = fs::remove_dir_all(&dir);
            attempt += 1;
            backoff(attempt);
            continue;
        }
        break (dir, result, refusal);
    };
    match result {
        Ok(value) => {
            if let Ok(entries) = fs::read_dir(&folder) {
                for entry in entries.flatten() {
                    let n = entry.file_name().to_string_lossy().into_owned();
                    if n.starts_with(&format!("{label}.")) && entry.path() != dir {
                        let _ = fs::remove_dir_all(entry.path());
                    }
                }
            }
            Ok(value)
        }
        Err(e) => Err(match refusal {
            Some(line) => (EXIT_REFUSED, format!("{line}\n  read: {view} of {label} in {room}\n")),
            None => error(format!("{e} (read {view} of {label} in {room})")),
        }),
    }
}

// ---------------------------------------------------------------- the room

/// Numeric order of two decimal strings.
fn num_cmp(a: &str, b: &str) -> Ordering {
    let a = a.trim_start_matches('0');
    let b = b.trim_start_matches('0');
    a.len().cmp(&b.len()).then_with(|| a.cmp(b))
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Roster {
    pub founder: Option<String>,
    /// (subject, stream cell), in roster order.
    pub members: Vec<(String, String)>,
}

/// The roster from a room cell's resource view.
pub(crate) fn roster_of(view: &Value) -> Roster {
    let mut fields: BTreeMap<u64, String> = BTreeMap::new();
    for entry in view.pointer("/cell/entries").and_then(Value::as_array).into_iter().flatten() {
        let field = entry.pointer("/key/field").and_then(Value::as_str).and_then(|f| f.parse::<u64>().ok());
        let value = entry.get("value").and_then(Value::as_str);
        if let (Some(f), Some(v)) = (field, value) {
            fields.insert(f, v.to_owned());
        }
    }
    // The roster is the fields below the room cell's own fields (the
    // tariff, Hermes: `credit::ROOM_FIELDS_START`); a field at or above it is
    // never a member row.
    let members = fields
        .iter()
        .filter(|(f, _)| **f >= 3 && **f % 2 == 1 && **f + 1 < crate::credit::ROOM_FIELDS_START)
        .filter_map(|(f, subject)| fields.get(&(f + 1)).map(|stream| (subject.clone(), stream.clone())))
        .collect();
    Roster { founder: fields.get(&2).cloned(), members }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Payload {
    Verified(String),
    Absent,
    Mismatch,
    /// Verified bytes that are not UTF-8.
    Binary,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Entry {
    pub height: u64,
    pub author: String,
    pub cell: String,
    pub sequence: u64,
    pub topic: String,
    pub to: Option<String>,
    pub re: Option<(String, u64)>,
    pub payload: Payload,
    /// The stream's owner by the roster.
    pub owner: String,
}

fn unhex(hex: &str) -> Option<Vec<u8>> {
    if hex.len() % 2 != 0 {
        return None;
    }
    (0..hex.len()).step_by(2).map(|i| u8::from_str_radix(hex.get(i..i + 2)?, 16).ok()).collect()
}

/// The entries of one stream-tail view (`view-tail`, STREAM-TAIL/v2).
pub(crate) fn entries_of(view: &Value, cell: &str, owner: &str) -> Vec<Entry> {
    let s = |e: &Value, k: &str| e.get(k).and_then(Value::as_str).map(str::to_owned);
    view.get("entries")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(|e| {
            let payload = match (e.get("payloadState").and_then(Value::as_str), s(e, "payload")) {
                (Some("verified"), Some(hex)) => match unhex(&hex).map(String::from_utf8) {
                    Some(Ok(text)) => Payload::Verified(text),
                    Some(Err(_)) => Payload::Binary,
                    None => Payload::Mismatch,
                },
                (Some("mismatch"), _) => Payload::Mismatch,
                _ => Payload::Absent,
            };
            let topic = s(e, "topic")
                .and_then(|h| unhex(&h))
                .map(|b| String::from_utf8_lossy(&b).into_owned())
                .unwrap_or_default();
            let re = e.get("ref").filter(|r| !r.is_null()).and_then(|r| {
                Some((s(r, "cell")?, s(r, "sequence")?.parse::<u64>().ok()?))
            });
            Some(Entry {
                height: s(e, "height")?.parse().ok()?,
                author: s(e, "author")?,
                cell: cell.to_owned(),
                sequence: s(e, "sequence")?.parse().ok()?,
                topic,
                to: s(e, "to"),
                re,
                payload,
                owner: owner.to_owned(),
            })
        })
        .collect()
}

/// THE merge order: (height, author, cell, sequence), numerically.
pub(crate) fn merge_order(a: &Entry, b: &Entry) -> Ordering {
    a.height
        .cmp(&b.height)
        .then_with(|| num_cmp(&a.author, &b.author))
        .then_with(|| num_cmp(&a.cell, &b.cell))
        .then_with(|| a.sequence.cmp(&b.sequence))
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Kind {
    Say { text: String, via: Option<Via> },
    Topic(String),
    Pin,
    Unpin,
    React(String),
    Raw(String),
    Unavailable,
}

pub(crate) fn kind_of(entry: &Entry) -> Kind {
    let text = match &entry.payload {
        Payload::Verified(text) => text,
        _ => return Kind::Unavailable,
    };
    let Ok(Value::Object(o)) = serde_json::from_str::<Value>(text) else {
        return Kind::Raw(text.clone());
    };
    let s = |k: &str| o.get(k).and_then(Value::as_str).map(str::to_owned);
    match s("type").as_deref() {
        Some("say") => match s("text") {
            Some(t) => {
                let via = match (s("via"), o.get("author")) {
                    (Some(network), Some(a)) => Some(Via {
                        network,
                        id: a.get("id").and_then(Value::as_str).unwrap_or("").to_owned(),
                        name: a.get("name").and_then(Value::as_str).unwrap_or("").to_owned(),
                    }),
                    _ => None,
                };
                Kind::Say { text: t, via }
            }
            None => Kind::Raw(text.clone()),
        },
        Some("topic") => s("text").map(Kind::Topic).unwrap_or_else(|| Kind::Raw(text.clone())),
        Some("pin") => Kind::Pin,
        Some("unpin") => Kind::Unpin,
        Some("react") => s("emoji").map(Kind::React).unwrap_or_else(|| Kind::Raw(text.clone())),
        _ => Kind::Raw(text.clone()),
    }
}

/// The merged room: the feed in merge order (`feed[i]` is entry `#i+1`), and
/// what the founder's entries decide.
#[derive(Debug, Clone)]
pub(crate) struct Feed {
    pub feed: Vec<Entry>,
    pub founder: Option<String>,
    /// (text, entry number) of the founder's last topic.
    pub topic: Option<(String, usize)>,
    /// entry number of the pinned entry, and of the pin.
    pub pin: Option<(usize, usize)>,
    /// target number -> emoji -> reactors in first-reaction order.
    pub reactions: BTreeMap<usize, BTreeMap<String, Vec<String>>>,
}

pub(crate) fn merge(mut entries: Vec<Entry>, founder: Option<String>) -> Feed {
    entries.sort_by(merge_order);
    entries.dedup_by(|a, b| a.cell == b.cell && a.sequence == b.sequence);
    let index: BTreeMap<(String, u64), usize> =
        entries.iter().enumerate().map(|(i, e)| ((e.cell.clone(), e.sequence), i + 1)).collect();
    let mut feed = Feed { feed: Vec::new(), founder: founder.clone(), topic: None, pin: None, reactions: BTreeMap::new() };
    for (i, e) in entries.iter().enumerate() {
        let n = i + 1;
        let by_founder = founder.as_deref() == Some(e.author.as_str());
        let target = e.re.as_ref().and_then(|r| index.get(r)).copied().filter(|t| *t < n);
        match kind_of(e) {
            Kind::Topic(t) if by_founder => feed.topic = Some((t, n)),
            Kind::Pin if by_founder => feed.pin = target.map(|t| (t, n)),
            Kind::Unpin if by_founder => feed.pin = None,
            Kind::React(emoji) => {
                if let Some(t) = target {
                    let who = feed.reactions.entry(t).or_default().entry(emoji).or_default();
                    if !who.contains(&e.author) {
                        who.push(e.author.clone());
                    }
                }
            }
            _ => {}
        }
    }
    feed.feed = entries;
    feed
}

/// Read the roster and every member stream (paging), and merge. Streams that
/// cannot be read are reported in `missing` with the Host's refusal line.
/// Split the roster by the Host's `who` view of the room, read under this
/// session's room grant: (current members, former members).
fn current_members(session: &Session, room: &Room, roster: Roster) -> Result<(Roster, Vec<(String, String)>), Done> {
    let ws = workspace_record(session).map_err(error)?;
    let grant = reference(session, &room.grant).map_err(error)?;
    let who = signed_read(session, &ws, &room.name, "who", &grant, "who", &[])?;
    let current: BTreeSet<String> = who
        .get("members")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(|m| m.get("subject").and_then(Value::as_str).map(str::to_owned))
        .collect();
    let (members, former): (Vec<_>, Vec<_>) =
        roster.members.into_iter().partition(|(subject, _)| current.contains(subject));
    Ok((Roster { founder: roster.founder, members }, former))
}

fn cache_feed(session:&Session,room:&Room,feed:&Feed)->Result<(),Done> {
    put_json(&chat_dir(session).join("rooms").join(format!("{}.cache.json",room.name)),
        &json!({"topic":feed.topic.as_ref().map(|t|t.0.clone()),"feed":feed.feed.iter().map(|e|json!([e.cell,e.sequence.to_string()])).collect::<Vec<_>>(),"height":feed.feed.last().map(|e|e.height)})).map_err(error)
}
fn stream_window(session:&Session,room:&Room,held:&Held,subject:&str,cell:&str,start:u64,count:usize)->Result<Value,Done> {
    let synthetic=json!({"kind":"object","target":cell,"observeCapability":held.capability});
    let mut view=signed_read(session,&held.ws,&room.name,&format!("resident-{cell}-{start}-{count}"),&synthetic,"tail",
        &[("start",start.to_string()),("count",count.to_string())])?;
    let _=subject;
    open_sealed(&mut view,&held.keys,cell);
    Ok(view)
}
fn read_exact_entry(session:&Session,room:&Room,reference:&(String,u64))->Result<(Feed,Roster,Vec<String>),Done> {
    let mut held=Held::open(session,room)?;held.roster(session,room)?;
    let subject=held.roster.members.iter().find(|(_,cell)|cell==&reference.0).map(|(subject,_)|subject.clone())
        .ok_or_else(||error("stable reply stream absent from signed roster"))?;
    let view=stream_window(session,room,&held,&subject,&reference.0,reference.1,1)?;
    let feed=merge(entries_of(&view,&reference.0,&subject),held.roster.founder.clone());
    cache_feed(session,room,&feed)?;
    Ok((feed,held.roster,Vec::new()))
}
/// Source-only per-stream cursor pages. Retained refs are re-read separately,
/// so a held old request cannot pin discovery to that old stream prefix.
fn read_discovery(session:&Session,room:&Room,file:&str,count:usize)->Result<(Feed,Roster,Vec<String>,Value),Done> {
    let bytes=fs::read(file).map_err(error)?;
    if bytes.len()>262144 {return Err(error("discovery cursor file exceeds bound"));}
    let request:Value=serde_json::from_slice(&bytes).map_err(error)?;
    if request["type"]!="mini-resident-discovery-v1" {return Err(error("discovery type differs"));}
    let cursors=request["cursors"].as_object().ok_or_else(||error("discovery cursors absent"))?;
    let retained=request["retained"].as_array().ok_or_else(||error("discovery retained refs absent"))?;
    if cursors.len()>1024 || retained.len()>1024 {return Err(error("discovery stream/retained bound exceeded"));}
    for (cell,seq) in cursors {decimal(cell,"discovery stream").map_err(error)?;if seq.as_u64().is_none(){return Err(error("discovery cursor invalid"));}}
    let mut held=Held::open(session,room)?;held.roster(session,room)?;
    let (roster,_)=current_members(session,room,held.roster.clone())?;
    let mut entries=Vec::new();let mut progressed=serde_json::Map::new();let mut missing=Vec::new();
    for (subject,cell) in &roster.members {
        let cursor=cursors.get(cell).and_then(Value::as_u64).unwrap_or(0);
        let start=cursor.checked_add(1).ok_or_else(||error("discovery sequence exhausted"))?;
        match stream_window(session,room,&held,subject,cell,start,count) {
            Ok(view)=>{
                let rows=entries_of(&view,cell,subject);
                if view["entries"].as_array().into_iter().flatten().any(|e|e["payloadState"]!="verified") {
                    missing.push(format!("stream of {subject} ({cell}): payload unavailable; cursor retained"));
                    progressed.insert(cell.clone(),json!(cursor));
                } else {
                    progressed.insert(cell.clone(),json!(rows.iter().map(|e|e.sequence).max().unwrap_or(cursor)));
                    entries.extend(rows);
                }
            },
            Err((_,line))=>{missing.push(format!("stream of {subject} ({cell}): {line}"));progressed.insert(cell.clone(),json!(cursor));}
        }
        for reference in retained.iter().filter(|r|r[0]==*cell) {
            let seq=reference[1].as_u64().filter(|n|*n>0).ok_or_else(||error("retained sequence invalid"))?;
            match stream_window(session,room,&held,subject,cell,seq,1) {
                Ok(view)=>entries.extend(entries_of(&view,cell,subject)),
                Err((_,line))=>missing.push(format!("retained stream of {subject} ({cell}): {line}")),
            }
        }
    }
    let feed=merge(entries,roster.founder.clone());cache_feed(session,room,&feed)?;
    Ok((feed,roster,missing,Value::Object(progressed)))
}

fn read_room(session: &Session, room: &Room) -> Result<(Feed, Roster, Vec<String>), Done> {
    let mut held = Held::open(session, room)?;
    held.roster(session, room)?;
    for (subject, stream) in held.roster.members.clone() {
        held.stream(session, room, &subject, &stream, true)?;
    }
    let (feed, missing) = held.feed();
    let _ = put_json(
        &chat_dir(session).join("rooms").join(format!("{}.cache.json", room.name)),
        &json!({"topic":feed.topic.as_ref().map(|t| t.0.clone()),
            "feed":feed.feed.iter().map(|e| json!([e.cell, e.sequence.to_string()])).collect::<Vec<_>>(),
            "height":feed.feed.last().map(|e| e.height)}),
    );
    Ok((feed, held.roster, missing))
}

/// Whether this session's reference for `room` is a private room's (PRIVATE-ROOMS).
pub(crate) fn room_is_private(session: &Session, room: &str) -> bool {
    reference(session, room).is_ok_and(|r| r.get("private").is_some())
}

/// The keys a reader of a private room opens with: (room id, the synced ring,
/// or none without a cache passphrase). `None` for a public room.
type RoomKeys = Option<(String, Option<crate::workspace::private::Keyring>)>;

fn room_keys(session: &Session, room: &Room) -> Result<RoomKeys, Done> {
    if !room_is_private(session, &room.name) {
        return Ok(None);
    }
    let ws = workspace_record(session).map_err(error)?;
    let keys = crate::workspace::roomkey::reader_keys(&session.workspace, &ws, &room.name).map_err(error)?;
    Ok(Some(keys))
}

/// Open every sealed entry of one stream-tail view in place: the payload
/// becomes the opened text (the typed JSON the author sealed); an entry this
/// reader holds no key for becomes the sealed marker; a refusal is printed as
/// one; plaintext posted into a private room is shown marked `[unsealed]`.
fn open_sealed(view: &mut Value, keys: &RoomKeys, stream: &str) {
    let Some((room_id, ring)) = keys else { return };
    let Some(entries) = view.get_mut("entries").and_then(Value::as_array_mut) else { return };
    for e in entries {
        if e.get("payloadState").and_then(Value::as_str) != Some("verified") {
            continue;
        }
        let Some(bytes) = e.get("payload").and_then(Value::as_str).and_then(unhex) else { continue };
        let sequence = e.get("sequence").and_then(Value::as_str).unwrap_or("").to_owned();
        let note = crate::workspace::roomkey::open_in_room(ring.as_ref(), room_id, stream, &sequence, &bytes);
        let shown = match &note {
            Value::String(marker) => marker.clone(),
            v if v.get("text").and_then(Value::as_str).is_some() => v["text"].as_str().unwrap_or_default().to_owned(),
            v if v.get("unsealed").is_some() => {
                let plain = v["unsealed"].as_str().unwrap_or_default();
                match serde_json::from_str::<Value>(plain) {
                    Ok(mut typed) if typed.get("text").and_then(Value::as_str).is_some() => {
                        typed["text"] = json!(format!("[unsealed] {}", typed["text"].as_str().unwrap_or_default()));
                        typed.to_string()
                    }
                    _ => format!("[unsealed] {plain}"),
                }
            }
            v => format!("[refused: {}]", v.get("refused").map(Value::to_string).unwrap_or_default()),
        };
        e["payload"] = json!(crate::hex(shown.as_bytes()));
        e["sealed"] = json!(true);
    }
}

/// What a reader holds of a room between signed reads: the roster, and per
/// stream the entries read so far and the next sequence to ask for.
struct Held {
    keys: RoomKeys,
    ws: Value,
    grant: Value,
    capability: String,
    roster: Roster,
    streams: BTreeMap<String, (Vec<Entry>, u64)>,
    missing: BTreeMap<String, String>,
}

impl Held {
    fn open(session: &Session, room: &Room) -> Result<Held, Done> {
        let ws = workspace_record(session).map_err(error)?;
        let grant = reference(session, &room.grant).map_err(error)?;
        let capability = member(&grant, "observeCapability").map_err(error)?.to_owned();
        let keys = room_keys(session, room)?;
        Ok(Held { keys, ws, grant, capability, roster: Roster { founder: None, members: Vec::new() }, streams: BTreeMap::new(), missing: BTreeMap::new() })
    }

    fn roster(&mut self, session: &Session, room: &Room) -> Result<(), Done> {
        let view = signed_read(session, &self.ws, &room.name, "roster", &self.grant, "resource", &[])?;
        self.roster = roster_of(&view);
        Ok(())
    }

    /// Read one stream from where this reader stopped (or from 1 when `full`).
    /// Full reads keep their windows as `s{cell}-p{start}` (what `--held`
    /// renders again); incremental reads as `s{cell}-f`.
    fn stream(&mut self, session: &Session, room: &Room, subject: &str, stream: &str, full: bool) -> Result<(), Done> {
        let synthetic = json!({"kind":"object","target":stream,"observeCapability":self.capability});
        let (mut entries, mut start) = match (full, self.streams.remove(stream)) {
            (false, Some(held)) => held,
            _ => (Vec::new(), 1),
        };
        for _ in 0..64 {
            let label = if full { format!("s{stream}-p{start}") } else { format!("s{stream}-f") };
            match signed_read(session, &self.ws, &room.name, &label, &synthetic, "tail",
                &[("start", start.to_string()), ("count", WINDOW.to_string())]) {
                Ok(mut view) => {
                    open_sealed(&mut view, &self.keys, stream);
                    entries.extend(entries_of(&view, stream, subject));
                    let next = view.get("nextSeq").and_then(Value::as_str).and_then(|v| v.parse::<u64>().ok()).unwrap_or(start);
                    self.missing.remove(stream);
                    if start + WINDOW >= next {
                        start = next.max(start);
                        break;
                    }
                    start += WINDOW;
                }
                Err((_, line)) => {
                    self.missing.insert(stream.to_owned(), format!("stream of {subject} ({stream}): {}", line.lines().next().unwrap_or("")));
                    break;
                }
            }
        }
        self.streams.insert(stream.to_owned(), (entries, start));
        Ok(())
    }

    fn feed(&self) -> (Feed, Vec<String>) {
        let entries = self.streams.values().flat_map(|(e, _)| e.iter().cloned()).collect();
        (merge(entries, self.roster.founder.clone()), self.missing.values().cloned().collect())
    }
}

/// The room as this session last read it: the retained signed views under
/// HOME/chat/reads/ROOM, rendered again by the Host's own renderer
/// (`inspect`), which re-checks every payload against its digest. Nothing is
/// asked of the Host.
fn read_held(session: &Session, room: &Room) -> Result<(Feed, Roster, Vec<String>), Done> {
    let ws = workspace_record(session).map_err(error)?;
    let path = |k| member_path(&ws, k).map_err(error);
    let (host, config) = (path("host")?, path("config")?);
    let folder = chat_dir(session).join("reads").join(&room.name);
    let latest = |label: &str| -> Option<PathBuf> {
        fs::read_dir(&folder)
            .ok()?
            .flatten()
            .filter(|e| e.file_name().to_string_lossy().starts_with(&format!("{label}.")))
            .map(|e| e.path().join("view.bin"))
            .filter(|p| p.is_file())
            .max_by_key(|p| fs::metadata(p).and_then(|m| m.modified()).ok())
    };
    let render = |kind: &str, bin: &Path| -> Result<Value, Done> {
        let nonce = random_nonce().map_err(error)?;
        let out = folder.join(format!("held-{nonce}.json"));
        let value = crate::inspect(&host, &config, kind, bin, &out).map_err(|e| error(format!("{e} ({})", bin.display())));
        let _ = fs::remove_file(&out);
        value
    };
    let roster_bin = latest("roster").ok_or_else(|| error(format!("this session holds no read of {}; tail it first", room.name)))?;
    let roster = roster_of(&render("view-resource", &roster_bin)?);
    let keys = room_keys(session, room)?;
    let mut entries = Vec::new();
    let mut missing = Vec::new();
    for (subject, stream) in &roster.members {
        let mut start = 1u64;
        let mut any = false;
        while let Some(bin) = latest(&format!("s{stream}-p{start}")) {
            any = true;
            let mut view = render("view-tail", &bin)?;
            open_sealed(&mut view, &keys, stream);
            entries.extend(entries_of(&view, stream, subject));
            start += WINDOW;
        }
        if !any {
            missing.push(format!("stream of {subject} ({stream}): no held read"));
        }
    }
    Ok((merge(entries, roster.founder.clone()), roster, missing))
}

// ---------------------------------------------------------------- rendering

pub(crate) struct Names {
    me: String,
    pet: BTreeMap<String, String>,
}

impl Names {
    fn of(&self, subject: &str) -> String {
        if let Some(n) = self.pet.get(subject) {
            return n.clone();
        }
        if subject == self.me {
            return "me".into();
        }
        format!("s…{}", &subject[subject.len().saturating_sub(6)..])
    }
}

fn clip(text: &str, max: usize) -> String {
    let flat: String = text.chars().map(|c| if c.is_control() { ' ' } else { c }).collect();
    if flat.chars().count() <= max {
        flat
    } else {
        let mut s: String = flat.chars().take(max).collect();
        s.push('…');
        s
    }
}

/// One feed line (no trailing newline), and the reactions under it.
pub(crate) fn render_entry(feed: &Feed, n: usize, names: &Names) -> String {
    let e = &feed.feed[n - 1];
    let who = names.of(&e.author);
    let mut head = format!("#{n} h{} {who}", e.height);
    if e.author != e.owner {
        head.push_str(&format!(" [in the stream of {}]", names.of(&e.owner)));
    }
    if let Some(to) = &e.to {
        head.push_str(&format!(" →{}", names.of(to)));
    }
    let reference = |e: &Entry| -> String {
        match &e.re {
            None => String::new(),
            Some(r) => feed
                .feed
                .iter()
                .position(|x| x.cell == r.0 && x.sequence == r.1)
                .map(|i| format!("#{}", i + 1))
                .unwrap_or_else(|| format!("(cell {} entry {}, not in this room)", r.0, r.1)),
        }
    };
    let founder = feed.founder.as_deref() == Some(e.author.as_str());
    let founder_name = feed.founder.as_deref().map(|f| names.of(f)).unwrap_or_else(|| "the founder".into());
    let body = match kind_of(e) {
        Kind::Say { text, via: None } => match &e.re {
            Some(_) => format!(" ↪{}: {}", reference(e), clip(&text, 400)),
            None => format!(": {}", clip(&text, 400)),
        },
        Kind::Say { text, via: Some(via) } => {
            let reply = if e.re.is_some() { format!(" ↪{}", reference(e)) } else { String::new() };
            format!(" via {} {}#{}{reply}: {}", via.network, clip(&via.name, 32), via.id, clip(&text, 400))
        }
        Kind::Topic(t) if founder => format!(" set the topic: {}", clip(&t, 64)),
        Kind::Topic(t) => format!(" set the topic to {:?} (ignored: only {founder_name}, the founder, sets the topic in this room)", clip(&t, 64)),
        Kind::Pin if founder => format!(" pinned {}", reference(e)),
        Kind::Pin => format!(" pinned {} (ignored: only {founder_name}, the founder, pins in this room)", reference(e)),
        Kind::Unpin if founder => " unpinned".into(),
        Kind::Unpin => format!(" unpinned (ignored: only {founder_name}, the founder, pins in this room)"),
        Kind::React(emoji) => format!(" reacted {} to {}", clip(&emoji, 32), reference(e)),
        Kind::Raw(text) => format!(": {}", clip(&text, 400)),
        Kind::Unavailable => match e.payload {
            Payload::Binary => ": [payload is not text]".into(),
            _ => ": [payload unavailable]".into(),
        },
    };
    let mut out = head + &body;
    if let Some(r) = feed.reactions.get(&n) {
        for (emoji, who) in r {
            out.push_str(&format!("\n      {} {}", clip(emoji, 32), who.iter().map(|w| names.of(w)).collect::<Vec<_>>().join(" ")));
        }
    }
    out
}

fn entry_json(feed: &Feed, n: usize, names: &Names) -> Value {
    let e = &feed.feed[n - 1];
    let (kind, text, via) = match kind_of(e) {
        Kind::Say { text, via } => ("say", Some(text), via),
        Kind::Topic(t) => ("topic", Some(t), None),
        Kind::Pin => ("pin", None, None),
        Kind::Unpin => ("unpin", None, None),
        Kind::React(x) => ("react", Some(x), None),
        Kind::Raw(t) => ("raw", Some(t), None),
        Kind::Unavailable => ("unavailable", None, None),
    };
    let re = e.re.as_ref().and_then(|r| feed.feed.iter().position(|x| x.cell == r.0 && x.sequence == r.1)).map(|i| i + 1);
    json!({"n":n,"height":e.height,"author":e.author,"name":names.of(&e.author),"cell":e.cell,
        "sequence":e.sequence,"topic":e.topic,"to":e.to,"re":re,"kind":kind,"text":text,
        "via":via.map(|v| json!({"network":v.network,"id":v.id,"name":v.name}))})
}

fn header(room: &Room, feed: &Feed, roster: &Roster, names: &Names) -> String {
    let mut h = format!("# {}", room.name);
    match &feed.topic {
        Some((t, n)) => h.push_str(&format!(" · topic: {} (#{n})", clip(t, 64))),
        None => h.push_str(" · no topic"),
    }
    if let Some((target, _)) = feed.pin {
        let e = &feed.feed[target - 1];
        let text = match kind_of(e) {
            Kind::Say { text, .. } | Kind::Raw(text) => clip(&text, 60),
            _ => String::new(),
        };
        h.push_str(&format!(" · pinned #{target} {}: {text}", names.of(&e.author)));
    }
    h.push_str(&format!(
        " · {} members: {}",
        roster.members.len(),
        roster.members.iter().map(|(s, _)| names.of(s)).collect::<Vec<_>>().join(", ")
    ));
    h
}

// ---------------------------------------------------------------- verbs

pub(crate) fn run(session: &Session, line: Line) -> Done {
    match run_inner(session, line) {
        Ok(()) => (EXIT_OK, String::new()),
        Err(done) => done,
    }
}

fn names(session: &Session) -> Names {
    let me = workspace_record(session)
        .ok()
        .and_then(|w| w.get("subject").and_then(Value::as_str).map(str::to_owned))
        .unwrap_or_default();
    Names { me, pet: petnames(session) }
}

fn resolve_member(session: &Session, who: &str) -> Result<String, Done> {
    if who.bytes().all(|b| b.is_ascii_digit()) {
        return Ok(who.to_owned());
    }
    petnames(session)
        .into_iter()
        .find(|(_, n)| n == who)
        .map(|(s, _)| s)
        .ok_or_else(|| usage(format!("no petname {who} (chat name SUBJECT {who})")))
}

/// The (cell, sequence) of feed entry `n`: from this reader's last tail when
/// it has one that long, else from a fresh read.
fn entry_ref(session: &Session, room: &Room, n: u64) -> Result<(String, u64), Done> {
    let cache = get_json(&chat_dir(session).join("rooms").join(format!("{}.cache.json", room.name)));
    let from = |v: &Value| -> Option<(String, u64)> {
        let pair = v.get("feed")?.as_array()?.get((n - 1) as usize)?;
        Some((pair.get(0)?.as_str()?.to_owned(), pair.get(1)?.as_str()?.parse().ok()?))
    };
    if let Some(found) = cache.as_ref().and_then(from) {
        return Ok(found);
    }
    let (feed, _, _) = read_room(session, room)?;
    feed.feed
        .get((n - 1) as usize)
        .map(|e| (e.cell.clone(), e.sequence))
        .ok_or_else(|| usage(format!("there is no entry #{n} in {} (it has {})", room.name, feed.feed.len())))
}

fn cached_topic(session: &Session, room: &Room) -> String {
    get_json(&chat_dir(session).join("rooms").join(format!("{}.cache.json", room.name)))
        .and_then(|v| v.get("topic").and_then(Value::as_str).map(str::to_owned))
        .unwrap_or_default()
}

/// Cut a topic to the kernel's 64 bytes on a character boundary.
fn topic_field(topic: &str) -> String {
    let mut end = topic.len().min(MAX_TOPIC);
    while !topic.is_char_boundary(end) {
        end -= 1;
    }
    topic[..end].to_owned()
}

/// One append to my stream in `room`. On `staleTarget` (my own earlier append
/// moved my stream after the plan read it) plan once more from a fresh read.
fn append(session: &Session, room: &Room, payload: Value, to: Option<String>, re: Option<(String, u64)>, topic: String) -> Result<Value, Done> {
    let stream = room
        .stream
        .clone()
        .ok_or_else(|| error(format!("you have no stream in {} (the founder births it: chat invite)", room.name)))?;
    let text = serde_json::to_string(&payload).expect("JSON");
    if text.len() > MAX_PAYLOAD {
        return Err(usage(format!("the entry is {} bytes; the limit is {MAX_PAYLOAD}", text.len())));
    }
    // A private room's entries are sealed; the kernel topic is plaintext the
    // operator reads, so a sealed append carries none (a topic entry's text is
    // inside the sealed payload already).
    let sealed = room_is_private(session, &room.name).then(|| room.name.clone());
    let topic = if sealed.is_some() { String::new() } else { topic };
    let mut append = json!({"type":"append","topic":topic_field(&topic),"text":text});
    if let Some(to) = to {
        append["to"] = json!(to);
    }
    if let Some((cell, sequence)) = re {
        append["ref"] = json!({"cell":cell,"sequence":sequence.to_string()});
    }
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
        "targets":[{"name":stream,"payload":append}]});
    let mut replanned = 0u64;
    loop {
        match propose_submit_in(session, "say", &request, sealed.as_deref()) {
            Err((EXIT_REFUSED, text)) if text.contains("staleTarget") && replanned < 3 => {
                replanned += 1;
                backoff(replanned as u32);
            }
            Ok(mut done) => {
                done["replanned"] = json!(replanned);
                return Ok(done);
            }
            Err(done) => return Err(done),
        }
    }
}

fn said(room: &Room, what: &str, result: &Value) {
    let tx = result.pointer("/outcome/transactionId").and_then(Value::as_str).unwrap_or("");
    let again = match (result["replanned"].as_u64().unwrap_or(0), result["resigned"].as_u64().unwrap_or(0)) {
        (0, 0) => String::new(),
        (p, r) => format!("; other writes landed first: re-planned {p}, re-signed {r}"),
    };
    println!("{what} in {} (transaction …{}{again})", room.name, &tx[tx.len().saturating_sub(10)..]);
}

fn run_inner(session: &Session, line: Line) -> Result<(), Done> {
    match line {
        Line::Say { room, to, re, text, via } => {
            let room = match room {
                Some(name) => load_room(session, &name),
                None => current_room(session),
            }
            .map_err(error)?;
            let text = match text {
                Text::Inline(t) => t,
                Text::File(f) => {
                    let p = session.home.join("requests").join(&f);
                    let t = fs::read_to_string(&p).map_err(|e| error(format!("cannot read {}: {e}", p.display())))?;
                    let t = t.trim_end_matches('\n').to_owned();
                    if t.is_empty() {
                        return Err(usage("the text file is empty"));
                    }
                    t
                }
            };
            let to = to.map(|t| resolve_member(session, &t)).transpose()?;
            let re = re.map(|n| entry_ref(session, &room, n)).transpose()?;
            let mut payload = json!({"type":"say","text":text});
            if let Some(v) = &via {
                payload["via"] = json!(v.network);
                payload["author"] = json!({"id":v.id,"name":v.name});
            }
            let topic = cached_topic(session, &room);
            let result = append(session, &room, payload, to, re, topic)?;
            said(&room, "said", &result);
            Ok(())
        }
        Line::Topic(None) => {
            let room = current_room(session).map_err(error)?;
            let (feed, _, _) = read_room(session, &room)?;
            let names = names(session);
            match &feed.topic {
                Some((t, n)) => println!("{} (#{n}, set by {})", t, names.of(&feed.feed[n - 1].author)),
                None => println!("{} has no topic", room.name),
            }
            Ok(())
        }
        Line::Topic(Some(text)) => {
            let room = current_room(session).map_err(error)?;
            let result = append(session, &room, json!({"type":"topic","text":text}), None, None, text.clone())?;
            said(&room, "topic appended", &result);
            founder_note(session, &room);
            Ok(())
        }
        Line::Pin(n) => {
            let room = current_room(session).map_err(error)?;
            let re = entry_ref(session, &room, n)?;
            let result = append(session, &room, json!({"type":"pin"}), None, Some(re), cached_topic(session, &room))?;
            said(&room, &format!("pin of #{n} appended"), &result);
            founder_note(session, &room);
            Ok(())
        }
        Line::Unpin => {
            let room = current_room(session).map_err(error)?;
            let result = append(session, &room, json!({"type":"unpin"}), None, None, cached_topic(session, &room))?;
            said(&room, "unpin appended", &result);
            founder_note(session, &room);
            Ok(())
        }
        Line::React { number, emoji } => {
            let room = current_room(session).map_err(error)?;
            let re = entry_ref(session, &room, number)?;
            let result = append(session, &room, json!({"type":"react","emoji":emoji}), None, Some(re), cached_topic(session, &room))?;
            said(&room, &format!("reacted to #{number}"), &result);
            Ok(())
        }
        Line::Tail { room, count, since, follow, json: as_json, held, entry, discovery } => {
            let room = match room {
                Some(name) => load_room(session, &name),
                None => current_room(session),
            }
            .map_err(error)?;
            tail(session, &room, count, since, follow, as_json, held, entry.as_ref(), discovery.as_deref())
        }
        Line::New { room, private } => chat_new(session, &room, private),
        Line::Invite { room, subject, name, enc, verbs } => chat_invite(session, &room, &subject, name.as_deref(), enc.as_deref(), &verbs),
        Line::Ls { room, since, import, json: as_json } => {
            let room = match room {
                // `room ls` is listed under `room`: a room made by `room new` (or
                // imported) has no chat record, and is read through its own
                // reference, whose capability observes the room.
                Some(name) => load_room(session, &name).or_else(|missing| match reference(session, &name) {
                    Ok(_) => Ok(Room { name: name.clone(), grant: name.clone(), stream: None }),
                    Err(_) => Err(format!(
                        "no room {name}: neither a chat room of this session nor a reference of its workspace ({missing})"
                    )),
                }),
                None => current_room(session),
            }
            .map_err(error)?;
            room_ls(session, &room, since, import, as_json)
        }
        Line::Hermes(line) => crate::hermes::run(session, line),
        Line::Join { room, invitation } => chat_join(session, &room, &invitation),
        Line::Enter(name) => {
            load_room(session, &name).map_err(error)?;
            set_current(session, &name).map_err(error)?;
            println!("current room: {name}");
            Ok(())
        }
        Line::Rooms => {
            let current = fs::read_to_string(chat_dir(session).join("current")).unwrap_or_default();
            let mut rooms: Vec<String> = fs::read_dir(chat_dir(session).join("rooms"))
                .map(|d| {
                    d.flatten()
                        .filter_map(|e| e.file_name().into_string().ok())
                        .filter(|n| n.ends_with(".json") && !n.ends_with(".cache.json"))
                        .map(|n| n.trim_end_matches(".json").to_owned())
                        .collect()
                })
                .unwrap_or_default();
            rooms.sort();
            for r in rooms {
                println!("{} {r}", if current.trim() == r { "*" } else { " " });
            }
            Ok(())
        }
        Line::Name { subject, name } => {
            set_petname(session, &subject, &name).map_err(error)?;
            println!("{subject} is {name} (to you)");
            Ok(())
        }
    }
}

/// Say, on stderr, when this session's topic/pin will be shown as ignored.
fn founder_note(session: &Session, room: &Room) {
    let me = names(session).me;
    let founder = get_json(&chat_dir(session).join("rooms").join(format!("{}.json", room.name)))
        .and_then(|v| v.get("founder").and_then(Value::as_str).map(str::to_owned));
    if founder.as_deref().is_some_and(|f| f != me) {
        eprintln!("note: only the founder's topic and pin count in {}; yours is shown as ignored", room.name);
    }
}

fn shown_entries(feed:&Feed,since:Option<u64>,entry:Option<&(String,u64)>)->Vec<usize> {
    (1..=feed.feed.len())
        .filter(|n|since.is_none_or(|h|feed.feed[n-1].height>h))
        .filter(|n|entry.is_none_or(|(cell,seq)|feed.feed[n-1].cell==*cell && feed.feed[n-1].sequence==*seq))
        .collect()
}
fn tail(session: &Session, room: &Room, count: usize, since: Option<u64>, follow: bool, as_json: bool, held: bool, entry: Option<&(String, u64)>, discovery: Option<&str>) -> Result<(), Done> {
    let names = names(session);
    let (feed, roster, missing, cursors) = if let Some(file)=discovery {
        read_discovery(session,room,file,count)?
    } else if let Some(reference)=entry {
        let (feed,roster,missing)=read_exact_entry(session,room,reference)?;
        (feed,roster,missing,Value::Null)
    } else {
        let (feed,roster,missing)=if held {read_held(session,room)?} else {read_room(session,room)?};
        (feed,roster,missing,Value::Null)
    };
    // The roster keeps a row for everyone ever invited; who is a member NOW is
    // the Host's `who` view (the subjects whose capability covers the room), so a
    // kicked or departed member is not counted (AUDIT-ROOMS, client defect 7).
    let (roster, former) = if held { (roster, Vec::new()) } else { current_members(session, room, roster)? };
    let mut out = std::io::stdout();
    let shown = shown_entries(&feed, since, entry);
    let start = if discovery.is_some() {0} else {shown.len().saturating_sub(count)};
    if as_json {
        let state = json!({"type":"mini-chat-room-v1","room":room.name,"founder":roster.founder,
            "members":roster.members.iter().map(|(s, c)| json!({"subject":s,"stream":c,"name":names.of(s)})).collect::<Vec<_>>(),
            "topic":feed.topic.as_ref().map(|t| t.0.clone()),"pin":feed.pin.map(|p| p.0),
            "entries":feed.feed.len(),"selectedEntries":shown.len(),"discoveryCursors":cursors,"unreadable":missing,
            "former":former.iter().map(|(s, c)| json!({"subject":s,"stream":c,"name":names.of(s)})).collect::<Vec<_>>()});
        let _ = writeln!(out, "{state}");
        for n in &shown[start..] {
            let _ = writeln!(out, "{}", entry_json(&feed, *n, &names));
        }
    } else {
        let mut line = header(room, &feed, &roster, &names);
        if !former.is_empty() {
            line.push_str(&format!(
                " · no longer members: {}",
                former.iter().map(|(s, _)| names.of(s)).collect::<Vec<_>>().join(", ")
            ));
        }
        let _ = writeln!(out, "{line}");
        for m in &missing {
            let _ = writeln!(out, "[unreadable] {m}");
        }
        for n in &shown[start..] {
            let _ = writeln!(out, "{}", render_entry(&feed, *n, &names));
        }
    }
    let _ = out.flush();
    if !follow {
        return Ok(());
    }
    // Follow: one signed `since` read of the room per poll (K-INDEX: the
    // transactions above HEIGHT that wrote cells under the room this grant
    // sees, and which cells). Only the streams it names are read again, from
    // where this reader stopped; the roster when the room cell itself moved.
    let mut held = Held::open(session, room)?;
    held.roster = roster.clone();
    let room_cell = member(&held.grant, "target").map_err(error)?.to_owned();
    for (_, stream) in &roster.members {
        held.streams.entry(stream.clone()).or_insert_with(|| (Vec::new(), 1));
    }
    for e in &feed.feed {
        let slot = held.streams.entry(e.cell.clone()).or_insert_with(|| (Vec::new(), 1));
        slot.0.push(e.clone());
        slot.1 = slot.1.max(e.sequence + 1);
    }
    let mut height = feed.feed.last().map(|e| e.height).unwrap_or(0).max(since.unwrap_or(0));
    let mut printed = feed.feed.len();
    loop {
        std::thread::sleep(std::time::Duration::from_secs(FOLLOW_INTERVAL_S));
        let since_view = signed_read(session, &held.ws.clone(), &room.name, "since", &held.grant.clone(), "since", &[("height", height.to_string())])?;
        let fresh: Vec<&Value> = since_view.get("entries").and_then(Value::as_array).map(|a| a.iter().collect()).unwrap_or_default();
        if fresh.is_empty() {
            continue;
        }
        let cells: std::collections::BTreeSet<String> = fresh
            .iter()
            .flat_map(|e| e.get("cells").and_then(Value::as_array).cloned().unwrap_or_default())
            .filter_map(|c| c.as_str().map(str::to_owned))
            .collect();
        if cells.contains(&room_cell) {
            held.roster(session, room)?;
        }
        for (subject, stream) in held.roster.members.clone() {
            if cells.contains(&stream) || !held.streams.contains_key(&stream) {
                held.stream(session, room, &subject, &stream, false)?;
            }
        }
        let (feed, _) = held.feed();
        for n in printed + 1..=feed.feed.len() {
            if as_json {
                let _ = writeln!(out, "{}", entry_json(&feed, n, &names));
            } else {
                let _ = writeln!(out, "{}", render_entry(&feed, n, &names));
            }
        }
        let _ = out.flush();
        printed = printed.max(feed.feed.len());
        height = fresh
            .iter()
            .filter_map(|e| e.get("height").and_then(Value::as_str).and_then(|h| h.parse::<u64>().ok()))
            .max()
            .unwrap_or(height)
            .max(height);
    }
}

// ---------------------------------------------------------------- the template

pub(crate) fn write_request(session: &Session, name: &str, value: &Value) -> Result<PathBuf, Done> {
    let dir = session.home.join("requests");
    private_dirs(&dir).map_err(error)?;
    let path = dir.join(format!("{name}.json"));
    let mut bytes = serde_json::to_vec(value).expect("JSON");
    bytes.push(b'\n');
    let _ = fs::remove_file(&path);
    private_file(&path, &bytes).map_err(error)?;
    Ok(path)
}

pub(crate) fn create_cell(session: &Session, name: &str, storage: &str, law: &Value, room: Option<&str>, owner: Option<&str>) -> Result<Value, Done> {
    create_cell_with_fields(session, name, storage, law, room, owner, None)
}

/// A declared cell names its exact field set at birth; content and stream
/// callers continue to use `create_cell` without an object-field declaration.
pub(crate) fn create_cell_with_fields(session: &Session, name: &str, storage: &str, law: &Value, room: Option<&str>, owner: Option<&str>, fields: Option<&str>) -> Result<Value, Done> {
    create_cell_as(session, name, storage, law, room, owner, None, fields)
}

/// `create_cell` with `--room-template T` (`private`: the room key, its keys
/// cell born in the room, the founder's own wrap).
fn create_cell_as(session: &Session, name: &str, storage: &str, law: &Value, room: Option<&str>, owner: Option<&str>, template: Option<&str>, fields: Option<&str>) -> Result<Value, Done> {
    let predicate = write_request(session, &format!("chat-law-{}", name.replace('/', ".")), law)?;
    let mut flags = vec![
        ("action", os("create")),
        ("dir", os(&session.workspace)),
        ("name", os(name)),
        ("storage", os(storage)),
        ("predicate", os(&predicate)),
    ];
    if let Some(room) = room {
        flags.push(("in", os(room)));
    }
    if let Some(owner) = owner {
        flags.push(("owner", os(owner)));
    }
    if let Some(template) = template {
        flags.push(("room-template", os(template)));
    }
    if let Some(fields) = fields {
        flags.push(("fields", os(fields)));
    }
    client("workspace", &flags)?;
    reference(session, name).map_err(error)
}

/// Grant `recipient` the room (`observe` + `append` under ROOM), publish it,
/// and return the recipient reference.
fn room_grant(session: &Session, room: &str, recipient: &str, verbs: &[String]) -> Result<Value, Done> {
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"delegate","name":room,
        "recipient":recipient,"verbs":verbs,"maxCost":"50000","room":true});
    let done = propose_submit(session, "grant", &request)?;
    let id = done["id"].as_str().unwrap_or_default().to_owned();
    let ws = &session.workspace;
    client(
        "workspace",
        &[("action", os("publish-delegation")), ("dir", os(ws)), ("proposal-id", os(&id)), ("attempt", os(ws.join("attempts").join(&id)))],
    )?;
    get_json(&ws.join("proposals").join(&id).join("recipient-reference.json"))
        .ok_or_else(|| error("the published delegation left no recipient-reference.json"))
}

pub(crate) fn import_from(session: &Session, name: &str, reference_json: &Value) -> Result<(), Done> {
    let path = session.home.join("inbox").join(format!("{name}.json"));
    private_dirs(&session.home.join("inbox")).map_err(error)?;
    let _ = fs::remove_file(&path);
    private_file(&path, &serde_json::to_vec(reference_json).expect("JSON")).map_err(error)?;
    client("workspace", &[("action", os("import")), ("dir", os(&session.workspace)), ("name", os(name)), ("from-ref", os(&path))])?;
    Ok(())
}

pub(crate) fn import_stream(session: &Session, name: &str, target: &str, capability: &str) -> Result<(), Done> {
    client(
        "workspace",
        &[
            ("action", os("import")),
            ("dir", os(&session.workspace)),
            ("name", os(name)),
            ("kind", os("object")),
            ("target", os(target)),
            ("observe-capability", os(capability)),
            ("operation-capability", os(capability)),
        ],
    )?;
    Ok(())
}

/// Write roster rows with the founder's own grant on the room.
fn roster_write(session: &Session, room: &str, fields: &[(u64, &str)]) -> Result<(), Done> {
    let actions: Vec<Value> = fields
        .iter()
        .map(|(f, v)| json!({"type":"create","key":{"type":"object","field":f.to_string()},"value":v}))
        .collect();
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
        "targets":[{"name":room,"payload":{"type":"scalar","actions":actions}}]});
    propose_submit(session, "roster", &request).map(|_| ())
}

pub(crate) fn me(session: &Session) -> Result<String, Done> {
    let ws = workspace_record(session).map_err(error)?;
    Ok(member(&ws, "subject").map_err(error)?.to_owned())
}

fn chat_new(session: &Session, name: &str, private: bool) -> Result<(), Done> {
    if room_path(session, name).exists() {
        return Err(usage(format!("this session already has a room {name}")));
    }
    let me = me(session)?;
    let law = author_law(&me);
    create_cell_as(session, name, "declared", &law, None, None, Some(if private { "private" } else { "chat" }),
        Some(&crate::credit::room_declared_fields()))?;
    if private {
        println!("room {name}: created private (only you write its roster; every say is sealed under the room key)");
    } else {
        println!("room {name}: created (only you write its roster)");
    }
    let stream_name = format!("{name}-me");
    let stream = create_cell(session, &stream_name, "stream", &law, Some(name), None)?;
    let stream_target = member(&stream, "target").map_err(error)?.to_owned();
    let grant = room_grant(session, name, &me, &MEMBER_GRANT.iter().map(|v| (*v).to_owned()).collect::<Vec<_>>())?;
    let grant_name = format!("{name}-room");
    import_from(session, &grant_name, &grant)?;
    roster_write(session, name, &[(2, &me), (3, &me), (4, &stream_target)])?;
    let room = Room { name: name.to_owned(), grant: grant_name, stream: Some(stream_name) };
    save_room(session, &room).map_err(error)?;
    let mut record = get_json(&room_path(session, name)).unwrap_or_default();
    record["founder"] = json!(me);
    put_json(&room_path(session, name), &record).map_err(error)?;
    set_current(session, name).map_err(error)?;
    println!("room {name}: your stream {stream_target}; you are its founder; it is your current room");
    Ok(())
}

/// What `chat invite` made: the invitation (the published room grant) and
/// the invitee's stream cell.
pub(crate) struct Invited {
    pub invitation: Value,
    pub stream: String,
}

fn chat_invite(session: &Session, name: &str, subject: &str, petname: Option<&str>, enc: Option<&str>, verbs: &[String]) -> Result<(), Done> {
    let invited = invite(session, name, subject, petname, enc, verbs)?;
    println!("invited {} to {name}: their stream {} (you paid for it; they own it)", petname.unwrap_or(subject), invited.stream);
    println!("give them this line:");
    println!("chat join {name} {}", serde_json::to_string(&invited.invitation).expect("JSON"));
    Ok(())
}

/// The founder adds `subject` to the roster of `name`: a room grant (`verbs`
/// under the room), the member's stream born `--in` the room under the
/// member's author law (the founder pays; the member owns it), the roster row;
/// in a private room also the room key wrapped to `enc` (PRIVATE-ROOMS).
pub(crate) fn invite(session: &Session, name: &str, subject: &str, petname: Option<&str>, enc: Option<&str>, verbs: &[String]) -> Result<Invited, Done> {
    let room = load_room(session, name).map_err(error)?;
    let private = room_is_private(session, name);
    let enc = match (private, enc) {
        (false, None) => None,
        (false, Some(_)) => return Err(usage(format!("{name} is not a private room: --enc is a private room's"))),
        (true, None) => {
            return Err(usage(format!("{name} is private: name the invitee's encryption key (--enc HEX, or @FILE in HOME/requests; their `whoami` prints it)")))
        }
        (true, Some(value)) => Some(match value.strip_prefix('@') {
            Some(file) if !file.is_empty() && !file.contains('/') && !file.starts_with('.') => {
                let p = session.home.join("requests").join(file);
                fs::read_to_string(&p).map_err(|e| error(format!("cannot read {}: {e}", p.display())))?.trim().to_owned()
            }
            Some(_) => return Err(usage("@FILE is a plain file name in HOME/requests")),
            None => value.to_owned(),
        }),
    };
    let me = me(session)?;
    let ws = workspace_record(session).map_err(error)?;
    let grant = reference(session, &room.grant).map_err(error)?;
    let roster = roster_of(&signed_read(session, &ws, name, "roster", &grant, "resource", &[])?);
    if roster.founder.as_deref() != Some(me.as_str()) {
        return Err(usage(format!("only the founder of {name} invites")));
    }
    // A kick/leave revokes grants but retains the stream and roster history.
    // Re-invitation gives fresh source authority and reuses that subject's slot.
    let prior=roster.members.iter().find(|(s,_)|s==subject).map(|(_,stream)|stream.clone());
    if prior.is_none() && roster.members.len()>=crate::room_schema::ROSTER_MEMBER_CAPACITY {
        return Err(usage(format!("the roster of {name} has reached its {} historical member slots; re-inviting an existing subject reuses its slot",crate::room_schema::ROSTER_MEMBER_CAPACITY)));
    }
    let invitation = room_grant(session, name, subject, verbs)?;
    let stream_target=if let Some(stream)=prior {stream}else {
        let slot=2*(roster.members.len() as u64+1)+1;
        let stream_name = format!("{name}-{}", &subject[subject.len().saturating_sub(10)..]);
        let stream = create_cell(session, &stream_name, "stream", &author_law(subject), Some(name), None)?;
        let stream_target=member(&stream,"target").map_err(error)?.to_owned();
        roster_write(session,name,&[(slot,subject),(slot+1,&stream_target)])?;
        stream_target
    };
    if let Some(enc) = &enc {
        // The room key, wrapped to the invitee's encryption key, in one write
        // to the keys cell (only the founder writes it).
        let id = fresh_id("wrap")?;
        client(
            "workspace",
            &[
                ("action", os("room-key")),
                ("op", os("invite")),
                ("dir", os(&session.workspace)),
                ("name", os(name)),
                ("member", os(subject)),
                ("enc-pub", os(enc)),
                ("proposal-id", os(&id)),
            ],
        )?;
    }
    if let Some(p) = petname {
        set_petname(session, subject, p).map_err(error)?;
    }
    let path = chat_dir(session).join("invites").join(format!("{name}-{subject}.json"));
    put_json(&path, &invitation).map_err(error)?;
    Ok(Invited { invitation, stream: stream_target })
}

/// `room ls`: the cells under the room that the Host's signed `since` view
/// names (every transaction above HEIGHT that wrote a cell this grant sees
/// under the room, and which cells), marked with the roster's streams and the
/// names this workspace holds for them. `--import` names each unnamed cell
/// `ROOM-cell-ID` under this room grant's capability, so later verbs can say
/// it; the reference is a hint, every use is a signed request.
fn room_ls(session: &Session, room: &Room, since: u64, import: bool, as_json: bool) -> Result<(), Done> {
    let ws = workspace_record(session).map_err(error)?;
    let grant = reference(session, &room.grant).map_err(error)?;
    let room_cell = member(&grant, "target").map_err(error)?.to_owned();
    let roster = roster_of(&signed_read(session, &ws, &room.name, "roster", &grant, "resource", &[])?);
    let view = signed_read(session, &ws, &room.name, "since", &grant, "since", &[("height", since.to_string())])?;
    let entries: Vec<Value> = view.get("entries").and_then(Value::as_array).cloned().unwrap_or_default();
    // cell -> (first height, last height, writers)
    let mut cells: BTreeMap<String, (String, String, Vec<String>)> = BTreeMap::new();
    for entry in &entries {
        let height = entry.get("height").and_then(Value::as_str).unwrap_or("0").to_owned();
        let subject = entry.get("subject").and_then(Value::as_str).unwrap_or("").to_owned();
        for cell in entry.get("cells").and_then(Value::as_array).into_iter().flatten().filter_map(Value::as_str) {
            let slot = cells.entry(cell.to_owned()).or_insert_with(|| (height.clone(), height.clone(), Vec::new()));
            slot.1 = height.clone();
            if !subject.is_empty() && !slot.2.contains(&subject) {
                slot.2.push(subject.clone());
            }
        }
    }
    let root = &session.workspace;
    let capability = member(&grant, "observeCapability").map_err(error)?.to_owned();
    let mut rows = Vec::new();
    for (cell, (first, last, writers)) in &cells {
        let mut names = crate::workspace::names_for_target(root, cell);
        let stream_of = roster.members.iter().find(|(_, s)| s == cell).map(|(subject, _)| subject.clone());
        if names.is_empty() && import && *cell != room_cell {
            let name = format!("{}-cell-{cell}", room.name);
            // The signed since result already proves this child's room lineage
            // under our grant. Retain its sealing hint in the first reference write.
            let sealed = grant.get("private").is_some_and(Value::is_object)
                .then_some((room.grant.as_str(), room_cell.as_str()));
            crate::workspace::import_with_private_context(root, crate::workspace::ImportInput {
                name: &name, kind: "object", target: cell,
                observe: &capability, operation: Some(&capability), control: None,
                provenance: None, room: None,
            }, sealed).map_err(error)?;
            names.push(name);
        }
        rows.push(json!({"cell":cell,"names":names,"room":*cell == room_cell,"stream":stream_of.is_some(),
            "streamOf":stream_of,"firstHeight":first,"lastHeight":last,"writers":writers}));
    }
    if as_json {
        println!("{}", json!({"type":"mini-room-ls-v1","room":room.name,"roomCell":room_cell,
            "founder":roster.founder,"since":since.to_string(),"cells":rows,"entries":entries,
            "authority":"signed since view under the room grant"}));
    } else {
        println!("# {} (cell {room_cell}): {} cells written above height {since}", room.name, rows.len());
        for row in &rows {
            let what = if row["room"] == json!(true) {
                "the room".to_owned()
            } else if let Some(owner) = row["streamOf"].as_str() {
                format!("stream of {owner}")
            } else {
                "cell".to_owned()
            };
            let names: Vec<String> = row["names"].as_array().into_iter().flatten().filter_map(Value::as_str).map(str::to_owned).collect();
            println!(
                "{:<22} {:<24} h{}..{} by {}  {}",
                row["cell"].as_str().unwrap_or(""),
                what,
                row["firstHeight"].as_str().unwrap_or(""),
                row["lastHeight"].as_str().unwrap_or(""),
                row["writers"].as_array().into_iter().flatten().filter_map(Value::as_str).collect::<Vec<_>>().join(","),
                names.join(",")
            );
        }
    }
    Ok(())
}

fn chat_join(session: &Session, name: &str, invitation: &str) -> Result<(), Done> {
    let value: Value = if let Some(file) = invitation.strip_prefix('@') {
        if file.is_empty() || file.contains('/') || file.starts_with('.') {
            return Err(usage("@FILE is a plain file name in HOME/requests"));
        }
        let p = session.home.join("requests").join(file);
        serde_json::from_slice(&fs::read(&p).map_err(|e| error(format!("cannot read {}: {e}", p.display())))?)
            .map_err(|e| usage(format!("the invitation is not JSON: {e}")))?
    } else {
        serde_json::from_str(invitation).map_err(|e| usage(format!("the invitation is not JSON: {e}")))?
    };
    let me = me(session)?;
    if value.get("recipient").and_then(Value::as_str) != Some(me.as_str()) {
        return Err(usage(format!("this invitation is not addressed to you ({me})")));
    }
    import_from(session, name, &value)?;
    let mut room = Room { name: name.to_owned(), grant: name.to_owned(), stream: None };
    let ws = workspace_record(session).map_err(error)?;
    let grant = reference(session, name).map_err(error)?;
    let roster = roster_of(&signed_read(session, &ws, name, "roster", &grant, "resource", &[])?);
    if let Some((_, stream)) = roster.members.iter().find(|(s, _)| *s == me) {
        let stream_name = format!("{name}-me");
        let capability = member(&grant, "observeCapability").map_err(error)?.to_owned();
        import_stream(session, &stream_name, stream, &capability)?;
        room.stream = Some(stream_name);
    }
    save_room(session, &room).map_err(error)?;
    if let Some(f) = &roster.founder {
        let mut record = get_json(&room_path(session, name)).unwrap_or_default();
        record["founder"] = json!(f);
        put_json(&room_path(session, name), &record).map_err(error)?;
    }
    set_current(session, name).map_err(error)?;
    match &room.stream {
        Some(_) => println!("joined {name}: {} members; it is your current room", roster.members.len()),
        None => println!("joined {name} to read; you have no stream on its roster yet (ask the founder)"),
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(height: u64, author: &str, cell: &str, sequence: u64, payload: &str) -> Entry {
        Entry {
            height,
            author: author.into(),
            cell: cell.into(),
            sequence,
            topic: String::new(),
            to: None,
            re: None,
            payload: Payload::Verified(payload.into()),
            owner: author.into(),
        }
    }

    #[test]
    fn chat_verbs_take_the_rest_of_the_line_as_text() {
        assert_eq!(
            plan("say it's #1, isn't it").unwrap().unwrap(),
            Line::Say { room: None, to: None, re: None, text: Text::Inline("it's #1, isn't it".into()), via: None }
        );
        assert_eq!(
            plan("say --to @bob --re 12 'yes, agreed'").unwrap().unwrap(),
            Line::Say { room: None, to: Some("bob".into()), re: Some(12), text: Text::Inline("yes, agreed".into()), via: None }
        );
        assert_eq!(
            plan("say --in commons --via discord --via-id 42 --via-name zed --file d-1.txt").unwrap().unwrap(),
            Line::Say {
                room: Some("commons".into()),
                to: None,
                re: None,
                text: Text::File("d-1.txt".into()),
                via: Some(Via { network: "discord".into(), id: "42".into(), name: "zed".into() })
            }
        );
        assert!(plan("say").unwrap().is_err());
        assert!(plan("say --via discord hi").unwrap().is_err());
        assert!(plan("say --re zero hi").unwrap().is_err());
        assert_eq!(
            plan("tail -n 5 --since 30 --follow").unwrap().unwrap(),
            Line::Tail { room: None, count: 5, since: Some(30), follow: true, json: false, held: false, entry: None, discovery: None }
        );
        assert_eq!(
            plan("tail --in commons --json --held").unwrap().unwrap(),
            Line::Tail { room: Some("commons".into()), count: 20, since: None, follow: false, json: true, held: true, entry: None, discovery: None }
        );
        assert!(plan("tail --held --follow").unwrap().is_err());
        assert!(plan("tail --bogus").unwrap().is_err());
        assert_eq!(plan("topic").unwrap().unwrap(), Line::Topic(None));
        assert_eq!(plan("topic release planning").unwrap().unwrap(), Line::Topic(Some("release planning".into())));
        assert!(plan(&format!("topic {}", "x".repeat(65))).unwrap().is_err());
        assert_eq!(plan("pin #3").unwrap().unwrap(), Line::Pin(3));
        assert_eq!(plan("unpin").unwrap().unwrap(), Line::Unpin);
        assert_eq!(plan("react 3 👍").unwrap().unwrap(), Line::React { number: 3, emoji: "👍".into() });
        assert!(plan("react 3 two words").unwrap().is_err());
        assert_eq!(plan("chat new commons").unwrap().unwrap(), Line::New { room: "commons".into(), private: false });
        assert_eq!(plan("chat new den --private").unwrap().unwrap(), Line::New { room: "den".into(), private: true });
        assert_eq!(
            plan("chat invite commons 1234 bob").unwrap().unwrap(),
            Line::Invite { room: "commons".into(), subject: "1234".into(), name: Some("bob".into()), enc: None, verbs: vec!["observe".into(), "append".into()] }
        );
        assert_eq!(
            plan("chat invite den 1234 --enc ab12 bob").unwrap().unwrap(),
            Line::Invite { room: "den".into(), subject: "1234".into(), name: Some("bob".into()), enc: Some("ab12".into()), verbs: vec!["observe".into(), "append".into()] }
        );
        assert_eq!(
            plan(r#"chat join commons {"a": "b c"}"#).unwrap().unwrap(),
            Line::Join { room: "commons".into(), invitation: r#"{"a": "b c"}"#.into() }
        );
        assert!(plan("chat name 12 345").unwrap().is_err());
        assert!(plan("read shared").is_none());
    }

    #[test]
    fn merge_order_is_height_then_author_cell_sequence_and_numbers_are_stable() {
        let a = entry(21, "900", "5", 1, r#"{"type":"say","text":"a1"}"#);
        let b = entry(22, "1000", "6", 1, r#"{"type":"say","text":"b1"}"#);
        // one transaction appending to two streams: same height, author orders
        let c = entry(23, "80", "7", 1, r#"{"type":"say","text":"c1"}"#);
        let d = entry(23, "900", "5", 2, r#"{"type":"say","text":"a2"}"#);
        let one = merge(vec![d.clone(), b.clone(), c.clone(), a.clone()], None);
        let two = merge(vec![a.clone(), c.clone(), d.clone(), b.clone()], None);
        let order = |f: &Feed| f.feed.iter().map(|e| (e.cell.clone(), e.sequence)).collect::<Vec<_>>();
        assert_eq!(order(&one), order(&two));
        assert_eq!(order(&one), vec![("5".into(), 1), ("6".into(), 1), ("7".into(), 1), ("5".into(), 2)]);
        // a later append never renumbers the earlier entries
        let later = entry(30, "1", "8", 1, r#"{"type":"say","text":"late"}"#);
        let three = merge(vec![later, a, b, c, d], None);
        assert_eq!(order(&three)[..4], order(&one)[..]);
        assert_eq!(num_cmp("1000", "900"), Ordering::Greater);
    }

    #[test]
    fn only_the_founders_topic_and_pin_count_and_reactions_aggregate() {
        let mut pin_by_b = entry(4, "2", "b", 2, r#"{"type":"pin"}"#);
        pin_by_b.re = Some(("b".into(), 1));
        let mut pin_by_a = entry(5, "1", "a", 2, r#"{"type":"pin"}"#);
        pin_by_a.re = Some(("b".into(), 1));
        let mut react_c = entry(6, "3", "c", 1, r#"{"type":"react","emoji":"+1"}"#);
        react_c.re = Some(("b".into(), 1));
        let mut react_c_again = entry(7, "3", "c", 2, r#"{"type":"react","emoji":"+1"}"#);
        react_c_again.re = Some(("b".into(), 1));
        let feed = merge(
            vec![
                entry(1, "1", "a", 1, r#"{"type":"topic","text":"plans"}"#),
                entry(2, "2", "b", 1, r#"{"type":"say","text":"hi"}"#),
                entry(3, "2", "b", 3, r#"{"type":"topic","text":"hijack"}"#),
                pin_by_b,
                pin_by_a,
                react_c,
                react_c_again,
            ],
            Some("1".into()),
        );
        assert_eq!(feed.topic, Some(("plans".into(), 1)));
        assert_eq!(feed.pin, Some((2, 5)));
        assert_eq!(feed.reactions.get(&2).and_then(|r| r.get("+1")), Some(&vec!["3".to_owned()]));
        let names = Names { me: "1".into(), pet: [("2".into(), "bob".into())].into_iter().collect() };
        assert!(render_entry(&feed, 3, &names).contains("ignored: only me, the founder, sets the topic"));
        assert!(render_entry(&feed, 4, &names).contains("ignored: only me, the founder, pins"));
        assert_eq!(render_entry(&feed, 2, &names), "#2 h2 bob: hi\n      +1 s…3");
    }

    #[test]
    fn exact_signed_history_selection_survives_over_hundred_intervening_entries() {
        let feed=merge((1..=140).map(|n|entry(n,"20","99",n,r#"{"type":"say","text":"message"}"#)).collect(),None);
        assert_eq!(shown_entries(&feed,None,Some(&("99".into(),1))),vec![1]);
        assert!(shown_entries(&feed,None,Some(&("98".into(),1))).is_empty());
        assert_eq!(shown_entries(&feed,Some(130),None).len(),10);
        assert!(parse_tail("--entry 99:1 --since 5").is_err());
        assert!(parse_tail("--entry 99:0").is_err());
        assert!(matches!(parse_tail("--entry 99:1 --json").unwrap(),Line::Tail {entry:Some(_),..}));
    }

    #[test]
    fn unverified_text_is_never_printed() {
        let view = json!({"type":"stream-tail","entries":[
            {"sequence":"1","author":"7","height":"9","transaction":"1","topic":"","payloadDigest":"1","to":null,"ref":null,
             "payload":null,"payloadState":"mismatch"},
            {"sequence":"2","author":"7","height":"10","transaction":"2","topic":"","payloadDigest":"1","to":null,"ref":null,
             "payload":hex(r#"{"type":"say","text":"ok"}"#),"payloadState":"verified"},
            {"sequence":"3","author":"7","height":"11","transaction":"3","topic":"","payloadDigest":"1","to":null,"ref":null,
             "payload":hex("forged"),"payloadState":"absent"}]});
        let feed = merge(entries_of(&view, "5", "7"), None);
        let names = Names { me: "0".into(), pet: BTreeMap::new() };
        assert_eq!(render_entry(&feed, 1, &names), "#1 h9 s…7: [payload unavailable]");
        assert_eq!(render_entry(&feed, 2, &names), "#2 h10 s…7: ok");
        assert_eq!(render_entry(&feed, 3, &names), "#3 h11 s…7: [payload unavailable]");
    }

    fn hex(text: &str) -> String {
        text.bytes().map(|b| format!("{b:02x}")).collect()
    }

    #[test]
    fn a_bridged_message_is_shown_as_the_bridge_saying_it() {
        let feed = merge(
            vec![entry(3, "55", "9", 1, r#"{"type":"say","text":"hello","via":"discord","author":{"id":"4242","name":"zed"}}"#)],
            None,
        );
        let names = Names { me: "1".into(), pet: [("55".into(), "bridge".into())].into_iter().collect() };
        assert_eq!(render_entry(&feed, 1, &names), "#1 h3 bridge via discord zed#4242: hello");
    }

    #[test]
    fn the_roster_reads_founder_and_member_rows() {
        let view = json!({"type":"resource","cell":{"root":"1","entries":[
            {"key":{"type":"object","resource":"9","field":"1"},"value":"0"},
            {"key":{"type":"object","resource":"9","field":"2"},"value":"100"},
            {"key":{"type":"object","resource":"9","field":"3"},"value":"100"},
            {"key":{"type":"object","resource":"9","field":"4"},"value":"500"},
            {"key":{"type":"object","resource":"9","field":"5"},"value":"200"},
            {"key":{"type":"object","resource":"9","field":"6"},"value":"600"}]}});
        assert_eq!(
            roster_of(&view),
            Roster { founder: Some("100".into()), members: vec![("100".into(), "500".into()), ("200".into(), "600".into())] }
        );
    }

    #[test]
    fn the_template_law_is_the_author_law() {
        let law = author_law("77");
        assert_eq!(law["type"], "any");
        assert_eq!(law["predicates"][1], json!({"type":"eq","slot":"request/subject","value":"77"}));
        assert_eq!(law["predicates"][0]["predicate"]["values"], json!(["2", "7"]));
    }

    #[test]
    fn a_refused_child_keeps_the_hosts_lines() {
        let (code, text) = child_ending(Some(3), "workspace attempt: /x\nrefused: law-denied: request/subject == 5\n  Host refused prepare, reply byte 255\n  client: x\n");
        assert_eq!(code, EXIT_REFUSED);
        assert!(text.starts_with("refused: law-denied: request/subject == 5\n"));
        assert_eq!(child_ending(Some(1), "mini: no such reference").1, "error: no such reference\n");
    }
}
