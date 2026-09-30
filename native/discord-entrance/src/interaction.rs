//! The interaction JSON in and the response JSON out.
//!
//! Only what the entrance uses is read: the type, the interaction id and token, the
//! application id, the invoking user's id (`member.user.id` in a guild, `user.id` in a DM),
//! the command name and its one string option `line`. Every response and follow-up is
//! ephemeral (flag 64: only the invoking user sees their own session's output) and mentions
//! nobody (`allowed_mentions.parse = []`), so output text cannot ping a channel.

use serde_json::{json, Value};

/// `/mini <line>`: one line for the session.
pub const COMMAND_LINE: &str = "mini";
/// `/mini-help`: the shell's own `help`.
pub const COMMAND_HELP: &str = "mini-help";
/// The name of `/mini`'s one string option.
pub const OPTION_LINE: &str = "line";
/// Discord's EPHEMERAL message flag.
pub const EPHEMERAL: u64 = 64;

#[derive(Debug, PartialEq, Eq)]
pub enum Interaction {
    Ping,
    Command(Command),
    Unsupported(u64),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Command {
    pub id: String,
    pub application_id: String,
    pub token: String,
    pub user_id: String,
    pub name: String,
    pub line: Option<String>,
}

fn str_at<'a>(v: &'a Value, path: &[&str]) -> Option<&'a str> {
    let mut cur = v;
    for p in path {
        cur = cur.get(p)?;
    }
    cur.as_str()
}

pub fn parse(body: &[u8]) -> Result<Interaction, String> {
    let v: Value = serde_json::from_slice(body).map_err(|e| format!("interaction JSON: {e}"))?;
    let kind = v.get("type").and_then(Value::as_u64).ok_or("interaction has no type")?;
    match kind {
        1 => Ok(Interaction::Ping),
        2 => {
            let field = |path: &[&str], what: &str| {
                str_at(&v, path).map(str::to_string).ok_or(format!("interaction has no {what}"))
            };
            let id = field(&["id"], "id")?;
            let application_id = field(&["application_id"], "application_id")?;
            let token = field(&["token"], "token")?;
            let user_id = str_at(&v, &["member", "user", "id"])
                .or_else(|| str_at(&v, &["user", "id"]))
                .map(str::to_string)
                .ok_or("interaction has no invoking user")?;
            let name = field(&["data", "name"], "command name")?;
            let line = v
                .get("data")
                .and_then(|d| d.get("options"))
                .and_then(Value::as_array)
                .and_then(|opts| {
                    opts.iter().find(|o| o.get("name").and_then(Value::as_str) == Some(OPTION_LINE))
                })
                .and_then(|o| o.get("value"))
                .and_then(Value::as_str)
                .map(str::to_string);
            Ok(Interaction::Command(Command { id, application_id, token, user_id, name, line }))
        }
        other => Ok(Interaction::Unsupported(other)),
    }
}

/// PONG.
pub fn pong() -> Value {
    json!({ "type": 1 })
}

/// CHANNEL_MESSAGE_WITH_SOURCE, ephemeral: an answer decided before any line ran.
pub fn message(content: &str) -> Value {
    json!({
        "type": 4,
        "data": { "content": content, "flags": EPHEMERAL, "allowed_mentions": { "parse": [] } }
    })
}

/// DEFERRED_CHANNEL_MESSAGE_WITH_SOURCE, ephemeral: the line is running; the answer is the
/// follow-up edit of `@original`.
pub fn deferred() -> Value {
    json!({ "type": 5, "data": { "flags": EPHEMERAL } })
}

/// The body of the `PATCH …/messages/@original` follow-up, or of a channel-webhook post.
pub fn followup(content: &str) -> Value {
    json!({ "content": content, "allowed_mentions": { "parse": [] } })
}

/// A Discord snowflake: decimal digits only.
pub fn is_snowflake(s: &str) -> bool {
    (1..=20).contains(&s.len()) && s.bytes().all(|b| b.is_ascii_digit())
}

/// An interaction token as it may appear in a URL path segment.
pub fn is_token(s: &str) -> bool {
    (1..=512).contains(&s.len())
        && s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-' || b == b'.')
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_ping_guild_and_dm_commands() {
        assert_eq!(parse(br#"{"type":1,"id":"1"}"#).unwrap(), Interaction::Ping);
        let guild = br#"{"type":2,"id":"11","application_id":"22","token":"tok-1",
            "member":{"user":{"id":"33"}},"data":{"name":"mini","options":[{"name":"line","type":3,"value":"read shared"}]}}"#;
        assert_eq!(
            parse(guild).unwrap(),
            Interaction::Command(Command {
                id: "11".into(),
                application_id: "22".into(),
                token: "tok-1".into(),
                user_id: "33".into(),
                name: "mini".into(),
                line: Some("read shared".into()),
            })
        );
        let dm = br#"{"type":2,"id":"11","application_id":"22","token":"t","user":{"id":"44"},"data":{"name":"mini-help"}}"#;
        match parse(dm).unwrap() {
            Interaction::Command(c) => {
                assert_eq!(c.user_id, "44");
                assert_eq!(c.line, None);
            }
            other => panic!("{other:?}"),
        }
        assert_eq!(parse(br#"{"type":3}"#).unwrap(), Interaction::Unsupported(3));
        assert!(parse(br#"{"type":2,"id":"1"}"#).is_err());
        assert!(parse(b"not json").is_err());
    }

    #[test]
    fn responses_are_ephemeral_and_mention_nobody() {
        let m = message("x");
        assert_eq!(m["data"]["flags"], EPHEMERAL);
        assert_eq!(m["data"]["allowed_mentions"]["parse"], json!([]));
        assert_eq!(deferred()["type"], 5);
        assert_eq!(deferred()["data"]["flags"], EPHEMERAL);
        assert_eq!(followup("x")["allowed_mentions"]["parse"], json!([]));
    }

    #[test]
    fn token_and_snowflake_shapes() {
        assert!(is_snowflake("123456789012345678"));
        assert!(!is_snowflake("12a"));
        assert!(!is_snowflake(""));
        assert!(is_token("aW50ZXJhY3Rpb24.abc_-"));
        assert!(!is_token("a/b"));
        assert!(!is_token("a?b"));
        assert!(!is_token("a\"b"));
    }
}
