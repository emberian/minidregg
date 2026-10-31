//! A thin Discord entrance to Mini.
//!
//! Discord POSTs signed interactions to an HTTPS URL (the interactions-endpoint model: no
//! gateway websocket, no long-lived connection). This crate is that endpoint. A Discord user
//! is mapped by a root-owned roster to one Mini session NAME, and the slash command's one
//! string option is handed, as one argument, to the same forced command the ssh entrance
//! uses (`mini-shell-ssh`, the candidate's `mini-line`, via `SSH_ORIGINAL_COMMAND`). `/mini-world` renders
//! the common native member projection; `/mini-status` retrieves actor-bound transport custody.
//! The session's workspace
//! and home are derived from NAME exactly as `render-authorized-keys.sh` derives them; the
//! Discord user chooses neither. There is no second verb set: `mini shell` decides what the
//! line means.
//!
//! * [`http`]: a bounded HTTP/1.1 request reader and response writer (plain HTTP; TLS is
//!   Caddy's). The tests' client is `tests/support/client.rs`, not part of this library.
//! * [`signature`]: Discord's `X-Signature-Ed25519` over `X-Signature-Timestamp || body`.
//! * [`interaction`]: the interaction JSON in, the response JSON out.
//! * [`roster`]: `discord_user_id -> session NAME`, fail-closed on ownership and shape.
//! * [`session`]: one line through the ssh entrance's forced command, and the `discord.log`.
//! * [`reply`]: the shell's ending line, and fitting output into Discord's 2000 characters.
//! * [`curl`]: the interaction follow-up PATCH through `/usr/bin/curl`; the URL (which carries
//!   the interaction token) reaches curl on stdin, never argv.
//! * [`gateway`]: gateway mode: the same interactions over Discord's WebSocket, for an
//!   application with no Interactions Endpoint URL; replies through the REST callback.
//! * [`server`]: the endpoint itself: verify, answer PING, refuse early, defer, run, PATCH.
//! * [`door`]: the self-serve door's queue schema, shared by the `/join` form (`mini-door`),
//!   the entrance's `/mini line:link CODE`, and the root processor (`mini-door-process`).
//!
//! Durable custody (leased owner-private records, delivery custody) is `mini_sdk::store` and
//! `mini_sdk::custody`, the one implementation Mini clients share.

pub mod curl;
pub mod door;
pub mod gateway;
pub mod navigation;
pub mod http;
pub mod interaction;
pub mod reply;
pub mod roster;
pub mod server;
pub mod session;
pub mod signature;

/// Seconds since the Unix epoch.
pub fn now_s() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

/// A required environment variable.
pub fn env_required(name: &str) -> Result<String, String> {
    match std::env::var(name) {
        Ok(v) if !v.is_empty() => Ok(v),
        _ => Err(format!("{name} is not set")),
    }
}

/// A required environment variable that must be an absolute path.
pub fn env_path(name: &str) -> Result<std::path::PathBuf, String> {
    let v = env_required(name)?;
    if !v.starts_with('/') {
        return Err(format!("{name} must be an absolute path"));
    }
    Ok(std::path::PathBuf::from(v))
}

/// An optional numeric environment variable.
pub fn env_u64(name: &str, default: u64) -> Result<u64, String> {
    match std::env::var(name) {
        Ok(v) if !v.is_empty() => v.parse().map_err(|_| format!("{name} must be a number")),
        _ => Ok(default),
    }
}
