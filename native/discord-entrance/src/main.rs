//! `mini-discord`: the Discord interactions endpoint for Mini.
//!
//! Takes no arguments. Configuration is the environment (the unit's 0600 `EnvironmentFile`,
//! `/etc/mini/discord.env`), so the application id and key never appear on argv:
//!
//! | variable | meaning |
//! |---|---|
//! | `MINI_DISCORD_APPLICATION_ID` | the Discord application (snowflake) |
//! | `MINI_DISCORD_PUBLIC_KEY` | the application's Ed25519 public key, hex |
//! | `MINI_DISCORD_LISTEN` | loopback address Caddy proxies to (default `127.0.0.1:8793`) |
//! | `MINI_DISCORD_ROSTER` | `discord_user_id -> session NAME` (default `/etc/mini/discord-roster.json`) |
//! | `MINI_DISCORD_ROSTER_OWNER_UID` | the uid that must own the roster (default 0) |
//! | `MINI_DISCORD_API_BASE` | default `https://discord.com/api/v10` (the evidence run points it at a loopback fake) |
//! | `MINI_DISCORD_SPOOL` | private directory for follow-up bodies (default `/run/mini-discord`) |
//! | `MINI_DISCORD_MAX_INFLIGHT` | lines running at once (default 4) |
//! | `MINI_SHELL_WRAPPER` `MINI_CLIENT` `MINI_HOST` `MINI_CONFIG` `MINI_SOCKET` | the ssh entrance's forced command and its first four arguments |
//! | `MINI_SESSIONS` `MINI_SPONSOR` `MINI_SPONSOR_WORKSPACE` | the session layout (`render-authorized-keys.sh`'s) |
//! | `MINI_LINE_TIMEOUT_S` | a line is stopped after this long (default 120) |
//! | `MINI_SESSION_RUNNER` | split tenancy: the root runner; each line runs as `sudo -n -- RUNNER NAME`, the line on stdin, as the session's own account |
//! | `MINI_DISCORD_STATE` | split tenancy: this account's own directory for interaction custody and the per-session line log (required with the runner, refused without it) |

use std::net::TcpListener;

use minidregg_discord_entrance::server::{App, Config};

fn main() {
    if std::env::args().len() > 1 {
        eprintln!("mini-discord takes no arguments; configure it through the environment (see the unit's EnvironmentFile)");
        std::process::exit(64);
    }
    let cfg = match Config::from_env() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("mini-discord: {e}");
            std::process::exit(78);
        }
    };
    let listen = cfg.listen.clone();
    let app = match App::new(cfg) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("mini-discord: {e}");
            std::process::exit(78);
        }
    };
    let listener = match TcpListener::bind(&listen) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("mini-discord: bind {listen}: {e}");
            std::process::exit(69);
        }
    };
    eprintln!("mini-discord: serving interactions on {listen}");
    app.serve(listener)
}
