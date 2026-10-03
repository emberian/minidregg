//! A loopback fake of Discord, for evidence and tests. Not deployed.
//!
//! Discord's two roles toward an interactions endpoint:
//!
//! * `interact`: the signer. Builds a slash-command interaction exactly as Discord sends it
//!   (`type 2`, `member.user.id`, `data.name`, `data.options[{name:"line",type:3,value}]`),
//!   signs `timestamp || body` with the application's Ed25519 key and POSTs it with
//!   `X-Signature-Ed25519` / `X-Signature-Timestamp`. `--corrupt-signature` flips one
//!   signature byte after signing. `ping` sends type 1.
//! * `api`: the webhook API. Accepts the follow-up `PATCH /api/v10/webhooks/APP/TOKEN/messages/@original`
//!   and channel-webhook `POST /api/webhooks/ID/TOKEN`, and records each body under DIR.
//!   It also keeps one channel, 701 (`DIR/channel-701.json`): a webhook post appears there
//!   as a message with `webhook_id`; `POST /fake/channels/701/messages` adds a person's
//!   message; `GET /api/v10/channels/701/messages?after=ID` answers Discord's shape (newest
//!   first) to `Authorization: Bot fake-bot-token` and 401 otherwise.
//!
//! ```text
//! fake-discord keygen SECRET_FILE                       # prints the public key hex
//! fake-discord ping ADDR SECRET_FILE
//! fake-discord interact ADDR SECRET_FILE APP USER ID TOKEN COMMAND [--line L | --line-file F] [--corrupt-signature]
//! fake-discord api ADDR DIR                             # serves until killed
//! ```

use std::io::Read;
use std::net::TcpListener;

use ed25519_dalek::{Signer, SigningKey};
use minidregg_discord_entrance::http::{client_request, read_request, write_response};
use minidregg_discord_entrance::now_s;
use minidregg_discord_entrance::signature::{hex_decode, hex_encode};
use serde_json::json;

fn die(msg: impl std::fmt::Display) -> ! {
    eprintln!("fake-discord: {msg}");
    std::process::exit(2);
}

fn key(path: &str) -> SigningKey {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| die(format!("{path}: {e}")));
    let bytes: [u8; 32] = hex_decode(text.trim()).and_then(|b| b.try_into().ok()).unwrap_or_else(|| die("bad secret"));
    SigningKey::from_bytes(&bytes)
}

fn post_signed(addr: &str, k: &SigningKey, body: &[u8], corrupt: bool) {
    let ts = now_s().to_string();
    let mut msg = ts.as_bytes().to_vec();
    msg.extend_from_slice(body);
    let mut sig = k.sign(&msg).to_bytes();
    if corrupt {
        sig[0] ^= 0x01;
    }
    let sig = hex_encode(&sig);
    let headers = [
        ("Content-Type", "application/json"),
        ("X-Signature-Ed25519", sig.as_str()),
        ("X-Signature-Timestamp", ts.as_str()),
    ];
    let (status, resp) = client_request(addr, "POST", "/interactions", &headers, body).unwrap_or_else(|e| die(e));
    println!("HTTP {status}");
    println!("{}", String::from_utf8_lossy(&resp));
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let a: Vec<&str> = args.iter().map(String::as_str).collect();
    match a.as_slice() {
        ["keygen", out] => {
            let mut seed = [0u8; 32];
            std::fs::File::open("/dev/urandom")
                .and_then(|mut f| f.read_exact(&mut seed))
                .unwrap_or_else(|e| die(e));
            std::fs::write(out, hex_encode(&seed)).unwrap_or_else(|e| die(e));
            println!("{}", hex_encode(SigningKey::from_bytes(&seed).verifying_key().as_bytes()));
        }
        ["ping", addr, secret] => {
            let body = json!({ "type": 1, "id": "1", "application_id": "1", "token": "ping" }).to_string();
            post_signed(addr, &key(secret), body.as_bytes(), false);
        }
        ["interact", addr, secret, app, user, id, token, command, rest @ ..] => {
            let mut line: Option<String> = None;
            let mut corrupt = false;
            let mut target: Option<String> = None;
            let mut page: Option<u64> = None;
            let mut i = 0;
            while i < rest.len() {
                match rest[i] {
                    "--line" if i + 1 < rest.len() => {
                        line = Some(rest[i + 1].to_string());
                        i += 1;
                    }
                    "--line-file" if i + 1 < rest.len() => {
                        let t = std::fs::read_to_string(rest[i + 1]).unwrap_or_else(|e| die(e));
                        line = Some(t.trim_end_matches('\n').to_string());
                        i += 1;
                    }
                    "--target" if i + 1 < rest.len() => {target=Some(rest[i+1].to_string());i+=1;},
                    "--page" if i + 1 < rest.len() => {page=Some(rest[i+1].parse().unwrap_or_else(|_|die("bad page")));i+=1;},
                    "--corrupt-signature" => corrupt = true,
                    other => die(format!("unknown option {other}")),
                }
                i += 1;
            }
            let mut data = json!({ "id": "900", "name": command, "type": 1 });
            if let Some(l) = line {
                data["options"] = json!([{ "name": "line", "type": 3, "value": l }]);
            }
            if let Some(t)=target {data["options"]=json!([{"name":"target","type":3,"value":t}]);}
            if let Some(p)=page {if !data["options"].is_array(){data["options"]=json!([])}data["options"].as_array_mut().unwrap().push(json!({"name":"page","type":4,"value":p}));}
            let body = json!({
                "type": 2,
                "id": id,
                "application_id": app,
                "token": token,
                "version": 1,
                "guild_id": "700",
                "channel_id": "701",
                "member": { "user": { "id": user, "username": format!("user-{user}") } },
                "data": data,
            })
            .to_string();
            post_signed(addr, &key(secret), body.as_bytes(), corrupt);
        }
        ["api", addr, dir] => {
            let listener = TcpListener::bind(addr).unwrap_or_else(|e| die(e));
            eprintln!("fake-discord api on {addr}, recording to {dir}");
            for stream in listener.incoming() {
                let Ok(mut stream) = stream else { continue };
                let Ok(req) = read_request(&mut stream) else { continue };
                let parts: Vec<&str> = req.path.trim_start_matches('/').split('/').collect();
                let file = match (req.method.as_str(), parts.as_slice()) {
                    ("PATCH", ["api", "v10", "webhooks", _app, token, "messages", "@original"]) => {
                        format!("{dir}/followup-{token}.json")
                    }
                    ("POST", ["api", "webhooks", id, token]) => {
                        // A webhook post shows up in the channel as a message from that webhook.
                        let content = serde_json::from_slice::<serde_json::Value>(&req.body)
                            .ok()
                            .and_then(|v| v.get("content").and_then(|c| c.as_str()).map(str::to_owned))
                            .unwrap_or_default();
                        channel_append(dir, json!({"content": content, "webhook_id": id,
                            "author": {"id": id, "username": "mirror", "bot": true}}));
                        format!("{dir}/channel-{token}-{}.json", now_s_nanos())
                    }
                    ("POST", ["fake", "channels", "701", "messages"]) => {
                        // A person typing in the channel (the test's hand).
                        match serde_json::from_slice::<serde_json::Value>(&req.body) {
                            Ok(message) => channel_append(dir, message),
                            Err(_) => {
                                let _ = write_response(&mut stream, 400, "Bad Request", "text/plain", b"not json\n");
                                continue;
                            }
                        }
                        format!("{dir}/human-{}.json", now_s_nanos())
                    }
                    ("GET", ["api", "v10", "channels", "701", "messages"]) => {
                        let bot = req.headers.iter().any(|(k, v)| k.eq_ignore_ascii_case("authorization") && v == "Bot fake-bot-token");
                        if !bot {
                            let _ = write_response(&mut stream, 401, "Unauthorized", "application/json", b"{\"message\":\"401: Unauthorized\"}");
                            continue;
                        }
                        let after = req.query.split('&').find_map(|kv| kv.strip_prefix("after=")).and_then(|a| a.parse::<u64>().ok()).unwrap_or(0);
                        let before = req.query.split('&').find_map(|kv| kv.strip_prefix("before=")).and_then(|a| a.parse::<u64>().ok()).unwrap_or(u64::MAX);
                        let all = channel_read(dir);
                        let mut newer: Vec<serde_json::Value> = all
                            .into_iter()
                            .filter(|m| m.get("id").and_then(|i| i.as_str()).and_then(|i| i.parse::<u64>().ok()).is_some_and(|i| i > after && i < before))
                            .collect();
                        newer.reverse(); // Discord answers newest first
                        newer.truncate(50);
                        let body = serde_json::to_vec(&newer).unwrap_or_default();
                        let _ = std::fs::write(format!("{dir}/channel-read-{}.json", now_s_nanos()), &body);
                        let _ = write_response(&mut stream, 200, "OK", "application/json", &body);
                        continue;
                    }
                    _ => {
                        let _ = write_response(&mut stream, 404, "Not Found", "text/plain", b"no such route\n");
                        continue;
                    }
                };
                let _ = std::fs::write(&file, &req.body);
                let log = format!("{} {} {} -> {}\n", now_s(), req.method, req.path, file);
                let _ = std::fs::OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(format!("{dir}/requests.log"))
                    .and_then(|mut f| std::io::Write::write_all(&mut f, log.as_bytes()));
                let _ = write_response(&mut stream, 200, "OK", "application/json", b"{\"id\":\"1\"}");
            }
        }
        _ => die("usage: keygen FILE | ping ADDR SECRET | interact ADDR SECRET APP USER ID TOKEN COMMAND [--line L|--line-file F] [--corrupt-signature] | api ADDR DIR"),
    }
}

/// The fake channel 701: a JSON array of messages, oldest first, ids from 1000.
fn channel_read(dir: &str) -> Vec<serde_json::Value> {
    std::fs::read(format!("{dir}/channel-701.json"))
        .ok()
        .and_then(|b| serde_json::from_slice(&b).ok())
        .unwrap_or_default()
}

fn channel_append(dir: &str, mut message: serde_json::Value) {
    let mut all = channel_read(dir);
    message["id"] = json!((1000 + all.len()).to_string());
    message["channel_id"] = json!("701");
    all.push(message);
    let _ = std::fs::write(format!("{dir}/channel-701.json"), serde_json::to_vec(&all).unwrap_or_default());
}

fn now_s_nanos() -> u128 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0)
}
