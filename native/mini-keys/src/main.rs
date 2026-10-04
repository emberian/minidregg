//! `mini-keys`: the key broker and its small clients.
//!
//!   mini-keys serve --config /etc/mini/keys/broker.json
//!       the broker (as its own account; the config and every ancestor root-owned)
//!   mini-keys relay [--client-config FILE | --socket SOCKET --uid UID]
//!       the ssh forced command for `mini-provider-credentials-v1`: one
//!       member-action exchange, stdin/stdout spliced to the broker
//!   mini-keys hello [--client-config FILE | --socket SOCKET --uid UID]
//!       which roles this account holds at the broker
//!   mini-keys pool --action set|revoke|ls [--provider NAME] [--secret FILE|-] [--runner R]
//!       the operator's pool key (root)
//!   mini-keys namespace --config BROKER_CONFIG --subject N --public-key HEX
//!       public namespace metadata for the root namespace helper; reads no key
use mini_keys::client::{Broker, CLIENT_CONFIG};
use mini_keys::server::{self, credentials, Config};
use mini_keys::{peer, wire};
use serde_json::{json, Value};
use std::io::{Read, Write};
use std::net::Shutdown;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

fn fail(message: impl std::fmt::Display) -> ! {
    eprintln!("mini-keys: {message}");
    std::process::exit(1);
}

struct Args(Vec<String>);

impl Args {
    fn take(&mut self, name: &str) -> Option<String> {
        let flag = format!("--{name}");
        let i = self.0.iter().position(|a| a == &flag)?;
        if i + 1 >= self.0.len() {
            fail(format!("{flag} needs a value"));
        }
        let v = self.0.remove(i + 1);
        self.0.remove(i);
        Some(v)
    }
    fn need(&mut self, name: &str) -> String {
        self.take(name).unwrap_or_else(|| fail(format!("--{name} is required")))
    }
    fn done(self) {
        if !self.0.is_empty() {
            fail(format!("unexpected arguments: {}", self.0.join(" ")));
        }
    }
}

fn broker(args: &mut Args) -> Broker {
    match (args.take("socket"), args.take("uid")) {
        (Some(socket), Some(uid)) => {
            if args.take("client-config").is_some() {
                fail("--client-config or --socket with --uid, not both");
            }
            let uid = uid.parse().unwrap_or_else(|_| fail("--uid must be numeric"));
            if !socket.starts_with('/') {
                fail("--socket must be absolute");
            }
            Broker::new(socket, uid)
        }
        (None, None) => {
            let path = args.take("client-config").unwrap_or_else(|| CLIENT_CONFIG.to_owned());
            // Root's file on a box (the default); a sandbox's own account's in a journey.
            Broker::load(Path::new(&path), peer::euid()).unwrap_or_else(|e| fail(e))
        }
        _ => fail("--socket and --uid go together"),
    }
}

/// One member exchange, byte for byte: the broker's frames to stdout, the
/// member's to the broker. Bounded in time and size; the broker enforces the rest.
fn relay(broker: Broker) {
    let end = Instant::now() + Duration::from_secs(35);
    let mut stream = broker.connect(end).unwrap_or_else(|e| fail(e));
    wire::send(&mut stream, &json!({"op":"member-action"}), end).unwrap_or_else(|e| fail(e));
    let mut upstream = stream.try_clone().unwrap_or_else(|_| fail("socket"));
    let left = end.saturating_duration_since(Instant::now());
    let _ = stream.set_read_timeout(Some(left));
    let _ = upstream.set_write_timeout(Some(left));
    let up = std::thread::spawn(move || {
        let mut input = std::io::stdin().lock();
        let mut buf = [0u8; 8192];
        let mut total = 0usize;
        loop {
            match input.read(&mut buf) {
                Ok(0) | Err(_) => break,
                Ok(n) => {
                    total += n;
                    if total > 4 * wire::MEMBER_FRAME || upstream.write_all(&buf[..n]).is_err() {
                        break;
                    }
                }
            }
        }
        wire::zero(&mut buf);
        let _ = upstream.shutdown(Shutdown::Write);
    });
    let mut output = std::io::stdout().lock();
    let mut buf = [0u8; 8192];
    let mut total = 0usize;
    loop {
        match stream.read(&mut buf) {
            Ok(0) | Err(_) => break,
            Ok(n) => {
                total += n;
                if total > 4 * wire::MEMBER_FRAME || output.write_all(&buf[..n]).and_then(|_| output.flush()).is_err() {
                    break;
                }
            }
        }
    }
    let _ = stream.shutdown(Shutdown::Both);
    drop(up);
}

fn read_secret(source: &str) -> String {
    let mut bytes = Vec::new();
    if source == "-" {
        let _ = std::io::stdin().lock().take(4100).read_to_end(&mut bytes);
    } else {
        let mut f = std::fs::File::open(source).unwrap_or_else(|_| fail("cannot read the secret file"));
        let _ = Read::by_ref(&mut f).take(4100).read_to_end(&mut bytes);
    }
    let secret = credentials::secret_from_input(&bytes).unwrap_or_else(|e| fail(e));
    wire::zero(&mut bytes);
    secret.expose().to_owned()
}

fn main() {
    let mut argv: Vec<String> = std::env::args().skip(1).collect();
    if argv.is_empty() {
        fail("usage: mini-keys serve|relay|hello|pool|namespace ... (see the source header)");
    }
    let verb = argv.remove(0);
    let mut args = Args(argv);
    match verb.as_str() {
        "serve" => {
            let config = PathBuf::from(args.need("config"));
            args.done();
            server::serve_box(&config).unwrap_or_else(|e| fail(e));
        }
        "relay" => {
            let b = broker(&mut args);
            args.done();
            relay(b);
        }
        "hello" => {
            let b = broker(&mut args);
            args.done();
            match mini_keys::client::hello(&b) {
                Ok(v) => println!("{v}"),
                Err(r) => fail(r),
            }
        }
        "pool" => {
            let action = args.need("action");
            let provider = args.take("provider");
            let secret = args.take("secret");
            let runner = args.take("runner");
            let b = broker(&mut args);
            args.done();
            let mut request = json!({"op":"pool","action":action});
            if let Some(p) = provider {
                request["provider"] = json!(p);
            }
            if let Some(r) = runner {
                request["runner"] = json!(r);
            }
            if let Some(source) = secret {
                request["secret"] = json!(read_secret(&source));
            }
            let result = b.call(&request, Duration::from_secs(30));
            if let Some(Value::String(mut s)) = request.as_object_mut().and_then(|m| m.remove("secret")) {
                unsafe { s.as_bytes_mut().fill(0) };
            }
            match result {
                Ok(v) => println!("{}", v["result"]),
                Err(r) => fail(r),
            }
        }
        "namespace" => {
            let config_path = PathBuf::from(args.need("config"));
            let subject = args.need("subject");
            let public_key = args.need("public-key");
            args.done();
            let owner = credentials::Owner::new(&subject, &public_key).unwrap_or_else(|e| fail(e));
            let config = Config::load_for_broker(&config_path).unwrap_or_else(|e| fail(e));
            let c = config.credentials.as_ref().unwrap_or_else(|| fail("the broker config has no credential store"));
            let namespace = credentials::namespace_path(&c.root, credentials::Namespace::Owner(&owner)).unwrap_or_else(|e| fail(e));
            println!(
                "{}",
                json!({"type":"mini-credential-namespace-v1","owner":{"subject":owner.subject,"publicKey":owner.public_key},
                    "serviceConfigSha256":config.sha256,"credentialsRoot":c.root,"subjectDirectory":namespace.parent(),
                    "namespace":namespace,"serviceLockDirectory":c.root.join("_service"),"serviceUid":peer::euid()})
            );
        }
        _ => fail(format!("unknown verb {verb}")),
    }
}
