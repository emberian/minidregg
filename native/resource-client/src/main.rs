use ed25519_dalek::{Signer, SigningKey};
use serde_json::{json, Value};
use std::env;
use std::ffi::{OsStr, OsString};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Output};
use std::sync::OnceLock;

#[cfg(unix)]
mod transport;

static SOCKET: OnceLock<PathBuf> = OnceLock::new();

const USAGE: &str = r#"mini — custody and exact-retry client for minidregg-host

usage:
  mini keygen --secret KEY --public PUBLIC
  mini profile --host HOST --config CONFIG.json [--socket SOCKET]
  mini describe --host HOST --config CONFIG.json [--socket SOCKET]
  mini bootstrap --host HOST --config OPERATOR.json --source GENESIS.json --dir DEPLOYMENT
  mini author --host HOST --config CONFIG.json --kind KIND --input INPUT.json --output OUTPUT.bin
  mini submit --host HOST --config CONFIG.json --intent INTENT.json [--intent-kind KIND] [--prepare-only true] --key KEY --dir ATTEMPT
  mini query --host HOST --config CONFIG.json --intent INTENT.json [--intent-kind KIND] --key KEY --view resource|policy|capability --dir ATTEMPT
  mini retry --attempt ATTEMPT [--mode submit|lookup] [--socket SOCKET|--direct true]
  mini export-evidence --host HOST --config CONFIG.json --call CALL.bin --output PACKAGE.bin
  mini verify-evidence --host HOST --config INDEPENDENT-PIN.json --package PACKAGE.bin --output RESULT.json
  mini serve --host HOST --config CONFIG.json --socket PRIVATE-DIR/mini.sock
  mini host-command --host HOST --config CONFIG.json --command FN-COMMAND [--arg ARG ...]
  mini consumer-poll --host HOST --config FN-POLL-CONFIG.json --socket SOCKET --dir NEW-ATTEMPT
  mini consumer-ack --host HOST --config FN-POLL-CONFIG.json --socket SOCKET --mini-transaction ID --dir NEW-ATTEMPT
  mini reply-consumer-poll --host HOST --config FN-REPLY-POLL-CONFIG.json --socket SOCKET --dir NEW-ATTEMPT
  mini reply-consumer-ack --host HOST --config FN-REPLY-POLL-CONFIG.json --socket SOCKET --mini-transaction ID --dir NEW-ATTEMPT

Add --socket PRIVATE-DIR/mini.sock to author, submit, query, retry, and other
supported host commands to use one persistent Lean host session.

The Lean host authors and decodes every semantic value. This client owns only
private-key custody, process transport, retained attempts, and exact retries.
"#;

type Result<T> = std::result::Result<T, String>;

#[derive(Debug)]
struct Args {
    command: OsString,
    values: Vec<(OsString, OsString)>,
}

impl Args {
    fn parse() -> Result<Self> {
        let mut raw = env::args_os().skip(1);
        let command = raw.next().ok_or_else(|| USAGE.to_owned())?;
        if command == OsStr::new("--help") || command == OsStr::new("-h") {
            return Err(USAGE.to_owned());
        }
        let mut values = Vec::new();
        while let Some(flag) = raw.next() {
            let rendered = flag.to_string_lossy();
            if !rendered.starts_with("--") || rendered.len() == 2 {
                return Err(format!("unexpected argument {rendered}\n\n{USAGE}"));
            }
            let value = raw
                .next()
                .ok_or_else(|| format!("missing value for {rendered}"))?;
            values.push((flag, value));
        }
        Ok(Self { command, values })
    }

    fn required(&mut self, name: &str) -> Result<OsString> {
        let flag = OsString::from(format!("--{name}"));
        let Some(index) = self.values.iter().position(|(key, _)| *key == flag) else {
            return Err(format!("missing --{name}"));
        };
        Ok(self.values.remove(index).1)
    }

    fn optional(&mut self, name: &str) -> Option<OsString> {
        let flag = OsString::from(format!("--{name}"));
        let index = self.values.iter().position(|(key, _)| *key == flag)?;
        Some(self.values.remove(index).1)
    }

    fn repeated(&mut self, name: &str) -> Vec<OsString> {
        let flag = OsString::from(format!("--{name}"));
        let mut found = Vec::new();
        self.values.retain(|(key, value)| {
            if *key == flag {
                found.push(value.clone());
                false
            } else {
                true
            }
        });
        found
    }

    fn finish(self) -> Result<()> {
        if self.values.is_empty() {
            Ok(())
        } else {
            Err(format!(
                "unknown or duplicate option {}",
                self.values[0].0.to_string_lossy()
            ))
        }
    }
}

fn path(value: OsString) -> PathBuf {
    PathBuf::from(value)
}

fn absolute(path: &Path) -> Result<PathBuf> {
    if path.is_absolute() {
        Ok(path.to_path_buf())
    } else {
        env::current_dir()
            .map(|cwd| cwd.join(path))
            .map_err(|error| format!("cannot resolve {}: {error}", path.display()))
    }
}

fn utf8_path(path: &Path) -> Result<&str> {
    path.to_str()
        .ok_or_else(|| format!("path is not valid UTF-8: {}", path.display()))
}

fn create_private(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options
        .open(path)
        .map_err(|error| format!("cannot create {}: {error}", path.display()))?;
    file.write_all(bytes)
        .and_then(|()| file.sync_all())
        .map_err(|error| format!("cannot write {}: {error}", path.display()))
}

fn create_public(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("cannot create {}: {error}", path.display()))?;
    file.write_all(bytes)
        .and_then(|()| file.sync_all())
        .map_err(|error| format!("cannot write {}: {error}", path.display()))
}

fn read_secret(path: &Path) -> Result<SigningKey> {
    let bytes = fs::read(path)
        .map_err(|error| format!("cannot read signing key {}: {error}", path.display()))?;
    let seed: [u8; 32] = bytes.try_into().map_err(|_| {
        format!(
            "signing key {} must contain exactly 32 raw bytes",
            path.display()
        )
    })?;
    Ok(SigningKey::from_bytes(&seed))
}

fn keygen(secret: &Path, public: &Path) -> Result<()> {
    if secret.exists() {
        return Err(format!("refusing to replace {}", secret.display()));
    }
    if public.exists() {
        return Err(format!("refusing to replace {}", public.display()));
    }
    let mut seed = [0u8; 32];
    File::open("/dev/urandom")
        .and_then(|mut source| source.read_exact(&mut seed))
        .map_err(|error| format!("cannot obtain operating-system randomness: {error}"))?;
    let signing = SigningKey::from_bytes(&seed);
    create_private(secret, &seed)?;
    seed.fill(0);
    if let Err(error) = create_public(public, &signing.verifying_key().to_bytes()) {
        fs::remove_file(secret).map_err(|cleanup| {
            format!(
                "{error}; also cannot remove newly-created {}: {cleanup}",
                secret.display()
            )
        })?;
        return Err(error);
    }
    println!("{}", hex(&signing.verifying_key().to_bytes()));
    Ok(())
}

fn process(host: &Path, config: &Path, arguments: &[&OsStr]) -> Result<Output> {
    if let Some(socket) = SOCKET.get() {
        return socket_process(socket, config, arguments);
    }
    let output = Command::new(host)
        .arg(config)
        .args(arguments)
        .output()
        .map_err(|error| format!("cannot run {}: {error}", host.display()))?;
    if !output.status.success() {
        return Err(format!(
            "{} exited {}; request status uncertain: {}",
            host.display(),
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(output)
}

#[cfg(unix)]
fn socket_process(socket: &Path, config: &Path, arguments: &[&OsStr]) -> Result<Output> {
    let command = arguments
        .first()
        .and_then(|s| s.to_str())
        .ok_or("missing host command")?;
    let read = |index: usize| -> Result<Vec<u8>> {
        let path = arguments.get(index).ok_or("missing host input path")?;
        let path = Path::new(path);
        let mut file = File::open(path)
            .map_err(|e| format!("cannot read host input {}: {e}", path.display()))?;
        let mut bytes = Vec::new();
        Read::by_ref(&mut file)
            .take((transport::HOST_MAX_FRAME + 1) as u64)
            .read_to_end(&mut bytes)
            .map_err(|e| format!("cannot read host input {}: {e}", path.display()))?;
        if bytes.len() > transport::HOST_MAX_FRAME {
            return Err(format!(
                "host input {} exceeds session frame bound",
                path.display()
            ));
        }
        Ok(bytes)
    };
    let pair = |first: Vec<u8>, second: Vec<u8>| -> Result<Vec<u8>> {
        let length: u32 = first.len().try_into().map_err(|_| "host input too large")?;
        let mut bytes = length.to_le_bytes().to_vec();
        bytes.extend(first);
        bytes.extend(second);
        Ok(bytes)
    };
    let kind_payload = |kind: &OsStr, input: Vec<u8>| -> Result<Vec<u8>> {
        let kind = kind.to_str().ok_or("host kind must be UTF-8")?.as_bytes();
        let length: u16 = kind.len().try_into().map_err(|_| "host kind too long")?;
        let mut bytes = length.to_le_bytes().to_vec();
        bytes.extend(kind);
        bytes.extend(input);
        Ok(bytes)
    };
    let (operation, payload, destination) = match command {
        "describe" if arguments.len() == 1 => (0, vec![], None),
        "profile" if arguments.len() == 1 => (6, vec![], None),
        "prepare" if arguments.len() == 3 => (1, read(1)?, Some(arguments[2])),
        "submit" if arguments.len() == 3 => (2, read(1)?, Some(arguments[2])),
        "lookup" if arguments.len() == 3 => (3, read(1)?, Some(arguments[2])),
        "challenge" if arguments.len() == 3 => (4, read(1)?, Some(arguments[2])),
        "query" if arguments.len() == 3 => (5, read(1)?, Some(arguments[2])),
        "author" if arguments.len() == 4 => {
            (7, kind_payload(arguments[1], read(2)?)?, Some(arguments[3]))
        }
        "inspect" if arguments.len() == 4 => {
            (8, kind_payload(arguments[1], read(2)?)?, Some(arguments[3]))
        }
        "signatures" if arguments.len() == 3 => (9, read(1)?, Some(arguments[2])),
        "observe-assemble" if arguments.len() == 4 => {
            (10, pair(read(1)?, read(2)?)?, Some(arguments[3]))
        }
        "assemble" if arguments.len() == 4 => (11, pair(read(1)?, read(2)?)?, Some(arguments[3])),
        _ => {
            return Err(format!(
                "{command} is not available through the persistent host session"
            ))
        }
    };
    let reply = transport::invoke(socket, config, operation, &payload)?;
    if reply[0] == 255 {
        return Err(format!(
            "host refused {command}; encoded refusal: {}",
            hex(&reply[1..])
        ));
    }
    if let Some(destination) = destination {
        write_new(Path::new(destination), &reply[1..])?;
    }
    use std::os::unix::process::ExitStatusExt;
    Ok(Output {
        status: std::process::ExitStatus::from_raw(0),
        stdout: reply[1..].to_vec(),
        stderr: Vec::new(),
    })
}

#[cfg(not(unix))]
fn socket_process(_socket: &Path, _config: &Path, _arguments: &[&OsStr]) -> Result<Output> {
    Err("persistent host sessions require Unix sockets".to_owned())
}

fn host_files(host: &Path, config: &Path, arguments: &[&Path]) -> Result<()> {
    let args: Vec<&OsStr> = arguments.iter().map(|path| path.as_os_str()).collect();
    process(host, config, &args).map(|_| ())
}

fn host_words(host: &Path, config: &Path, arguments: &[&str]) -> Result<Output> {
    let args: Vec<&OsStr> = arguments.iter().map(OsStr::new).collect();
    process(host, config, &args)
}

fn create_dir(path: &Path) -> Result<()> {
    fs::create_dir(path).map_err(|error| format!("cannot create {}: {error}", path.display()))
}

fn copy_new(source: &Path, destination: &Path) -> Result<()> {
    let mut input =
        File::open(source).map_err(|error| format!("cannot open {}: {error}", source.display()))?;
    let mut output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(destination)
        .map_err(|error| format!("cannot create {}: {error}", destination.display()))?;
    io::copy(&mut input, &mut output)
        .and_then(|_| output.sync_all())
        .map_err(|error| {
            format!(
                "cannot copy {} to {}: {error}",
                source.display(),
                destination.display()
            )
        })
}

fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
    create_public(path, bytes)
}

fn bootstrap(host: &Path, config: &Path, source: &Path, directory: &Path) -> Result<()> {
    create_dir(directory)?;
    let source_copy = directory.join("genesis-source.json");
    let operator_copy = directory.join("operator-config.json");
    let source_bin = directory.join("genesis-source.bin");
    let genesis_bin = directory.join("genesis.bin");
    let pinned = directory.join("pinned-config.json");
    let profile = directory.join("profile.json");
    copy_new(source, &source_copy)?;
    copy_new(config, &operator_copy)?;
    let output = host_words(host, &operator_copy, &["profile"])?;
    write_new(&profile, &output.stdout)?;
    process(
        host,
        &operator_copy,
        &[
            OsStr::new("author"),
            OsStr::new("genesis"),
            source_copy.as_os_str(),
            source_bin.as_os_str(),
        ],
    )?;
    process(
        host,
        &operator_copy,
        &[
            OsStr::new("genesis"),
            source_bin.as_os_str(),
            genesis_bin.as_os_str(),
            pinned.as_os_str(),
        ],
    )?;
    host_files(host, &pinned, &[Path::new("bootstrap"), &genesis_bin])?;
    let description = process(host, &pinned, &[OsStr::new("describe")])?;
    write_new(&directory.join("description.json"), &description.stdout)?;
    println!("{}", pinned.display());
    Ok(())
}

fn author(host: &Path, config: &Path, kind: &OsStr, input: &Path, output: &Path) -> Result<()> {
    if output.exists() {
        return Err(format!("refusing to replace {}", output.display()));
    }
    process(
        host,
        config,
        &[
            OsStr::new("author"),
            kind,
            input.as_os_str(),
            output.as_os_str(),
        ],
    )?;
    Ok(())
}

fn inspect(host: &Path, config: &Path, kind: &str, input: &Path, output: &Path) -> Result<Value> {
    process(
        host,
        config,
        &[
            OsStr::new("inspect"),
            OsStr::new(kind),
            input.as_os_str(),
            output.as_os_str(),
        ],
    )?;
    let bytes =
        fs::read(output).map_err(|error| format!("cannot read {}: {error}", output.display()))?;
    serde_json::from_slice(&bytes)
        .map_err(|error| format!("invalid host JSON {}: {error}", output.display()))
}

fn decode_hex(value: &str) -> Result<Vec<u8>> {
    if !value.len().is_multiple_of(2) {
        return Err("host emitted odd-length header hex".to_owned());
    }
    value
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            std::str::from_utf8(pair)
                .ok()
                .and_then(|text| u8::from_str_radix(text, 16).ok())
                .ok_or_else(|| "host emitted non-hex header".to_owned())
        })
        .collect()
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push(DIGITS[(byte >> 4) as usize] as char);
        output.push(DIGITS[(byte & 15) as usize] as char);
    }
    output
}

fn challenge_headers(value: &Value) -> Result<Vec<Vec<u8>>> {
    let headers = value
        .get("headers")
        .and_then(Value::as_array)
        .ok_or_else(|| "host challenge JSON has no headers array".to_owned())?;
    headers
        .iter()
        .map(|header| {
            header
                .as_str()
                .ok_or_else(|| "host challenge header is not a string".to_owned())
                .and_then(decode_hex)
        })
        .collect()
}

fn plan_headers(value: &Value) -> Result<Vec<Vec<u8>>> {
    let slots = value
        .get("slots")
        .and_then(Value::as_array)
        .ok_or_else(|| "host plan JSON has no slots array".to_owned())?;
    slots
        .iter()
        .map(|slot| {
            slot.get("header")
                .and_then(Value::as_str)
                .ok_or_else(|| "host plan slot has no header string".to_owned())
                .and_then(decode_hex)
        })
        .collect()
}

fn sign_headers(signing: &SigningKey, headers: &[Vec<u8>]) -> Value {
    Value::Array(
        headers
            .iter()
            .map(|header| Value::String(hex(&signing.sign(header).to_bytes())))
            .collect(),
    )
}

fn write_json_new(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value)
        .map_err(|error| format!("cannot render {}: {error}", path.display()))?;
    bytes.push(b'\n');
    write_new(path, &bytes)
}

fn print_json(value: &Value) -> Result<()> {
    let rendered = serde_json::to_string_pretty(value)
        .map_err(|error| format!("cannot render host JSON: {error}"))?;
    println!("{rendered}");
    Ok(())
}

fn print_confirmed_outcome(value: &Value) -> Result<()> {
    print_json(value)?;
    match value.get("type").and_then(Value::as_str) {
        Some("confirmed") => Ok(()),
        Some(kind) => Err(format!(
            "host returned {kind}; exact outcome evidence was retained"
        )),
        None => Err("host outcome JSON has no type; exact evidence was retained".to_owned()),
    }
}

fn encode_signatures(
    host: &Path,
    config: &Path,
    signing: &SigningKey,
    headers: Vec<Vec<u8>>,
    json_path: &Path,
    bin_path: &Path,
) -> Result<()> {
    write_json_new(json_path, &sign_headers(signing, &headers))?;
    process(
        host,
        config,
        &[
            OsStr::new("signatures"),
            json_path.as_os_str(),
            bin_path.as_os_str(),
        ],
    )?;
    Ok(())
}

fn write_manifest(directory: &Path, host: &Path, config: &Path, operation: &str) -> Result<()> {
    let host = absolute(host)?;
    let config = absolute(config)?;
    let manifest = json!({
        "format": "minidregg-resource-client-attempt-v1",
        "operation": operation,
        "host": utf8_path(&host)?,
        "config": utf8_path(&config)?,
        "socket": SOCKET.get().map(|socket| absolute(socket)).transpose()?.map(|socket| socket.to_string_lossy().into_owned())
    });
    write_json_new(&directory.join("attempt.json"), &manifest)
}

struct Observed {
    signed: PathBuf,
}

fn authorize_observation(
    host: &Path,
    config: &Path,
    intent: &Path,
    intent_kind: &OsStr,
    signing: &SigningKey,
    directory: &Path,
) -> Result<Observed> {
    let intent_bin = directory.join("intent.bin");
    let challenge_bin = directory.join("challenge.bin");
    let challenge_json = directory.join("challenge.json");
    let signatures_json = directory.join("observation-signatures.json");
    let signatures_bin = directory.join("observation-signatures.bin");
    let signed = directory.join("signed-observation.bin");
    if intent_kind == OsStr::new("binary") {
        copy_new(intent, &intent_bin)?;
    } else {
        author(host, config, intent_kind, intent, &intent_bin)?;
    }
    host_files(
        host,
        config,
        &[Path::new("challenge"), &intent_bin, &challenge_bin],
    )?;
    let presentation = inspect(host, config, "challenge", &challenge_bin, &challenge_json)?;
    encode_signatures(
        host,
        config,
        signing,
        challenge_headers(&presentation)?,
        &signatures_json,
        &signatures_bin,
    )?;
    host_files(
        host,
        config,
        &[
            Path::new("observe-assemble"),
            &challenge_bin,
            &signatures_bin,
            &signed,
        ],
    )?;
    Ok(Observed { signed })
}

fn submit(
    host: &Path,
    config: &Path,
    intent: &Path,
    intent_kind: &OsStr,
    key: &Path,
    directory: &Path,
    prepare_only: bool,
) -> Result<()> {
    create_dir(directory)?;
    let retained_intent = directory.join(if intent_kind == OsStr::new("binary") {
        "intent-source.bin"
    } else {
        "intent.json"
    });
    copy_new(intent, &retained_intent)?;
    let retained_config = directory.join("config.json");
    copy_new(config, &retained_config)?;
    write_manifest(directory, host, &retained_config, "submit")?;
    let signing = read_secret(key)?;
    let observed = authorize_observation(
        host,
        &retained_config,
        &retained_intent,
        intent_kind,
        &signing,
        directory,
    )?;
    let plan_bin = directory.join("plan.bin");
    let plan_json = directory.join("plan.json");
    let signatures_json = directory.join("transaction-signatures.json");
    let signatures_bin = directory.join("transaction-signatures.bin");
    let call = directory.join("call.bin");
    host_files(
        host,
        &retained_config,
        &[Path::new("prepare"), &observed.signed, &plan_bin],
    )?;
    let presentation = inspect(host, &retained_config, "plan", &plan_bin, &plan_json)?;
    encode_signatures(
        host,
        &retained_config,
        &signing,
        plan_headers(&presentation)?,
        &signatures_json,
        &signatures_bin,
    )?;
    host_files(
        host,
        &retained_config,
        &[Path::new("assemble"), &plan_bin, &signatures_bin, &call],
    )?;
    if prepare_only {
        return Ok(());
    }
    let outcome_bin = directory.join("outcome.bin");
    let outcome_json = directory.join("outcome.json");
    host_files(
        host,
        &retained_config,
        &[Path::new("submit"), &call, &outcome_bin],
    )?;
    let outcome = inspect(
        host,
        &retained_config,
        "outcome",
        &outcome_bin,
        &outcome_json,
    )?;
    print_confirmed_outcome(&outcome)
}

fn query(
    host: &Path,
    config: &Path,
    intent: &Path,
    intent_kind: &OsStr,
    key: &Path,
    view: &str,
    directory: &Path,
) -> Result<()> {
    if !matches!(view, "resource" | "policy" | "capability") {
        return Err("--view must be resource, policy, or capability".to_owned());
    }
    create_dir(directory)?;
    let retained_intent = directory.join(if intent_kind == OsStr::new("binary") {
        "intent-source.bin"
    } else {
        "intent.json"
    });
    copy_new(intent, &retained_intent)?;
    let retained_config = directory.join("config.json");
    copy_new(config, &retained_config)?;
    write_manifest(directory, host, &retained_config, "query")?;
    let signing = read_secret(key)?;
    let observed = authorize_observation(
        host,
        &retained_config,
        &retained_intent,
        intent_kind,
        &signing,
        directory,
    )?;
    let view_bin = directory.join("view.bin");
    let view_json = directory.join("view.json");
    host_files(
        host,
        &retained_config,
        &[Path::new("query"), &observed.signed, &view_bin],
    )?;
    let presentation = inspect(
        host,
        &retained_config,
        &format!("view-{view}"),
        &view_bin,
        &view_json,
    )?;
    print_json(&presentation)
}

fn manifest_paths(directory: &Path) -> Result<(PathBuf, PathBuf, Option<PathBuf>)> {
    let path = directory.join("attempt.json");
    let bytes =
        fs::read(&path).map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    let value: Value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("invalid {}: {error}", path.display()))?;
    if value.get("format").and_then(Value::as_str) != Some("minidregg-resource-client-attempt-v1") {
        return Err(format!("unsupported attempt manifest {}", path.display()));
    }
    let host = value
        .get("host")
        .and_then(Value::as_str)
        .map(PathBuf::from)
        .ok_or_else(|| "attempt manifest has no host path".to_owned())?;
    let config = value
        .get("config")
        .and_then(Value::as_str)
        .map(PathBuf::from)
        .ok_or_else(|| "attempt manifest has no config path".to_owned())?;
    let socket = value
        .get("socket")
        .and_then(Value::as_str)
        .map(PathBuf::from);
    Ok((host, config, socket))
}

fn next_retry(directory: &Path) -> Result<(PathBuf, PathBuf)> {
    for index in 1..=9999 {
        let binary = directory.join(format!("retry-{index:04}.bin"));
        let json = directory.join(format!("retry-{index:04}.json"));
        if !binary.exists() && !json.exists() {
            return Ok((binary, json));
        }
    }
    Err("attempt has exhausted retry evidence names".to_owned())
}

fn retry(directory: &Path, mode: &str, direct: bool) -> Result<()> {
    if !matches!(mode, "submit" | "lookup") {
        return Err("--mode must be submit or lookup".to_owned());
    }
    let call = directory.join("call.bin");
    if !call.is_file() {
        return Err(format!("attempt has no retained {}", call.display()));
    }
    let (host, config, socket) = manifest_paths(directory)?;
    if !direct && SOCKET.get().is_none() {
        if let Some(socket) = socket {
            let _ = SOCKET.set(socket);
        }
    }
    let (outcome_bin, outcome_json) = next_retry(directory)?;
    host_files(&host, &config, &[Path::new(mode), &call, &outcome_bin])?;
    let outcome = inspect(&host, &config, "outcome", &outcome_bin, &outcome_json)?;
    print_confirmed_outcome(&outcome)
}

fn host_command(host: &Path, config: &Path, command: &OsStr, arguments: &[OsString]) -> Result<()> {
    let word = command.to_str().ok_or("host command must be UTF-8")?;
    if !matches!(
        word,
        "portable-verify-fn"
            | "consumer-verify-poll-files"
            | "portable-consumer-decide"
            | "poll-consumer-decide"
            | "consumer-poll-decide"
            | "consumer-export-inbox"
            | "consumer-export-poll"
            | "consumer-ack-poll"
            | "reply-consumer-poll-decide"
            | "reply-consumer-export-result"
            | "reply-consumer-ack-poll"
            | "consumer-export-reply"
            | "consumer-stage-reply-plan"
            | "consumer-stage-reply-sign"
            | "consumer-decide-test"
    ) {
        return Err(format!("unsupported fn consumer command {word}"));
    }
    if SOCKET.get().is_some() {
        return Err("fn consumer file commands require direct Host/Main CLI until a typed session opcode exists".to_owned());
    }
    let mut all = Vec::with_capacity(arguments.len() + 1);
    all.push(command);
    all.extend(arguments.iter().map(OsString::as_os_str));
    let output = process(host, config, &all)?;
    io::stdout()
        .write_all(&output.stdout)
        .map_err(|e| format!("cannot print host output: {e}"))
}

#[cfg(unix)]
#[derive(Clone, Copy)]
struct ConsumerRoute {
    poll_command: &'static str,
    ack_command: &'static str,
    poll_opcode: u8,
    ack_opcode: u8,
    poll_type: &'static str,
    ack_type: &'static str,
    reply: bool,
}

#[cfg(unix)]
const B_CONSUMER: ConsumerRoute = ConsumerRoute {
    poll_command: "consumer-poll",
    ack_command: "consumer-ack",
    poll_opcode: 12,
    ack_opcode: 13,
    poll_type: "fn-consumer-poll-session-v1",
    ack_type: "fn-consumer-ack-session-v1",
    reply: false,
};

#[cfg(unix)]
const A_REPLY_CONSUMER: ConsumerRoute = ConsumerRoute {
    poll_command: "reply-consumer-poll",
    ack_command: "reply-consumer-ack",
    poll_opcode: 14,
    ack_opcode: 15,
    poll_type: "fn-a-reply-poll-session-v1",
    ack_type: "fn-a-reply-ack-session-v1",
    reply: true,
};

#[cfg(unix)]
fn historical_without_intent(value: &Value, route: ConsumerRoute) -> bool {
    if route.reply {
        matches!(
            value.pointer("/decision/decision").and_then(Value::as_str),
            Some("repeated" | "conflict-recorded")
        )
    } else {
        matches!(
            value
                .pointer("/decision/decision/type")
                .and_then(Value::as_str),
            Some(
                "historical-repeat"
                    | "historical-carrier-variation-evidence"
                    | "historical-conflict-evidence"
            )
        )
    }
}

#[cfg(unix)]
fn private_consumer_attempt(
    host: &Path,
    config: &Path,
    directory: &Path,
    operation: &str,
) -> Result<PathBuf> {
    use std::os::unix::fs::DirBuilderExt;
    fs::DirBuilder::new()
        .mode(0o700)
        .create(directory)
        .map_err(|e| {
            format!(
                "cannot create private consumer attempt {}: {e}",
                directory.display()
            )
        })?;
    let retained_config = directory.join("config.json");
    copy_new(config, &retained_config)?;
    write_manifest(directory, host, &retained_config, operation)?;
    Ok(retained_config)
}

#[cfg(unix)]
fn consumer_poll(host: &Path, config: &Path, directory: &Path, route: ConsumerRoute) -> Result<()> {
    let socket = SOCKET.get().ok_or("consumer poll requires --socket")?;
    let retained_config = private_consumer_attempt(host, config, directory, route.poll_command)?;
    let frame = transport::invoke(socket, &retained_config, route.poll_opcode, &[])?;
    write_new(&directory.join("reply.frame"), &frame)?;
    if frame[0] == 255 {
        return Err(format!(
            "host refused {}; complete encoded reply retained in {}",
            route.poll_command,
            directory.join("reply.frame").display()
        ));
    }
    let value: Value = serde_json::from_slice(&frame[1..])
        .map_err(|e| format!("invalid fn consumer host JSON; complete reply retained: {e}"))?;
    write_new(&directory.join("decision.json"), &frame[1..])?;
    if value.get("type").and_then(Value::as_str) != Some(route.poll_type) {
        return Err("unexpected fn consumer host reply type; complete reply retained".to_owned());
    }
    let status = value
        .get("status")
        .and_then(Value::as_str)
        .ok_or("fn consumer reply lacks status; complete reply retained")?;
    let intent_hex = value
        .get("intentHex")
        .and_then(Value::as_str)
        .ok_or("fn consumer reply lacks intentHex; complete reply retained")?;
    let intent = decode_hex(intent_hex)?;
    if hex(&intent) != intent_hex {
        return Err(
            "fn consumer intentHex is not canonical lowercase; complete reply retained".to_owned(),
        );
    }
    match status {
        "accepted-decision" => {
            if intent.is_empty() {
                if !historical_without_intent(&value, route) {
                    return Err("fn consumer accepted without an intent or historical decision; complete reply retained".to_owned());
                }
            } else {
                write_new(&directory.join("intent.bin"), &intent)?;
            }
            print_json(&value)
        }
        "idle"
            if !route.reply
                && intent.is_empty()
                && value.pointer("/decision/type").and_then(Value::as_str)
                    == Some("fn-empty-page-idle-v1") =>
        {
            print_json(&value)
        }
        "skip-decision"
            if !route.reply
                && value.pointer("/decision/type").and_then(Value::as_str)
                    == Some("fn-empty-page-progress-decision-v1") =>
        {
            match value.pointer("/decision/decision").and_then(Value::as_str) {
                Some("proposed-fresh") if !intent.is_empty() => {
                    write_new(&directory.join("intent.bin"), &intent)?;
                    print_json(&value)
                }
                Some("repeated") if intent.is_empty() => print_json(&value),
                _ => Err(
                    "inconsistent fn empty-page decision and intent; complete reply retained"
                        .to_owned(),
                ),
            }
        }
        "refused" if intent.is_empty() => {
            print_json(&value)?;
            Err("fn consumer refused; complete decision retained".to_owned())
        }
        _ => Err("inconsistent fn consumer status and intent; complete reply retained".to_owned()),
    }
}

#[cfg(unix)]
fn consumer_ack(
    host: &Path,
    config: &Path,
    transaction: &str,
    directory: &Path,
    route: ConsumerRoute,
) -> Result<()> {
    let socket = SOCKET.get().ok_or("consumer ack requires --socket")?;
    let bytes = transaction.as_bytes();
    if bytes.is_empty()
        || bytes.len() > 80
        || bytes.iter().any(|b| !b.is_ascii_digit())
        || (bytes.len() > 1 && bytes[0] == b'0')
    {
        return Err("--mini-transaction must be canonical decimal (1–80 bytes)".to_owned());
    }
    let retained_config = private_consumer_attempt(host, config, directory, route.ack_command)?;
    write_new(&directory.join("transaction-id.txt"), bytes)?;
    let frame = transport::invoke(socket, &retained_config, route.ack_opcode, bytes)?;
    write_new(&directory.join("reply.frame"), &frame)?;
    if frame[0] == 255 {
        return Err(format!(
            "host refused {}; complete encoded reply retained in {}",
            route.ack_command,
            directory.join("reply.frame").display()
        ));
    }
    let value: Value = serde_json::from_slice(&frame[1..])
        .map_err(|e| format!("invalid fn ack host JSON; complete reply retained: {e}"))?;
    write_new(&directory.join("ack.json"), &frame[1..])?;
    if value.get("type").and_then(Value::as_str) != Some(route.ack_type)
        || value.get("miniTransactionId").and_then(Value::as_str) != Some(transaction)
    {
        return Err("fn ack reply identity mismatch; complete reply retained".to_owned());
    }
    print_json(&value)?;
    match value.get("fnAck").and_then(Value::as_str) {
        Some("durable-accepted") => Ok(()),
        Some("refused" | "uncertain" | "transport-fault") => {
            Err("fn ack incomplete; complete reply retained for reconciliation".to_owned())
        }
        _ => Err("fn ack reply lacks valid status; complete reply retained".to_owned()),
    }
}

fn run(mut args: Args) -> Result<()> {
    if let Some(socket) = args.optional("socket") {
        let _ = SOCKET.set(path(socket));
    }
    match args.command.to_string_lossy().as_ref() {
        "serve" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            args.finish()?;
            let socket = SOCKET.get().ok_or("serve requires --socket")?;
            #[cfg(unix)]
            {
                transport::serve(socket, &host, &config)
            }
            #[cfg(not(unix))]
            {
                Err("persistent host sessions require Unix sockets".to_owned())
            }
        }
        "host-command" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let command = args.required("command")?;
            let arguments = args.repeated("arg");
            args.finish()?;
            host_command(&host, &config, &command, &arguments)
        }
        "consumer-poll" | "reply-consumer-poll" => {
            let reply = args.command == OsStr::new("reply-consumer-poll");
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            #[cfg(unix)]
            {
                consumer_poll(
                    &host,
                    &config,
                    &directory,
                    if reply { A_REPLY_CONSUMER } else { B_CONSUMER },
                )
            }
            #[cfg(not(unix))]
            {
                Err("persistent host sessions require Unix sockets".to_owned())
            }
        }
        "consumer-ack" | "reply-consumer-ack" => {
            let reply = args.command == OsStr::new("reply-consumer-ack");
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let transaction = args.required("mini-transaction")?;
            let directory = path(args.required("dir")?);
            args.finish()?;
            let transaction = transaction
                .to_str()
                .ok_or("--mini-transaction must be UTF-8")?;
            #[cfg(unix)]
            {
                consumer_ack(
                    &host,
                    &config,
                    transaction,
                    &directory,
                    if reply { A_REPLY_CONSUMER } else { B_CONSUMER },
                )
            }
            #[cfg(not(unix))]
            {
                Err("persistent host sessions require Unix sockets".to_owned())
            }
        }
        "profile" | "describe" => {
            let command = args.command.clone();
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            args.finish()?;
            let output = process(&host, &config, &[command.as_os_str()])?;
            io::stdout()
                .write_all(&output.stdout)
                .map_err(|e| format!("cannot print host output: {e}"))
        }
        "keygen" => {
            if SOCKET.get().is_some() {
                return Err("keygen does not use a host socket".to_owned());
            }
            let secret = path(args.required("secret")?);
            let public = path(args.required("public")?);
            args.finish()?;
            keygen(&secret, &public)
        }
        "bootstrap" => {
            if SOCKET.get().is_some() {
                return Err("bootstrap requires direct Host/Main CLI".to_owned());
            }
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let source = path(args.required("source")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            bootstrap(&host, &config, &source, &directory)
        }
        "author" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let kind = args.required("kind")?;
            let input = path(args.required("input")?);
            let output = path(args.required("output")?);
            args.finish()?;
            author(&host, &config, &kind, &input, &output)
        }
        "submit" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let intent = path(args.required("intent")?);
            let intent_kind = args
                .optional("intent-kind")
                .unwrap_or_else(|| OsString::from("intent"));
            let prepare_only = match args.optional("prepare-only").as_deref() {
                None => false,
                Some(value) if value == OsStr::new("false") => false,
                Some(value) if value == OsStr::new("true") => true,
                _ => return Err("--prepare-only must be true or false".to_owned()),
            };
            let key = path(args.required("key")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            submit(
                &host,
                &config,
                &intent,
                &intent_kind,
                &key,
                &directory,
                prepare_only,
            )
        }
        "query" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let intent = path(args.required("intent")?);
            let intent_kind = args
                .optional("intent-kind")
                .unwrap_or_else(|| OsString::from("intent"));
            let key = path(args.required("key")?);
            let view = args.required("view")?;
            let directory = path(args.required("dir")?);
            args.finish()?;
            let view = view
                .to_str()
                .ok_or_else(|| "--view must be UTF-8".to_owned())?;
            query(
                &host,
                &config,
                &intent,
                &intent_kind,
                &key,
                view,
                &directory,
            )
        }
        "retry" => {
            let directory = path(args.required("attempt")?);
            let mode = args
                .optional("mode")
                .unwrap_or_else(|| OsString::from("submit"));
            let direct = match args.optional("direct").as_deref() {
                None => false,
                Some(value) if value == OsStr::new("false") => false,
                Some(value) if value == OsStr::new("true") => true,
                _ => return Err("--direct must be true or false".to_owned()),
            };
            if direct && SOCKET.get().is_some() {
                return Err("--direct true cannot be combined with --socket".to_owned());
            }
            args.finish()?;
            let mode = mode
                .to_str()
                .ok_or_else(|| "--mode must be UTF-8".to_owned())?;
            retry(&directory, mode, direct)
        }
        "export-evidence" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let call = path(args.required("call")?);
            let output = path(args.required("output")?);
            args.finish()?;
            if output.exists() {
                return Err(format!("refusing to replace {}", output.display()));
            }
            host_files(
                &host,
                &config,
                &[Path::new("export-evidence"), &call, &output],
            )
        }
        "verify-evidence" => {
            let host = path(args.required("host")?);
            let config = path(args.required("config")?);
            let package = path(args.required("package")?);
            let output = path(args.required("output")?);
            args.finish()?;
            if output.exists() {
                return Err(format!("refusing to replace {}", output.display()));
            }
            host_files(
                &host,
                &config,
                &[Path::new("verify-evidence"), &package, &output],
            )
        }
        other => Err(format!("unknown command {other}\n\n{USAGE}")),
    }
}

fn main() -> ExitCode {
    match Args::parse().and_then(run) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) if error == USAGE => {
            print!("{error}");
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("mini: {error}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ed25519_dalek::{Verifier, VerifyingKey};
    use std::time::{SystemTime, UNIX_EPOCH};

    fn scratch(name: &str) -> PathBuf {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = env::temp_dir().join(format!("mini-{name}-{}-{unique}", std::process::id()));
        fs::create_dir(&path).unwrap();
        path
    }

    #[test]
    fn named_options_preserve_interleaved_fn_argument_order() {
        let mut args = Args {
            command: OsString::from("host-command"),
            values: [
                ("--arg", "first"),
                ("--host", "host"),
                ("--arg", "second"),
                ("--config", "config"),
                ("--command", "consumer-export-reply"),
                ("--arg", "third"),
            ]
            .into_iter()
            .map(|(key, value)| (OsString::from(key), OsString::from(value)))
            .collect(),
        };
        assert_eq!(args.required("host").unwrap(), OsStr::new("host"));
        assert_eq!(args.required("config").unwrap(), OsStr::new("config"));
        assert_eq!(
            args.required("command").unwrap(),
            OsStr::new("consumer-export-reply")
        );
        assert_eq!(
            args.repeated("arg"),
            vec!["first", "second", "third"]
                .into_iter()
                .map(OsString::from)
                .collect::<Vec<_>>()
        );
        args.finish().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn historical_fn_decisions_need_no_new_mini_intent() {
        assert!(historical_without_intent(
            &json!({"decision": {"decision": {"type": "historical-repeat"}}}),
            B_CONSUMER,
        ));
        assert!(historical_without_intent(
            &json!({"decision": {"decision": {"type": "historical-carrier-variation-evidence"}}}),
            B_CONSUMER,
        ));
        assert!(historical_without_intent(
            &json!({"decision": {"decision": "repeated"}}),
            A_REPLY_CONSUMER,
        ));
        assert!(!historical_without_intent(
            &json!({"decision": {"decision": {"type": "proposed-fresh"}}}),
            B_CONSUMER,
        ));
        assert!(!historical_without_intent(
            &json!({"decision": {"decision": "proposed-fresh"}}),
            A_REPLY_CONSUMER,
        ));
    }

    #[test]
    fn inspected_headers_are_signed_as_exact_bytes_in_order() {
        let challenge = json!({"headers": ["00ff10", "6d696e69"]});
        let headers = challenge_headers(&challenge).unwrap();
        assert_eq!(headers, [vec![0, 255, 16], b"mini".to_vec()]);

        let signing = SigningKey::from_bytes(&[27; 32]);
        let rendered = sign_headers(&signing, &headers);
        let signatures = rendered.as_array().unwrap();
        let verifying = VerifyingKey::from_bytes(&signing.verifying_key().to_bytes()).unwrap();
        for (header, signature) in headers.iter().zip(signatures) {
            let bytes: [u8; 64] = decode_hex(signature.as_str().unwrap())
                .unwrap()
                .try_into()
                .unwrap();
            verifying
                .verify(header, &ed25519_dalek::Signature::from_bytes(&bytes))
                .unwrap();
        }
    }

    #[test]
    fn plan_slots_reject_presentation_without_exact_header_strings() {
        assert!(plan_headers(&json!({"slots": [{"header": "01"}]})).is_ok());
        assert!(plan_headers(&json!({"slots": [{"header": 1}]})).is_err());
        assert!(plan_headers(&json!({"slots": [{"header": "0"}]})).is_err());
        assert!(plan_headers(&json!({"slots": [{"header": "zz"}]})).is_err());
        assert!(print_confirmed_outcome(&json!({"type": "confirmed"})).is_ok());
        assert!(print_confirmed_outcome(&json!({"type": "refused"})).is_err());
    }

    #[test]
    fn key_generation_refuses_to_clobber_existing_custody_files() {
        let directory = scratch("key-no-clobber");
        let secret = directory.join("signer.key");
        let public = directory.join("signer.pub");
        fs::write(&secret, b"existing-secret").unwrap();
        fs::write(&public, b"existing-public").unwrap();

        assert!(keygen(&secret, &public).is_err());
        assert_eq!(fs::read(&secret).unwrap(), b"existing-secret");
        assert_eq!(fs::read(&public).unwrap(), b"existing-public");
        fs::remove_file(&secret).unwrap();
        assert!(keygen(&secret, &public).is_err());
        assert!(!secret.exists());
        assert_eq!(fs::read(&public).unwrap(), b"existing-public");

        let source = directory.join("source");
        fs::write(&source, b"replacement").unwrap();
        assert!(copy_new(&source, &public).is_err());
        assert_eq!(fs::read(&public).unwrap(), b"existing-public");
        fs::remove_dir_all(directory).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn retry_reuses_retained_call_and_never_replaces_prior_evidence() {
        use std::os::unix::fs::PermissionsExt;

        let directory = scratch("exact-retry");
        let host = directory.join("fake-host.sh");
        let config = directory.join("config.json");
        let call = directory.join("call.bin");
        fs::write(
            &host,
            b"#!/bin/sh\nif [ \"$2\" = inspect ]; then printf '{\"type\":\"confirmed\"}' >\"$5\"; else cp \"$3\" \"$4\"; fi\n",
        )
        .unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        fs::write(&config, b"{}").unwrap();
        fs::write(&call, [0, 1, 2, 255, 17]).unwrap();
        write_json_new(
            &directory.join("attempt.json"),
            &json!({
                "format": "minidregg-resource-client-attempt-v1",
                "operation": "submit",
                "host": host,
                "config": config
            }),
        )
        .unwrap();

        retry(&directory, "submit", false).unwrap();
        let first = fs::read(directory.join("retry-0001.bin")).unwrap();
        retry(&directory, "lookup", false).unwrap();
        assert_eq!(fs::read(&call).unwrap(), [0, 1, 2, 255, 17]);
        assert_eq!(first, [0, 1, 2, 255, 17]);
        assert_eq!(fs::read(directory.join("retry-0002.bin")).unwrap(), first);
        assert!(directory.join("retry-0001.json").is_file());
        assert!(directory.join("retry-0002.json").is_file());
        fs::remove_dir_all(directory).unwrap();
    }
}
