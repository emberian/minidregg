use ed25519_dalek::{Signer, SigningKey};
use serde_json::{json, Value};
use std::env;
use std::ffi::{OsStr, OsString};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Output};

const USAGE: &str = r#"mini — custody and exact-retry client for minidregg-host

usage:
  mini keygen --secret KEY --public PUBLIC
  mini bootstrap --host HOST --config OPERATOR.json --source GENESIS.json --dir DEPLOYMENT
  mini author --host HOST --config CONFIG.json --kind KIND --input INPUT.json --output OUTPUT.bin
  mini submit --host HOST --config CONFIG.json --intent INTENT.json [--intent-kind KIND] --key KEY --dir ATTEMPT
  mini query --host HOST --config CONFIG.json --intent INTENT.json [--intent-kind KIND] --key KEY --view resource|policy|capability --dir ATTEMPT
  mini retry --attempt ATTEMPT [--mode submit|lookup]

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
        Ok(self.values.swap_remove(index).1)
    }

    fn optional(&mut self, name: &str) -> Option<OsString> {
        let flag = OsString::from(format!("--{name}"));
        let index = self.values.iter().position(|(key, _)| *key == flag)?;
        Some(self.values.swap_remove(index).1)
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
    let output = Command::new(host)
        .arg(config)
        .args(arguments)
        .output()
        .map_err(|error| format!("cannot run {}: {error}", host.display()))?;
    if !output.status.success() {
        return Err(format!(
            "{} exited {}: {}",
            host.display(),
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(output)
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
        "config": utf8_path(&config)?
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
    author(host, config, intent_kind, intent, &intent_bin)?;
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
) -> Result<()> {
    create_dir(directory)?;
    copy_new(intent, &directory.join("intent.json"))?;
    let retained_config = directory.join("config.json");
    copy_new(config, &retained_config)?;
    write_manifest(directory, host, &retained_config, "submit")?;
    let signing = read_secret(key)?;
    let observed = authorize_observation(
        host,
        &retained_config,
        &directory.join("intent.json"),
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
    copy_new(intent, &directory.join("intent.json"))?;
    let retained_config = directory.join("config.json");
    copy_new(config, &retained_config)?;
    write_manifest(directory, host, &retained_config, "query")?;
    let signing = read_secret(key)?;
    let observed = authorize_observation(
        host,
        &retained_config,
        &directory.join("intent.json"),
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

fn manifest_paths(directory: &Path) -> Result<(PathBuf, PathBuf)> {
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
    Ok((host, config))
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

fn retry(directory: &Path, mode: &str) -> Result<()> {
    if !matches!(mode, "submit" | "lookup") {
        return Err("--mode must be submit or lookup".to_owned());
    }
    let call = directory.join("call.bin");
    if !call.is_file() {
        return Err(format!("attempt has no retained {}", call.display()));
    }
    let (host, config) = manifest_paths(directory)?;
    let (outcome_bin, outcome_json) = next_retry(directory)?;
    host_files(&host, &config, &[Path::new(mode), &call, &outcome_bin])?;
    let outcome = inspect(&host, &config, "outcome", &outcome_bin, &outcome_json)?;
    print_confirmed_outcome(&outcome)
}

fn run(mut args: Args) -> Result<()> {
    match args.command.to_string_lossy().as_ref() {
        "keygen" => {
            let secret = path(args.required("secret")?);
            let public = path(args.required("public")?);
            args.finish()?;
            keygen(&secret, &public)
        }
        "bootstrap" => {
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
            let key = path(args.required("key")?);
            let directory = path(args.required("dir")?);
            args.finish()?;
            submit(&host, &config, &intent, &intent_kind, &key, &directory)
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
            args.finish()?;
            let mode = mode
                .to_str()
                .ok_or_else(|| "--mode must be UTF-8".to_owned())?;
            retry(&directory, mode)
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

        retry(&directory, "submit").unwrap();
        let first = fs::read(directory.join("retry-0001.bin")).unwrap();
        retry(&directory, "lookup").unwrap();
        assert_eq!(fs::read(&call).unwrap(), [0, 1, 2, 255, 17]);
        assert_eq!(first, [0, 1, 2, 255, 17]);
        assert_eq!(fs::read(directory.join("retry-0002.bin")).unwrap(), first);
        assert!(directory.join("retry-0001.json").is_file());
        assert!(directory.join("retry-0002.json").is_file());
        fs::remove_dir_all(directory).unwrap();
    }
}
