//! The byte control of the signing path. `mini submit` is run, in a worker process, against a
//! recording stand-in for the local Host (its storeless `codec` loop and its one-shot verbs) and
//! for the local consent provider. Every frame and every one-shot request is logged as bytes,
//! followed by the attempt directory's retained files. The log must equal
//! `tests/fixtures/signing-path.wire`, written once from the client before the signing path moved
//! into `mini_sdk::flow` (`MINI_WIRE_REGEN=1` rewrites it): the move changes no byte on any wire
//! and no byte of custody.
use super::*;
use std::os::unix::fs::PermissionsExt;

/// The Host stand-in. `$2 = codec`: the storeless frame loop, which answers op 8 (`inspect`)
/// with a JSON presentation of the kind (a confirmed receipt for `outcome`) and every other frame
/// with a checksum of the request. Otherwise a one-shot verb `HOST CONFIG VERB IN... OUT`: it logs
/// the verb and its inputs' bytes and writes a checksum of them to OUT.
const HOST: &str = r#"#!/bin/sh
D=DIR
if [ "$2" = codec ]; then
  while :; do
    n=$(dd bs=1 count=4 2>/dev/null | od -An -tu4 | tr -d ' \n')
    [ -n "$n" ] || exit 0
    dd bs=1 count="$n" of="$D/cf" 2>/dev/null
    op=$(od -An -tu1 -N1 "$D/cf" | tr -d ' \n')
    { printf 'codec %s ' "$op"; od -An -tx1 -v "$D/cf" | tr -d ' \n'; echo; } >> "$D/wire"
    if [ "$op" = 8 ]; then
      k=$(od -An -tu2 -j1 -N2 "$D/cf" | tr -d ' \n')
      kind=$(dd if="$D/cf" bs=1 skip=3 count="$k" 2>/dev/null)
      if [ "$kind" = outcome ]; then
        printf '%s' '{"type":"confirmed","confirmation":"installed","transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"}' > "$D/cb"
      else
        printf '{"kind":"%s"}' "$kind" > "$D/cb"
      fi
    else
      printf 'C%s-%s' "$op" "$(cksum < "$D/cf" | cut -d' ' -f1)" > "$D/cb"
    fi
    m=$(( $(wc -c < "$D/cb") + 1 ))
    printf "$(printf '\\%03o\\%03o\\%03o\\%03o\\%03o' $((m%256)) $((m/256%256)) $((m/65536%256)) 0 "$op")"
    cat "$D/cb"
  done
fi
verb=$2; shift 2
: > "$D/oi"
printf 'oneshot %s' "$verb" >> "$D/wire"
while [ $# -gt 1 ]; do
  printf ' ' >> "$D/wire"; od -An -tx1 -v "$1" | tr -d ' \n' >> "$D/wire"; cat "$1" >> "$D/oi"; shift
done
echo >> "$D/wire"
printf 'O-%s-%s' "$verb" "$(cksum < "$D/oi" | cut -d' ' -f1)" > "$1"
"#;

/// The consent provider stand-in (`CONSENT SETTINGS stdio`): logs each frame; answers 220 with
/// the retained intent (the first pair element), 221 and 222 with two headers, 229 with an anchor.
const CONSENT: &str = r#"#!/bin/sh
D=DIR
while :; do
  n=$(dd bs=1 count=4 2>/dev/null | od -An -tu4 | tr -d ' \n')
  [ -n "$n" ] || exit 0
  dd bs=1 count="$n" of="$D/pf" 2>/dev/null
  op=$(od -An -tu1 -N1 "$D/pf" | tr -d ' \n')
  { printf 'consent %s ' "$op"; od -An -tx1 -v "$D/pf" | tr -d ' \n'; echo; } >> "$D/wire"
  case "$op" in
    220) l=$(od -An -tu4 -j1 -N4 "$D/pf" | tr -d ' \n'); dd if="$D/pf" bs=1 skip=5 count="$l" of="$D/pb" 2>/dev/null ;;
    221) printf '["c1%s","c2"]' "$(cksum < "$D/pf" | cut -d' ' -f1)" > "$D/pb" ;;
    222) printf '["d1%s","d2"]' "$(cksum < "$D/pf" | cut -d' ' -f1)" > "$D/pb" ;;
    229) printf 'ANCHOR' > "$D/pb" ;;
    *) : > "$D/pb" ;;
  esac
  m=$(( $(wc -c < "$D/pb") + 1 ))
  printf "$(printf '\\%03o\\%03o\\%03o\\%03o\\%03o' $((m%256)) $((m/256%256)) $((m/65536%256)) 0 "$op")"
  cat "$D/pb"
done
"#;

fn stand_in(dir: &Path, name: &str, body: &str) -> PathBuf {
    let path = dir.join(name);
    fs::write(&path, body.replace("DIR", &dir.display().to_string())).unwrap();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
    path
}

/// The retained files of the attempt, by name and bytes. `attempt.json` names this run's paths,
/// so only its keys are logged.
fn custody_listing(attempt: &Path) -> String {
    let mut names: Vec<_> = fs::read_dir(attempt).unwrap().map(|e| e.unwrap().file_name().into_string().unwrap()).collect();
    names.sort();
    let mut out = String::new();
    for name in names {
        let bytes = fs::read(attempt.join(&name)).unwrap();
        if name == "attempt.json" {
            let value: Value = serde_json::from_slice(&bytes).unwrap();
            let mut keys: Vec<_> = value.as_object().unwrap().keys().cloned().collect();
            keys.sort();
            out.push_str(&format!("custody {name} keys {}\n", keys.join(",")));
        } else {
            out.push_str(&format!("custody {name} {}\n", hex(&bytes)));
        }
    }
    out
}

#[test]
#[ignore = "worker for the_signing_path_wire_bytes_are_pinned"]
fn signing_wire_worker() {
    let dir = PathBuf::from(std::env::var_os("MINI_WIRE_DIR").expect("wire dir"));
    let host = dir.join("host");
    let result = if std::env::var_os("MINI_WIRE_DRY_RUN").is_some() {
        dry_run(&host, &dir.join("config.json"), &dir.join("intent.json"), OsStr::new("intent"),
            &dir.join("mini.key"), &dir.join("attempt")).map(|refusal| assert_eq!(refusal, None))
    } else {
        submit(&host, &dir.join("config.json"), &dir.join("intent.json"), OsStr::new("intent"),
            &dir.join("mini.key"), &dir.join("attempt"), false)
    };
    let mut log = fs::OpenOptions::new().append(true).open(dir.join("wire")).unwrap();
    writeln!(log, "result {result:?}").unwrap();
    log.write_all(custody_listing(&dir.join("attempt")).as_bytes()).unwrap();
}

#[test]
fn the_signing_path_wire_bytes_are_pinned() {
    pinned("tests/fixtures/signing-path.wire", false);
}

/// `mini dry-run` (op 130 over the signed plan) under the same control.
#[test]
fn the_dry_run_wire_bytes_are_pinned() {
    pinned("tests/fixtures/dry-run-path.wire", true);
}

fn pinned(golden: &str, dry_run: bool) {
    let dir = std::env::temp_dir().join(format!("mini-wire-{}-{}-{}", if dry_run { "dry" } else { "submit" }, std::process::id(),
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
    fs::create_dir(&dir).unwrap();
    let host = stand_in(&dir, "host", HOST);
    let consent = stand_in(&dir, "consent", CONSENT);
    fs::write(dir.join("config.json"), br#"{"domain":"7"}"#).unwrap();
    fs::write(dir.join("consent.json"), br#"{"consent":"settings"}"#).unwrap();
    fs::write(dir.join("intent.json"), br#"{"subject":"42","nonce":"9"}"#).unwrap();
    create_private(&dir.join("mini.key"), &[5u8; 32]).unwrap();
    fs::write(dir.join("wire"), b"").unwrap();
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "signing_wire_tests::signing_wire_worker", "--ignored", "--nocapture", "--test-threads=1"])
        .env("MINI_WIRE_DIR", &dir)
        .env("MINI_CONSENT_RESIDENT", "0")
        .env("MINI_CODEC_RESIDENT", "0") // a test binary has no `codec-resident` verb (client_consent::codec_test_lock)
        .env("HOME", &dir)
        .env("MINI_CONSENT_ANCHOR_DIR", dir.join("anchors"))
        .env("MINI_LOCAL_HOST", &host)
        .env("MINI_CONSENT_HOST", &consent)
        .env("MINI_CONSENT_CONFIG", dir.join("consent.json"))
        .env_remove("MINI_THIN_CONSENT")
        .env(if dry_run { "MINI_WIRE_DRY_RUN" } else { "MINI_WIRE_SUBMIT" }, "1")
        .output().unwrap();
    assert!(output.status.success(), "{}{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
    let wire = fs::read_to_string(dir.join("wire")).unwrap();
    let golden = Path::new(env!("CARGO_MANIFEST_DIR")).join(golden);
    if std::env::var_os("MINI_WIRE_REGEN").is_some() {
        fs::write(&golden, &wire).unwrap();
    }
    let expected = fs::read_to_string(&golden).unwrap();
    let _ = fs::remove_dir_all(&dir);
    assert!(wire.contains("result Ok(())"), "{wire}");
    assert_eq!(wire, expected, "the signing path changed a byte on the wire or in custody");
}
