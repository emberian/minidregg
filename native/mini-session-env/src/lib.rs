//! A hosted member session's consent and codec selection, read from the box's files.
//!
//! The ssh wrapper (`mini-line`, the forced command) exports these for a shell, and
//! `mini-web-spawn` hands them to a web body it starts directly: one reading, so the two
//! sessions of one member always select the same consent worker and codec Host.
use std::ffi::OsString;
use std::fs::File;
use std::io::Read;
use std::os::unix::ffi::OsStringExt;
use std::os::unix::fs::FileTypeExt;
use std::path::Path;

/// The first line of a small root-owned settings file, trimmed of blanks; `None` when the file
/// cannot be read.
pub fn first_line(path: &Path) -> Option<Vec<u8>> {
    let mut bytes = Vec::new();
    let _ = File::open(path).ok()?.take(4096).read_to_end(&mut bytes);
    let line = bytes.split(|b| *b == b'\n').next().unwrap_or_default();
    let blank = |b: &u8| *b == b' ' || *b == b'\t' || *b == b'\r';
    let start = line.iter().position(|b| !blank(b)).unwrap_or(line.len());
    let end = line.iter().rposition(|b| !blank(b)).map_or(start, |e| e + 1);
    Some(line[start..end].to_vec())
}

/// An absolute path from a settings line.
pub fn absolute(bytes: &[u8]) -> Option<OsString> {
    bytes.starts_with(b"/").then(|| OsString::from_vec(bytes.to_vec()))
}

fn is_digest(word: &[u8]) -> bool {
    word.len() == 64 && word.iter().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(b))
}

fn sha256_file(path: &Path) -> Result<String, String> {
    use sha2::Digest;
    let mut file = File::open(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut hasher = sha2::Sha256::new();
    std::io::copy(&mut file, &mut hasher).map_err(|e| format!("{}: {e}", path.display()))?;
    Ok(hasher.finalize().iter().map(|b| format!("{b:02x}")).collect())
}

/// Delegated full consent (split tenancy; `mini-consent@NAME.socket`, rendered per hosted
/// member): a member's client cannot read the operator's Store to replay it, so it asks the
/// operator's worker over `HOME/consent/peer.sock`. The client pins the listener (systemd's, uid
/// 0), the consent executable (`minidregg-client-consent` beside `mini`) and the pinned config by
/// sha256; the worker computes the same pins from the same files. The ship renders both digests
/// once into `HOME/consent/peer.pins` (root 0644, one line: `CONSENT_SHA256 CONFIG_SHA256`, 64
/// lowercase hex each), so no session hashes the 190 MB provider; a box shipped before that file
/// existed hashes here. Empty when no consent socket is beside `home`. `Err` is a refusal: a
/// malformed `peer.pins`, or a file that cannot be hashed.
pub fn delegated_consent(mini: &Path, host: &Path, config: &Path, home: &Path)
    -> Result<Vec<(&'static str, OsString)>, String> {
    let peer = home.join("consent/peer.sock");
    if !std::fs::symlink_metadata(&peer).is_ok_and(|m| m.file_type().is_socket()) {
        return Ok(Vec::new());
    }
    let consent_host = mini.parent().unwrap_or(Path::new("/")).join("minidregg-client-consent");
    let pins = home.join("consent/peer.pins");
    let (consent, settings) = match first_line(&pins) {
        Some(line) => {
            let mut words = line.split(|b| *b == b' ' || *b == b'\t').filter(|w| !w.is_empty());
            match (words.next(), words.next()) {
                (Some(a), Some(b)) if is_digest(a) && is_digest(b) => {
                    (String::from_utf8_lossy(a).into_owned(), String::from_utf8_lossy(b).into_owned())
                }
                _ => return Err(format!("{} must hold two sha256 digests", pins.display())),
            }
        }
        None => (sha256_file(&consent_host)?, sha256_file(config)?),
    };
    // The client takes a durable consent selection only with all of these together.
    Ok(vec![
        ("MINI_CONSENT_SOCKET", peer.into_os_string()),
        ("MINI_CONSENT_PEER_UID", "0".into()),
        ("MINI_CONSENT_HOST", consent_host.into_os_string()),
        ("MINI_LOCAL_HOST", host.as_os_str().to_owned()),
        ("MINI_CONSENT_CONFIG", config.as_os_str().to_owned()),
        ("MINI_CONSENT_SHA256", consent.into()),
        ("MINI_CONSENT_CONFIG_SHA256", settings.into()),
    ])
}

/// The box's shared codec Host (split tenancy): `session_codec` (`/etc/mini/session-codec`, root
/// 0644, one absolute socket path, `mini serve-codec`'s systemd listener in a directory of the
/// sessions' group). Every member's codec frames go there; the client refuses unless it greets
/// with the session's own Host image and settings digests. Empty without the file.
pub fn shared_codec(session_codec: &Path) -> Result<Vec<(&'static str, OsString)>, String> {
    let Some(line) = first_line(session_codec) else { return Ok(Vec::new()) };
    let socket = absolute(&line)
        .ok_or_else(|| format!("{} must name an absolute socket", session_codec.display()))?;
    Ok(vec![("MINI_CODEC_SOCKET", socket), ("MINI_CODEC_PEER_UID", "0".into())])
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::{Digest, Sha256};
    use std::collections::BTreeMap;
    use std::fs;

    #[test]
    fn delegated_consent_only_beside_a_consent_socket_and_pins_both_digests() {
        // Short on purpose: the scratch binds a Unix socket, and macOS caps its path at 104 bytes.
        let dir = std::env::temp_dir().join(format!("mse-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        let bin = dir.join("bin");
        fs::create_dir_all(&bin).unwrap();
        fs::write(bin.join("minidregg-client-consent"), b"provider").unwrap();
        fs::write(dir.join("config.json"), b"{}").unwrap();
        let (mini, host, config) = (bin.join("mini"), bin.join("minidregg-host"), dir.join("config.json"));
        let home = dir.join("h");
        fs::create_dir_all(home.join("consent")).unwrap();
        assert!(delegated_consent(&mini, &host, &config, &home).unwrap().is_empty(), "no socket");
        fs::write(home.join("consent/peer.sock"), b"").unwrap();
        assert!(delegated_consent(&mini, &host, &config, &home).unwrap().is_empty(), "a regular file is no socket");
        fs::remove_file(home.join("consent/peer.sock")).unwrap();
        let _listener = std::os::unix::net::UnixListener::bind(home.join("consent/peer.sock")).unwrap();
        let hex = |b: &[u8]| Sha256::digest(b).iter().map(|x| format!("{x:02x}")).collect::<String>();
        let env: BTreeMap<_, _> = delegated_consent(&mini, &host, &config, &home).unwrap().into_iter().collect();
        assert_eq!(env.len(), 7);
        assert_eq!(env["MINI_CONSENT_SOCKET"], home.join("consent/peer.sock").into_os_string());
        assert_eq!(env["MINI_CONSENT_PEER_UID"], OsString::from("0"));
        assert_eq!(env["MINI_CONSENT_SHA256"], OsString::from(hex(b"provider")));
        assert_eq!(env["MINI_CONSENT_CONFIG_SHA256"], OsString::from(hex(b"{}")));
        assert_eq!(env["MINI_LOCAL_HOST"], host.clone().into_os_string());
        assert_eq!(env["MINI_CONSENT_HOST"], bin.join("minidregg-client-consent").into_os_string());
        assert_eq!(env["MINI_CONSENT_CONFIG"], config.clone().into_os_string());
        // Rendered pins are taken as they are; a malformed file refuses.
        let (a, b) = ("a".repeat(64), "b".repeat(64));
        fs::write(home.join("consent/peer.pins"), format!("{a} {b}\n")).unwrap();
        let env: BTreeMap<_, _> = delegated_consent(&mini, &host, &config, &home).unwrap().into_iter().collect();
        assert_eq!((env["MINI_CONSENT_SHA256"].clone(), env["MINI_CONSENT_CONFIG_SHA256"].clone()), (a.into(), b.into()));
        fs::write(home.join("consent/peer.pins"), "nope\n").unwrap();
        assert!(delegated_consent(&mini, &host, &config, &home).is_err(), "malformed pins refuse");
        fs::remove_file(home.join("consent/peer.pins")).unwrap();
        fs::remove_file(bin.join("minidregg-client-consent")).unwrap();
        assert!(delegated_consent(&mini, &host, &config, &home).is_err(), "a socket without its provider refuses");
        let codec = dir.join("session-codec");
        assert!(shared_codec(&codec).unwrap().is_empty());
        fs::write(&codec, "relative/sock\n").unwrap();
        assert!(shared_codec(&codec).is_err());
        fs::write(&codec, "/run/mini/codec/codec.sock\n").unwrap();
        assert_eq!(shared_codec(&codec).unwrap()[0].1, OsString::from("/run/mini/codec/codec.sock"));
        let _ = fs::remove_dir_all(&dir);
    }
}
