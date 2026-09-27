//! Loaded-current application birth authoring. The Host derives and checks the
//! complete canonical intent; this client only retains its exact bytes before
//! the ordinary `mini submit --intent-kind binary` custody path may dispatch.
use crate::{
    copy_new, create_dir, create_private, hex, host_image_sha256, session_invoke,
    sync_directory_ancestors, Result,
};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, File};
use std::io::Read;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;

const MAX_SOURCE: usize = 256 * 1024;
const MAX_INTENT: usize = 4 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Route {
    Application,
    Session,
}

impl Route {
    fn operation(self) -> u8 {
        match self {
            Self::Application => 30,
            Self::Session => 31,
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::Application => "application",
            Self::Session => "session",
        }
    }
}

fn bounded_source(path: &Path) -> Result<Vec<u8>> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|e| format!("current birth source {}: {e}", path.display()))?;
    if !metadata.file_type().is_file() || metadata.len() == 0 || metadata.len() > MAX_SOURCE as u64
    {
        return Err("current birth source must be a nonempty regular file at most 256 KiB".into());
    }
    let mut bytes = Vec::new();
    File::open(path)
        .and_then(|file| file.take((MAX_SOURCE + 1) as u64).read_to_end(&mut bytes))
        .map_err(|e| format!("current birth source {}: {e}", path.display()))?;
    if bytes.is_empty() || bytes.len() > MAX_SOURCE {
        return Err("current birth source exceeds bound".into());
    }
    let value: Value =
        serde_json::from_slice(&bytes).map_err(|e| format!("current birth source JSON: {e}"))?;
    if !value.is_object() {
        return Err("current birth source must be a JSON object".into());
    }
    Ok(bytes)
}

fn intent_from_frame(route: Route, frame: &[u8]) -> Result<&[u8]> {
    match frame {
        [255, ..] => Err(format!(
            "current {} birth authoring refused; retained encoded Host outcome",
            route.label()
        )),
        [operation, bytes @ ..]
            if *operation == route.operation()
                && !bytes.is_empty()
                && bytes.len() <= MAX_INTENT =>
        {
            Ok(bytes)
        }
        _ => Err("current birth Host reply has the wrong opcode or intent bound".into()),
    }
}

pub(crate) fn author(
    host: &Path,
    config: &Path,
    socket: &Path,
    source: &Path,
    directory: &Path,
    route: Route,
) -> Result<()> {
    let source_bytes = bounded_source(source)?;
    create_dir(directory)?;
    fs::set_permissions(directory, fs::Permissions::from_mode(0o700))
        .map_err(|e| format!("current birth attempt mode: {e}"))?;
    let retained_source = directory.join("source.json");
    let retained_config = directory.join("config.json");
    copy_new(source, &retained_source)?;
    copy_new(config, &retained_config)?;
    let retained_bytes = bounded_source(&retained_source)?;
    if retained_bytes != source_bytes {
        return Err("current birth source changed during retention".into());
    }
    let source_sha = hex(&Sha256::digest(&retained_bytes));
    let host_sha = host_image_sha256(host)?;
    let manifest = json!({
        "type":"minidregg-current-application-birth-author-v1",
        "route":route.label(),"operation":route.operation(),
        "host":host,"hostSha256":host_sha,"config":retained_config,
        "socket":socket,"sourceSha256":source_sha,
    });
    create_private(
        &directory.join("author.json"),
        &serde_json::to_vec_pretty(&manifest).map_err(|e| e.to_string())?,
    )?;
    sync_directory_ancestors(directory)?;
    let frame = session_invoke(
        host,
        socket,
        &retained_config,
        route.operation(),
        &retained_bytes,
    )?;
    create_private(&directory.join("reply.frame"), &frame)?;
    sync_directory_ancestors(directory)?;
    let bytes = intent_from_frame(route, &frame)?;
    create_private(&directory.join("intent.bin"), bytes)?;
    sync_directory_ancestors(directory)?;
    println!("{}", directory.join("intent.bin").display());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Read, Write};
    use std::os::unix::net::UnixListener;
    use std::thread;

    #[test]
    fn only_matching_bounded_canonical_intent_frame_is_released() {
        assert_eq!(
            intent_from_frame(Route::Application, &[30, 1, 2]).unwrap(),
            &[1, 2]
        );
        assert!(intent_from_frame(Route::Application, &[31, 1]).is_err());
        assert!(intent_from_frame(Route::Application, &[30]).is_err());
        assert!(intent_from_frame(Route::Application, &[255, 9]).is_err());
        assert!(intent_from_frame(Route::Session, &[30, 1]).is_err());
        assert_eq!(intent_from_frame(Route::Session, &[31, 3]).unwrap(), &[3]);
    }

    #[test]
    fn v2_socket_reply_is_retained_before_publishing_intent_or_refusal() {
        for reply in [vec![30, 1, 2, 3], vec![255, 7, 8]] {
            let root = std::env::temp_dir().join(format!(
                "mini-current-birth-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            fs::create_dir(&root).unwrap();
            let host = root.join("host");
            let config = root.join("config.json");
            let source = root.join("source.json");
            let socket = root.join("host.sock");
            let directory = root.join("attempt");
            fs::write(&host, b"pinned host image").unwrap();
            fs::write(&config, b"{}").unwrap();
            fs::write(&source, b"{\"subject\":\"7\"}").unwrap();
            let listener = UnixListener::bind(&socket).unwrap();
            let sent = reply.clone();
            let peer = thread::spawn(move || {
                let (mut stream, _) = listener.accept().unwrap();
                let mut length = [0u8; 4];
                stream.read_exact(&mut length).unwrap();
                let mut envelope = vec![0u8; u32::from_le_bytes(length) as usize];
                stream.read_exact(&mut envelope).unwrap();
                assert_eq!(envelope[0], 2, "host image must use pinned v2 envelope");
                let source = b"{\"subject\":\"7\"}";
                assert!(envelope.ends_with(source));
                assert_eq!(envelope[envelope.len() - source.len() - 1], 30);
                stream
                    .write_all(&(sent.len() as u32).to_le_bytes())
                    .unwrap();
                stream.write_all(&sent).unwrap();
            });
            let result = author(
                &host,
                &config,
                &socket,
                &source,
                &directory,
                Route::Application,
            );
            peer.join().unwrap();
            assert_eq!(fs::read(directory.join("reply.frame")).unwrap(), reply);
            if reply[0] == 30 {
                result.unwrap();
                assert_eq!(fs::read(directory.join("intent.bin")).unwrap(), &[1, 2, 3]);
            } else {
                assert!(result.is_err());
                assert!(!directory.join("intent.bin").exists());
            }
            fs::remove_dir_all(root).unwrap();
        }
    }
}
