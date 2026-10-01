//! Loaded-current application birth authoring. The Host derives and checks the
//! complete canonical intent; this client only retains its exact bytes before
//! the ordinary `mini submit --intent-kind binary` custody path may dispatch.
use crate::{
    copy_new, create_private, hex, host_image_sha256, session_invoke, sync_directory_ancestors,
    Result,
};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, File};
use std::io::Read;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, PermissionsExt};
use std::path::Path;

/// Births carrying a Nock program (NOCK K-NOCK-CELL) carry its hex in the source.
const MAX_SOURCE: usize = 4 * 1024 * 1024;
const MAX_INTENT: usize = 4 * 1024 * 1024;

fn retained_file(path: &Path, limit: usize) -> Result<Vec<u8>> {
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    let metadata = fs::symlink_metadata(path).map_err(|e| format!("{}: {e}", path.display()))?;
    if !metadata.file_type().is_file()
        || metadata.uid() != unsafe { geteuid() }
        || metadata.len() == 0
        || metadata.len() > limit as u64
    {
        return Err(format!(
            "{} is not an owner-retained bounded regular file",
            path.display()
        ));
    }
    let mut bytes = Vec::new();
    File::open(path)
        .and_then(|file| file.take((limit + 1) as u64).read_to_end(&mut bytes))
        .map_err(|e| format!("{}: {e}", path.display()))?;
    if bytes.len() != metadata.len() as usize {
        return Err("retained file changed during read".into());
    }
    Ok(bytes)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Route {
    Application,
    Session,
    Resource,
}

impl Route {
    fn operation(self) -> u8 {
        match self {
            Self::Application => 30,
            Self::Session => 31,
            Self::Resource => 91,
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::Application => "application",
            Self::Session => "session",
            Self::Resource => "resource",
        }
    }
}

fn bounded_source(path: &Path) -> Result<Vec<u8>> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|e| format!("current birth source {}: {e}", path.display()))?;
    if !metadata.file_type().is_file() || metadata.len() == 0 || metadata.len() > MAX_SOURCE as u64
    {
        return Err("current birth source must be a nonempty regular file at most 4 MiB".into());
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
    signed_factory_observation: Option<&Path>,
    directory: &Path,
    route: Route,
) -> Result<()> {
    let source_bytes = bounded_source(source)?;
    if fs::symlink_metadata(directory).is_err() {
        let mut builder = fs::DirBuilder::new();
        builder.mode(0o700);
        builder
            .create(directory)
            .map_err(|e| format!("current birth attempt directory: {e}"))?;
    }
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    let named = fs::symlink_metadata(directory).map_err(|e| e.to_string())?;
    if !named.file_type().is_dir()
        || named.uid() != unsafe { geteuid() }
        || named.permissions().mode() & 0o077 != 0
    {
        return Err("current birth attempt must be an owner-private real directory".into());
    }
    let retained_source = directory.join("source.json");
    let retained_config = directory.join("config.json");
    if !retained_source.exists() {
        copy_new(source, &retained_source)?;
    }
    if !retained_config.exists() {
        copy_new(config, &retained_config)?;
    }
    let retained_bytes = bounded_source(&retained_source)?;
    if retained_bytes != source_bytes {
        return Err("current birth source changed during retention".into());
    }
    if fs::read(config).map_err(|e| e.to_string())? != retained_file(&retained_config, MAX_SOURCE)?
    {
        return Err("current birth config changed during retention".into());
    }
    let source_sha = hex(&Sha256::digest(&retained_bytes));
    let host_sha = host_image_sha256(host)?;
    let retained_observation = directory.join("factory-observation.bin");
    let observation_bytes = match (route, signed_factory_observation) {
        (Route::Resource, supplied) => {
            if !retained_observation.exists() {
                let supplied =
                    supplied.ok_or("current resource birth requires signed factory observation")?;
                let bytes = fs::read(supplied)
                    .map_err(|e| format!("cannot read signed factory observation: {e}"))?;
                if bytes.is_empty() || bytes.len() > MAX_INTENT {
                    return Err("signed factory observation is empty or too large".into());
                }
                create_private(&retained_observation, &bytes)?;
            }
            let bytes = retained_file(&retained_observation, MAX_INTENT)?;
            Some(bytes)
        }
        (_, Some(_)) => {
            return Err("application/session authoring takes no factory observation".into())
        }
        (_, None) => None,
    };
    let manifest = json!({
        "type":"minidregg-current-application-birth-author-v1",
        "route":route.label(),"operation":route.operation(),
        "host":host,"hostSha256":host_sha,"config":retained_config,
        "socket":socket,"sourceSha256":source_sha,
        "factoryObservationSha256":observation_bytes.as_ref().map(|bytes|hex(&Sha256::digest(bytes))),
    });
    let manifest_path = directory.join("author.json");
    if manifest_path.exists() {
        let old: Value = serde_json::from_slice(&retained_file(&manifest_path, MAX_SOURCE)?)
            .map_err(|e| format!("retained current birth manifest: {e}"))?;
        if old != manifest {
            return Err("retained current birth author differs from current pinned inputs".into());
        }
    } else {
        create_private(
            &manifest_path,
            &serde_json::to_vec_pretty(&manifest).map_err(|e| e.to_string())?,
        )?;
    }
    sync_directory_ancestors(directory)?;
    if directory.join("reply.frame").exists() {
        let intent = retained_intent(directory, route)?;
        println!("{}", intent.display());
        return Ok(());
    }
    let payload = if let Some(observation) = &observation_bytes {
        let len: u32 = observation
            .len()
            .try_into()
            .map_err(|_| "observation too long")?;
        let mut framed = len.to_le_bytes().to_vec();
        framed.extend_from_slice(observation);
        framed.extend_from_slice(&retained_bytes);
        framed
    } else {
        retained_bytes.clone()
    };
    let frame = session_invoke(host, socket, &retained_config, route.operation(), &payload)?;
    create_private(&directory.join("reply.frame"), &frame)?;
    sync_directory_ancestors(directory)?;
    let bytes = intent_from_frame(route, &frame)?;
    create_private(&directory.join("intent.bin"), bytes)?;
    sync_directory_ancestors(directory)?;
    println!("{}", directory.join("intent.bin").display());
    Ok(())
}

/// Finish local author retention after a crash between the complete Host frame
/// and the copied intent. This never contacts Host or submits an effect.
pub(crate) fn retained_intent(directory: &Path, route: Route) -> Result<std::path::PathBuf> {
    let manifest: Value =
        serde_json::from_slice(&retained_file(&directory.join("author.json"), MAX_SOURCE)?)
            .map_err(|e| e.to_string())?;
    if manifest.get("route").and_then(Value::as_str) != Some(route.label())
        || manifest.get("operation").and_then(Value::as_u64) != Some(route.operation() as u64)
    {
        return Err("retained current birth author route differs".into());
    }
    let source = directory.join("source.json");
    let source_bytes = bounded_source(&source)?;
    if manifest.get("sourceSha256").and_then(Value::as_str)
        != Some(hex(&Sha256::digest(&source_bytes)).as_str())
    {
        return Err("retained current birth source changed".into());
    }
    if route == Route::Resource {
        let observation = retained_file(&directory.join("factory-observation.bin"), MAX_INTENT)?;
        if manifest
            .get("factoryObservationSha256")
            .and_then(Value::as_str)
            != Some(hex(&Sha256::digest(&observation)).as_str())
        {
            return Err("retained signed factory observation changed".into());
        }
    }
    let frame = retained_file(&directory.join("reply.frame"), MAX_INTENT + 1)?;
    let exact = intent_from_frame(route, &frame)?;
    let path = directory.join("intent.bin");
    if path.exists() {
        if retained_file(&path, MAX_INTENT)? != exact {
            return Err("retained current birth intent differs from Host reply".into());
        }
    } else {
        create_private(&path, exact)?;
        sync_directory_ancestors(directory)?;
    }
    Ok(path)
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
        assert_eq!(intent_from_frame(Route::Resource, &[91, 4]).unwrap(), &[4]);
        assert!(intent_from_frame(Route::Resource, &[32, 4]).is_err());
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
                None,
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

    #[test]
    fn resource_author_resumes_partial_retention_and_never_reissues_after_reply() {
        let root = std::env::temp_dir().join(format!(
            "mra-{}-{}",
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
        let observation = root.join("signed-observation.bin");
        let socket = root.join("host.sock");
        let directory = root.join("attempt");
        fs::write(&host, b"pinned host image").unwrap();
        fs::write(&config, b"{}").unwrap();
        fs::write(&source, b"{\"subject\":\"7\"}").unwrap();
        fs::write(&observation, b"signed factory observation").unwrap();
        let mut builder = fs::DirBuilder::new();
        builder.mode(0o700);
        builder.create(&directory).unwrap(); // interrupted immediately after mkdir
        let listener = UnixListener::bind(&socket).unwrap();
        let peer = thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut length = [0u8; 4];
            stream.read_exact(&mut length).unwrap();
            let mut envelope = vec![0u8; u32::from_le_bytes(length) as usize];
            stream.read_exact(&mut envelope).unwrap();
            assert_eq!(envelope[0], 2);
            assert!(envelope.ends_with(b"{\"subject\":\"7\"}"));
            assert!(envelope
                .windows(26)
                .any(|bytes| bytes == b"signed factory observation"));
            stream.write_all(&[3, 0, 0, 0, 91, 1, 2]).unwrap();
        });
        author(
            &host,
            &config,
            &socket,
            &source,
            Some(&observation),
            &directory,
            Route::Resource,
        )
        .unwrap();
        peer.join().unwrap();
        assert_eq!(fs::read(directory.join("intent.bin")).unwrap(), [1, 2]);
        fs::remove_file(directory.join("intent.bin")).unwrap(); // interrupted after durable reply
        author(
            &host,
            &config,
            &socket,
            &source,
            None,
            &directory,
            Route::Resource,
        )
        .unwrap();
        assert_eq!(fs::read(directory.join("intent.bin")).unwrap(), [1, 2]);
        fs::remove_dir_all(root).unwrap();
    }
}
