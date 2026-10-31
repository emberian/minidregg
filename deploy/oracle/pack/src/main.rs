//! Physical operator packer: exact staged members, canonical Sandstorm SPK signing.
//! No Mini authority, admission or runtime policy is implemented here.
use ed25519_dalek::{Signer, SigningKey};
use minidregg_spk_package_stream::archive_capnp;
use sandstorm_package::{spk::base32, File, FileContent};
use serde_json::{json, Value};
use sha2::{Digest, Sha256, Sha512};
use std::{
    collections::BTreeMap,
    fs::{self, OpenOptions},
    io::{Read, Write},
    os::unix::fs::{OpenOptionsExt, PermissionsExt},
    path::{Path, PathBuf},
};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
const RAW_LIMIT: usize = 256 * 1024 * 1024;
const DECODED_LIMIT: usize = 768 * 1024 * 1024;

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
fn text<'a>(v: &'a Value, key: &str) -> Result<&'a str> {
    v[key]
        .as_str()
        .ok_or_else(|| format!("missing string {key}").into())
}
fn canonical(path: &str) -> Result<()> {
    if path.is_empty()
        || path.starts_with('/')
        || path.len() > 4096
        || path.split('/').count() > 64
        || path
            .split('/')
            .any(|p| p.is_empty() || p == "." || p == ".." || p.len() > 255)
        || path.chars().any(|c| c.is_control() || c == '\\')
    {
        return Err("invalid staged package path".into());
    }
    Ok(())
}
fn read_regular(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    if !file.metadata()?.is_file() || file.metadata()?.len() > limit as u64 {
        return Err("input is not a bounded regular file".into());
    }
    let mut bytes = Vec::new();
    file.take(limit as u64 + 1).read_to_end(&mut bytes)?;
    if bytes.len() > limit {
        return Err("input grew beyond bound".into());
    }
    Ok(bytes)
}
fn key(path: &Path) -> Result<SigningKey> {
    if fs::symlink_metadata(path)?.permissions().mode() & 0o077 != 0 {
        return Err("private key must have no group/other permission".into());
    }
    let bytes = read_regular(path, 32)?;
    let seed: [u8; 32] = bytes
        .try_into()
        .map_err(|_| "private key must be exactly 32 bytes")?;
    Ok(SigningKey::from_bytes(&seed))
}
fn keygen(path: &Path) -> Result<()> {
    let mut seed = [0u8; 32];
    std::fs::File::open("/dev/urandom")?.read_exact(&mut seed)?;
    let mut out = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)?;
    out.write_all(&seed)?;
    let signing = SigningKey::from_bytes(&seed);
    println!(
        "{}",
        json!({"app_id":base32(signing.verifying_key().as_bytes()),
        "public_key_hex":hex(signing.verifying_key().as_bytes())})
    );
    Ok(())
}
fn source_path(stage: &Path, receipt: &Value, member: &str) -> Result<PathBuf> {
    let source = &receipt["package_sources"][member];
    let root = match text(source, "root")? {
        "image" => stage.join("image"),
        "appliance" => PathBuf::from(text(&receipt["inputs"], "appliance")?),
        "rootfs" => PathBuf::from(text(&receipt["inputs"], "rootfs")?),
        _ => return Err("unknown physical input root".into()),
    };
    let relative = text(source, "path")?;
    canonical(relative)?;
    Ok(root.join(relative))
}
fn tree(
    parent: &str,
    entries: &BTreeMap<String, Value>,
    sources: &BTreeMap<String, FileContent>,
) -> Result<Vec<File>> {
    let mut files = Vec::new();
    for (path, entry) in entries {
        let (directory, leaf) = path.rsplit_once('/').unwrap_or(("", path));
        if directory != parent {
            continue;
        }
        let content = if text(entry, "kind")? == "directory" {
            FileContent::Directory(tree(path, entries, sources)?)
        } else {
            sources.get(path).ok_or("missing member source")?.clone()
        };
        files.push(File {
            name: leaf.to_owned(),
            content,
            mtime_ns: 0,
        });
    }
    Ok(files)
}

fn fill_files(
    mut builder: capnp::struct_list::Builder<'_, archive_capnp::archive::file::Owned>,
    files: &[File],
) {
    for (index, file) in files.iter().enumerate() {
        let mut entry = builder.reborrow().get(index as u32);
        entry.set_name(&file.name);
        entry.set_last_modification_time_ns(0);
        match &file.content {
            FileContent::Regular(bytes) => entry.set_regular(bytes),
            FileContent::Executable(bytes) => entry.set_executable(bytes),
            FileContent::Symlink(target) => entry.set_symlink(target),
            FileContent::Directory(children) => {
                fill_files(entry.init_directory(children.len() as u32), children)
            }
        }
    }
}

fn sign_archive(files: &[File], signing: &SigningKey) -> Result<(Vec<u8>, usize)> {
    // Reuse the canonical generated schema already used by the production
    // verifier. In particular, empty regular/executable data remains a byte
    // list, not the void list emitted by the pinned legacy Bread writer.
    let archive = {
        let mut message = capnp::message::Builder::new_default();
        fill_files(
            message
                .init_root::<archive_capnp::archive::Builder>()
                .init_files(files.len() as u32),
            files,
        );
        capnp::serialize::write_message_to_words(&message)
    };
    let hash = Sha512::digest(&archive);
    let mut combined = signing.sign(&hash).to_bytes().to_vec();
    combined.extend_from_slice(&hash);
    let mut signature = capnp::message::Builder::new_default();
    {
        let mut root = signature.init_root::<archive_capnp::signature::Builder>();
        root.set_public_key(signing.verifying_key().as_bytes());
        root.set_signature(&combined);
    }
    let signature = capnp::serialize::write_message_to_words(&signature);
    let decoded = signature.len() + archive.len();
    if decoded > DECODED_LIMIT {
        return Err("package exceeds standard decoded limit".into());
    }
    let mut encoder = xz2::write::XzEncoder::new(Vec::new(), 6);
    encoder.write_all(&signature)?;
    encoder.write_all(&archive)?;
    let mut bytes = vec![0x8f, 0xc6, 0xcd, 0xef, 0x45, 0x1a, 0xea, 0x96];
    bytes.extend(encoder.finish()?);
    Ok((bytes, decoded))
}
fn pack(stage: &Path, stage_sha: &str, private_key: &Path, output: &Path) -> Result<()> {
    if output.exists() {
        return Err("output already exists".into());
    }
    let raw = read_regular(&stage.join("STAGE.json"), 64 * 1024 * 1024)?;
    if hex(&Sha256::digest(&raw)) != stage_sha {
        return Err("stage receipt hash mismatch".into());
    }
    let receipt: Value = serde_json::from_slice(&raw)?;
    if text(&receipt, "schema")? != "oracle-package-stage-v1" {
        return Err("unknown stage schema".into());
    }
    let signing = key(private_key)?;
    let app_id = base32(signing.verifying_key().as_bytes());
    if text(&receipt, "app_id")? != app_id {
        return Err("signing key differs from staged app identity".into());
    }
    let entries: BTreeMap<String, Value> =
        serde_json::from_value(receipt["expected_package_entries"].clone())?;
    if entries.len() > 100_000 {
        return Err("too many package members".into());
    }
    let mut sources = BTreeMap::new();
    let mut total = 0usize;
    for (path, entry) in &entries {
        canonical(path)?;
        if let Some((parent, _)) = path.rsplit_once('/') {
            if entries.get(parent).and_then(|e| e["kind"].as_str()) != Some("directory") {
                return Err("member parent is not a staged directory".into());
            }
        }
        let content = match text(entry, "kind")? {
            "directory" => continue,
            "symlink" => {
                let expected = text(entry, "target")?;
                if fs::read_link(source_path(stage, &receipt, path)?)?.to_str() != Some(expected) {
                    return Err(format!("symlink changed: {path}").into());
                }
                FileContent::Symlink(expected.to_owned())
            }
            "file" => {
                let size = entry["size"].as_u64().ok_or("missing member size")?;
                if size >= 512 * 1024 * 1024 {
                    return Err("SPK member exceeds format limit".into());
                }
                total = total
                    .checked_add(size as usize)
                    .ok_or("member total overflow")?;
                if total > 700 * 1024 * 1024 {
                    return Err("runtime exceeds standard decoded budget; reduce closure".into());
                }
                let path_source = source_path(stage, &receipt, path)?;
                let executable = entry["executable"]
                    .as_bool()
                    .ok_or("missing executable flag")?;
                if (fs::symlink_metadata(&path_source)?.permissions().mode() & 0o111 != 0)
                    != executable
                {
                    return Err(format!("executable bits changed: {path}").into());
                }
                let bytes = read_regular(&path_source, size as usize)?;
                if bytes.len() as u64 != size
                    || hex(&Sha256::digest(&bytes)) != text(entry, "sha256")?
                {
                    return Err(format!("member bytes changed: {path}").into());
                }
                if executable {
                    FileContent::Executable(bytes)
                } else {
                    FileContent::Regular(bytes)
                }
            }
            _ => return Err("unknown member type".into()),
        };
        sources.insert(path.clone(), content);
    }
    let files = tree("", &entries, &sources)?;
    drop(sources);
    let (bytes, decoded) = sign_archive(&files, &signing)?;
    if bytes.len() > RAW_LIMIT {
        return Err("compressed runtime exceeds Mini's 256 MiB cap".into());
    }
    let mut temporary =
        tempfile::NamedTempFile::new_in(output.parent().ok_or("output needs parent")?)?;
    temporary.write_all(&bytes)?;
    temporary.persist_noclobber(output)?;
    println!(
        "{}",
        json!({"app_id":app_id,"raw_sha256":hex(&Sha256::digest(&bytes)),
        "raw_bytes":bytes.len(),"decoded_bytes":decoded,"members":entries.len(),
        "stage_sha256":stage_sha,"verification":"Signed package requires independent post-pack inventory verification."})
    );
    Ok(())
}
fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("keygen") if args.len() == 3 => keygen(Path::new(&args[2])),
        Some("pack") if args.len() == 6 => pack(Path::new(&args[2]), &args[3], Path::new(&args[4]), Path::new(&args[5])),
        _ => Err("usage: minidregg-oracle-pack keygen PRIVATE_KEY | pack STAGE STAGE_SHA256 PRIVATE_KEY NEW_OUTPUT.spk".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> (tempfile::TempDir, PathBuf, PathBuf, String) {
        let dir = tempfile::tempdir().unwrap();
        let stage = dir.path().join("stage");
        fs::create_dir_all(stage.join("image/opt/oracle-data")).unwrap();
        let key_path = dir.path().join("test-key");
        let mut key_file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&key_path)
            .unwrap();
        key_file.write_all(&[9; 32]).unwrap();
        let app_id = base32(SigningKey::from_bytes(&[9; 32]).verifying_key().as_bytes());
        let files = [
            ("sandstorm-manifest", br#"{"app_id":"fixture-only","app_title":"packer fixture","app_version":1,"continue_command":{"argv":["/app"]}}"#.as_slice()),
            ("app", b"fixture payload".as_slice()),
            ("minidregg-data.json", br#"{"schema":"minidregg-public-data-v1","inventory_sha256":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}"#.as_slice()),
        ];
        let mut entries = serde_json::Map::new();
        let mut sources = serde_json::Map::new();
        for (name, bytes) in files {
            fs::write(stage.join("image").join(name), bytes).unwrap();
            entries.insert(name.into(), json!({"kind":"file","size":bytes.len(),"sha256":hex(&Sha256::digest(bytes)),"executable":false}));
            sources.insert(name.into(), json!({"root":"image","path":name}));
        }
        for name in ["opt", "opt/oracle-data"] {
            entries.insert(name.into(), json!({"kind":"directory"}));
        }
        std::os::unix::fs::symlink(
            "/opt/oracle-data/root/store.sqlite3",
            stage.join("image/store"),
        )
        .unwrap();
        entries.insert(
            "store".into(),
            json!({"kind":"symlink","target":"/opt/oracle-data/root/store.sqlite3"}),
        );
        sources.insert("store".into(), json!({"root":"image","path":"store"}));
        let receipt = json!({"schema":"oracle-package-stage-v1","app_id":app_id,"version":1,
            "expected_package_entries":entries,"package_sources":sources});
        let bytes = serde_json::to_vec(&receipt).unwrap();
        fs::write(stage.join("STAGE.json"), &bytes).unwrap();
        (dir, stage, key_path, hex(&Sha256::digest(bytes)))
    }

    #[test]
    fn real_signed_split_package_preserves_members() {
        let (dir, stage, key_path, stage_sha) = fixture();
        let output = dir.path().join("runtime.spk");
        pack(&stage, &stage_sha, &key_path, &output).unwrap();
        let parsed = sandstorm_package::Spk::parse(&fs::read(&output).unwrap()).unwrap();
        assert_eq!(
            parsed.archive.find("app"),
            Some(b"fixture payload".as_slice())
        );
        assert!(parsed.archive.files.iter().any(|f| f.name == "store" && matches!(&f.content, FileContent::Symlink(target) if target == "/opt/oracle-data/root/store.sqlite3")));
        assert_eq!(
            parsed.public_key,
            SigningKey::from_bytes(&[9; 32]).verifying_key().to_bytes()
        );
        assert!(pack(&stage, &stage_sha, &key_path, &output).is_err());
    }

    #[test]
    fn changed_members_or_stage_are_not_published() {
        let (dir, stage, key_path, stage_sha) = fixture();
        let output = dir.path().join("must-not-exist.spk");
        fs::write(stage.join("image/app"), b"changed payload").unwrap();
        assert!(pack(&stage, &stage_sha, &key_path, &output)
            .unwrap_err()
            .to_string()
            .contains("member bytes changed"));
        assert!(!output.exists());
        assert!(pack(&stage, &"0".repeat(64), &key_path, &output)
            .unwrap_err()
            .to_string()
            .contains("stage receipt hash mismatch"));
        assert!(!output.exists());
    }

    #[test]
    fn empty_regular_and_executable_pass_independent_capnp_verification() {
        let files = vec![
            File::regular("sandstorm-manifest", br#"{"app_id":"fixture-only","app_title":"empty fixture","app_version":1,"continue_command":{"argv":["/empty-executable"]}}"#.to_vec()),
            File::regular("empty-regular", Vec::new()),
            File::executable("empty-executable", Vec::new()),
        ];
        let (bytes, _) = sign_archive(&files, &SigningKey::from_bytes(&[11; 32])).unwrap();
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("empty.spk");
        fs::write(&path, bytes).unwrap();
        let verified = minidregg_spk_package_stream::verify(
            &path,
            dir.path(),
            minidregg_spk_package_stream::Limits::DEFAULT,
        )
        .unwrap();
        for wanted in ["empty-regular", "empty-executable"] {
            let (index, entry) = verified
                .entries()
                .iter()
                .enumerate()
                .find(|(_, e)| e.path == Path::new(wanted))
                .unwrap();
            assert_eq!(entry.len(), 0);
            assert!(
                matches!(entry.kind, minidregg_spk_package_stream::EntryKind::Regular { executable } if executable == (wanted == "empty-executable"))
            );
            let mut copied = Vec::new();
            verified.copy_member(index, &mut copied).unwrap();
            assert!(copied.is_empty());
        }
    }
}
