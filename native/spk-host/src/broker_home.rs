//! Root-declared read-only visibility for an existing Store outside /var.
//! This affects the operator resident only. The app's bwrap root stays separate.
use super::*;
use std::collections::BTreeSet;
use std::os::unix::fs::FileTypeExt;

fn text(path: &Path) -> io::Result<&str> {
    let value = path
        .to_str()
        .ok_or_else(|| invalid("visibility path is not UTF-8"))?;
    if !path.is_absolute()
        || path.components().count() < 3
        || value.len() > 4096
        || !value
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"/_-.".contains(&b))
        || path.components().any(|part| {
            !matches!(
                part,
                std::path::Component::RootDir | std::path::Component::Normal(_)
            )
        })
    {
        return Err(invalid(
            "visibility path is not a literal absolute file/socket-parent path",
        ));
    }
    Ok(value)
}

pub(super) fn validate(paths: &[PathBuf], uid: u32) -> io::Result<()> {
    if paths.len() > 256 {
        return Err(invalid("resident visibility inventory exceeds 256 paths"));
    }
    let mut seen = BTreeSet::new();
    for path in paths {
        text(path)?;
        if !seen.insert(path) || fs::canonicalize(path)? != *path {
            return Err(invalid("resident visibility path duplicated or symlinked"));
        }
        let mut prefix = PathBuf::from("/");
        for part in path.components().skip(1) {
            prefix.push(part);
            let meta = fs::symlink_metadata(&prefix)?;
            if meta.file_type().is_symlink()
                || ![0, uid].contains(&meta.uid())
                || meta.mode() & 0o022 != 0
            {
                return Err(invalid(format!(
                    "resident visibility custody refused: {}",
                    prefix.display()
                )));
            }
        }
        let meta = fs::symlink_metadata(path)?;
        if meta.is_file() {
            if meta.nlink() != 1 {
                return Err(invalid("resident visibility file has multiple links"));
            }
        } else if meta.is_dir() {
            // At render time only the exact resident's Mini socket parent is
            // selected. A general home/build directory is never exposed.
            if path.components().count() < 4 {
                return Err(invalid("broad resident directory visibility refused"));
            }
            let sockets = fs::read_dir(path)?.filter_map(Result::ok).any(|e| {
                fs::symlink_metadata(e.path()).is_ok_and(|m| {
                    m.file_type().is_socket() && m.uid() == uid && m.mode() & 0o002 == 0
                })
            });
            if !sockets {
                return Err(invalid(
                    "resident visible directory is not an operator socket parent",
                ));
            }
        } else {
            return Err(invalid(
                "resident visibility permits regular files/socket parent only",
            ));
        }
    }
    Ok(())
}

fn path_field(value: &Value, field: &str) -> io::Result<PathBuf> {
    let path = value
        .get(field)
        .and_then(Value::as_str)
        .ok_or_else(|| invalid(format!("resident lacks {field}")))?;
    let path = PathBuf::from(path);
    text(&path)?;
    Ok(path)
}
fn home(path: &Path) -> bool {
    path.starts_with("/home") || path.starts_with("/root")
}

pub(super) fn render(
    broker: &Broker,
    store: &str,
    app: &str,
    resident: &Value,
) -> io::Result<String> {
    if resident.get("protocol").and_then(Value::as_str) != Some("mini-spk-resident-start-v3") {
        return Err(invalid(
            "resident visibility requires exact native resident v3 config",
        ));
    }
    let declared = &broker.config.resident_home_read_only_paths;
    validate(declared, broker.operator_uid)?;
    let mut needed = BTreeSet::<PathBuf>::new();
    for field in ["miniConfig", "miniHost", "completionCustodianSeed"] {
        let path = path_field(resident, field)?;
        if home(&path) {
            needed.insert(path);
        }
    }
    let socket = path_field(resident, "miniOperatorSocket")?;
    let socket_parent = socket
        .parent()
        .ok_or_else(|| invalid("Mini socket lacks parent"))?;
    if home(socket_parent) {
        needed.insert(socket_parent.to_path_buf());
    }
    let actual_socket = fs::symlink_metadata(&socket)?;
    if !actual_socket.file_type().is_socket() || actual_socket.uid() != broker.operator_uid {
        return Err(invalid(
            "resident Mini endpoint is not this operator's socket",
        ));
    }
    let app_dir = broker.root().join(store).join("host/apps").join(app);
    for (field, leaf) in [
        ("beginManagementCustody", "begin.json"),
        ("claimManagementCustody", "claim.json"),
        ("completionManagementCustody", "completion.json"),
    ] {
        if path_field(resident, field)? != app_dir.join("custody").join(leaf) {
            return Err(invalid(
                "resident management custody differs from fixed app directory",
            ));
        }
        let mut file = open_operator_file(
            broker.root(),
            &[store, "host", "apps", app, "custody", leaf],
            broker.operator_uid,
        )?;
        let mut bytes = Vec::new();
        Read::by_ref(&mut file)
            .take(MAX_CONFIG + 1)
            .read_to_end(&mut bytes)?;
        if bytes.len() as u64 > MAX_CONFIG {
            return Err(invalid("management custody exceeds bound"));
        }
        seeds(&serde_json::from_slice::<Value>(&bytes)?, &mut needed)?;
    }
    for entrance in resident
        .get("entrances")
        .and_then(Value::as_array)
        .ok_or_else(|| invalid("resident entrances absent"))?
    {
        let path = path_field(entrance, "dispatchCustody")?;
        let directory = path_field(entrance, "directory")?;
        let name = directory
            .file_name()
            .and_then(|n| n.to_str())
            .ok_or_else(|| invalid("route name absent"))?;
        if directory != app_dir.join("routes").join(name)
            || path != directory.join("dispatch-custody.json")
        {
            return Err(invalid("resident route custody differs from app routes"));
        }
        let mut file = open_operator_file(
            broker.root(),
            &[
                store,
                "host",
                "apps",
                app,
                "routes",
                name,
                "dispatch-custody.json",
            ],
            broker.operator_uid,
        )?;
        let mut bytes = Vec::new();
        Read::by_ref(&mut file)
            .take(MAX_CONFIG + 1)
            .read_to_end(&mut bytes)?;
        if bytes.len() as u64 > MAX_CONFIG {
            return Err(invalid("dispatch custody exceeds bound"));
        }
        seeds(&serde_json::from_slice::<Value>(&bytes)?, &mut needed)?;
    }
    for path in &needed {
        if !declared.contains(path) {
            return Err(invalid(format!(
                "resident home path needs root read-only inventory: {}",
                path.display()
            )));
        }
    }
    if declared.is_empty() {
        return Ok(String::new());
    }
    let mut selected = BTreeSet::new();
    let mut empty_parents = BTreeSet::new();
    for path in declared {
        if fs::symlink_metadata(path)?.is_file() || path == socket_parent {
            selected.insert(text(path)?.to_owned());
            if home(path) && fs::symlink_metadata(path)?.is_file() {
                let parent = path.parent().ok_or_else(|| invalid("visible file lacks parent"))?;
                if parent != socket_parent {
                    // Keep immediate-parent custody metadata without exposing
                    // its other contents. systemd mounts exact files atop this
                    // empty read-only directory, not the original directory.
                    let meta = fs::symlink_metadata(parent)?;
                    empty_parents.insert(format!("{}:ro,mode={:04o},uid={},gid={}", text(parent)?, meta.mode() & 0o777, meta.uid(), meta.gid()));
                }
            }
        }
    }
    let paths = selected.into_iter().collect::<Vec<_>>().join(" ");
    let parents = empty_parents.into_iter().collect::<Vec<_>>().join(" ");
    Ok(format!("# source-rendered exact operator visibility; app bwrap root remains isolated\n[Service]\nProtectHome=tmpfs\nTemporaryFileSystem={parents}\nBindReadOnlyPaths={paths}\n"))
}
fn seeds(value: &Value, needed: &mut BTreeSet<PathBuf>) -> io::Result<()> {
    for signer in value
        .get("signers")
        .and_then(Value::as_array)
        .ok_or_else(|| invalid("native custody signers absent"))?
    {
        let path = path_field(signer, "seedPath")?;
        if home(&path) {
            needed.insert(path);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn unit_path_injection_and_broad_paths_refuse() {
        for bad in [
            "/home",
            "/home/ember/../other/key",
            "/home/ember/a b",
            "/home/ember/%n",
            "/home/ember/key:other",
            "/home/ember/key\nUser=root",
            "relative/key",
        ] {
            assert!(text(Path::new(bad)).is_err(), "{bad}");
        }
        assert!(text(Path::new("/home/ember/a2/members/member-0/keys/mini.key")).is_ok());
    }
    #[test]
    fn protected_files_and_exact_socket_directories_only() {
        let parent = PathBuf::from(std::env::var_os("HOME").unwrap());
        let root = parent.join(format!(".spk-visibility-{}", std::process::id()));
        fs::create_dir(&root).unwrap();
        fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
        let file = root.join("key");
        fs::write(&file, b"owned").unwrap();
        fs::set_permissions(&file, fs::Permissions::from_mode(0o600)).unwrap();
        let uid = unsafe { libc::geteuid() };
        validate(std::slice::from_ref(&file), uid).unwrap();
        assert!(validate(std::slice::from_ref(&root), uid).is_err());
        let socket = root.join("operator.sock");
        let listener = UnixListener::bind(&socket).unwrap();
        fs::set_permissions(&socket, fs::Permissions::from_mode(0o600)).unwrap();
        validate(std::slice::from_ref(&root), uid).unwrap();
        assert!(validate(&[file.clone(), file.clone()], uid).is_err());
        let link = root.join("link");
        std::os::unix::fs::symlink(&file, &link).unwrap();
        assert!(validate(&[link], uid).is_err());
        fs::set_permissions(&file, fs::Permissions::from_mode(0o620)).unwrap();
        assert!(validate(&[file], uid).is_err());
        drop(listener);
        fs::remove_dir_all(root).unwrap();
    }
}
