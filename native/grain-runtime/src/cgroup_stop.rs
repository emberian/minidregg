//! Read-only physical snapshot of a controller or stopped worker subtree.
//! Callers exclude their own concurrent launches. This is not a freeze or a
//! claim against an administrator moving processes after the final observation.
use super::*;
use std::collections::BTreeMap;
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::fs::MetadataExt;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Identity {
    device: u64,
    inode: u64,
}
fn identity(file: &File) -> Result<Identity> {
    let stat = file
        .metadata()
        .map_err(|e| format!("controller cgroup metadata: {e}"))?;
    Ok(Identity {
        device: stat.dev(),
        inode: stat.ino(),
    })
}
fn child(parent: &File, name: &str, directory: bool) -> Result<File> {
    let name = std::ffi::CString::new(name).map_err(|_| "invalid cgroup entry name")?;
    let flags = libc::O_RDONLY
        | libc::O_CLOEXEC
        | libc::O_NOFOLLOW
        | if directory { libc::O_DIRECTORY } else { 0 };
    let fd = unsafe { libc::openat(parent.as_raw_fd(), name.as_ptr(), flags) };
    if fd < 0 {
        return Err(format!(
            "open controller cgroup entry: {}",
            io::Error::last_os_error()
        ));
    }
    Ok(unsafe { File::from_raw_fd(fd) })
}
fn read(parent: &File, name: &str) -> Result<String> {
    let file = child(parent, name, false)?;
    let mut value = String::new();
    file.take(65_537)
        .read_to_string(&mut value)
        .map_err(|e| format!("read cgroup {name}: {e}"))?;
    if value.len() > 65_536 {
        return Err("controller cgroup observation exceeds bound".into());
    }
    Ok(value)
}
fn empty_population(file: &File) -> Result<()> {
    let events = read(file, "cgroup.events")?;
    let values: Vec<_> = events
        .lines()
        .filter_map(|line| {
            let fields: Vec<_> = line.split_whitespace().collect();
            (fields.first() == Some(&"populated")).then_some(fields)
        })
        .collect();
    if values != vec![vec!["populated", "0"]] {
        return Err("controller descendant cgroup is populated or has invalid events".into());
    }
    if !read(file, "cgroup.procs")?.trim().is_empty() {
        return Err("controller descendant cgroup holds processes".into());
    }
    Ok(())
}
#[derive(Clone, Copy)]
enum RootPopulation<'a> {
    SoleController(u32),
    EmptyWorker,
    QuiescentController(&'a [u32]),
}
fn root_population(file: &File, expected: RootPopulation<'_>) -> Result<()> {
    match expected {
        RootPopulation::SoleController(pid) => {
            let procs = read(file, "cgroup.procs")?;
            if procs.split_whitespace().collect::<Vec<_>>() != vec![pid.to_string().as_str()] {
                return Err("controller cgroup does not contain only its current process".into());
            }
            Ok(())
        }
        RootPopulation::EmptyWorker => empty_population(file),
        RootPopulation::QuiescentController(expected) => {
            if process_ids(file)? != expected {
                return Err("controller process inventory changed during codec proof".into());
            }
            Ok(())
        }
    }
}
fn snapshot(
    file: &File,
    prefix: &Path,
    depth: usize,
    tree: &mut BTreeMap<PathBuf, Identity>,
    population: RootPopulation<'_>,
) -> Result<()> {
    if depth > 16 || tree.len() >= 256 {
        return Err("controller cgroup topology exceeds proof bound".into());
    }
    if depth == 0 {
        root_population(file, population)?;
    } else {
        empty_population(file)?;
    }
    tree.insert(prefix.to_owned(), identity(file)?);
    // fd-relative opens keep reads on the same directories if a path is replaced.
    let mut names = Vec::new();
    for entry in fs::read_dir(format!("/proc/self/fd/{}", file.as_raw_fd()))
        .map_err(|e| format!("controller cgroup directory: {e}"))?
    {
        let entry = entry.map_err(|e| format!("controller cgroup enumeration: {e}"))?;
        let kind = entry
            .file_type()
            .map_err(|e| format!("controller cgroup entry type: {e}"))?;
        if kind.is_symlink() {
            return Err("controller cgroup contains a symbolic link".into());
        }
        if kind.is_dir() {
            names.push(
                entry
                    .file_name()
                    .into_string()
                    .map_err(|_| "controller cgroup entry is not UTF-8")?,
            );
        }
    }
    names.sort();
    for name in names {
        let next = child(file, &name, true)?;
        snapshot(&next, &prefix.join(&name), depth + 1, tree, population)?;
    }
    Ok(())
}
fn open_root(path: &Path) -> Result<File> {
    OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(path)
        .map_err(|e| format!("open controller cgroup: {e}"))
}
fn prove_tree_with(
    path: &Path,
    population: RootPopulation<'_>,
    mut recheck: impl FnMut() -> Result<()>,
) -> Result<()> {
    recheck()?;
    let first = open_root(path)?;
    let mut before = BTreeMap::new();
    snapshot(&first, Path::new(""), 0, &mut before, population)?;
    recheck()?;
    let second = open_root(path)?;
    let mut after = BTreeMap::new();
    snapshot(&second, Path::new(""), 0, &mut after, population)?;
    if before != after {
        return Err("controller cgroup subtree changed during physical proof".into());
    }
    // Worker root.events aggregates every descendant, so this final empty
    // check also rejects late descendant population after the second traversal.
    root_population(&second, population)?;
    recheck()?;
    Ok(())
}
fn prove_with(path: &Path, pid: u32, recheck: impl FnMut() -> Result<()>) -> Result<()> {
    prove_tree_with(path, RootPopulation::SoleController(pid), recheck)
}
fn native_root(path: &Path) -> Result<File> {
    let root = open_root(path)?;
    let mut stat = std::mem::MaybeUninit::<libc::statfs>::uninit();
    if unsafe { libc::fstatfs(root.as_raw_fd(), stat.as_mut_ptr()) } != 0 {
        return Err(format!(
            "controller cgroup filesystem: {}",
            io::Error::last_os_error()
        ));
    }
    if unsafe { stat.assume_init() }.f_type as u64 != 0x6367_7270 {
        return Err("controller proof requires the actual cgroup v2 filesystem".into());
    }
    Ok(root)
}
pub(super) fn prove(path: &Path, task: &str) -> Result<()> {
    let root = native_root(path)?;
    let expected = identity(&root)?;
    prove_with(path, std::process::id(), || {
        if identity(&open_root(path)?)? != expected {
            return Err("controller cgroup identity changed during physical proof".into());
        }
        prove_controller_unit(task)
    })
}

// The cached local codec is not a signer, submitter or model worker. These
// exact two native entry points only serve Host pureCodec frames (7–11),
// without opening a Store. Do not generalize this to arbitrary descendants.
#[derive(Clone, Debug, PartialEq, Eq)]
struct CodecProcess {
    pid: u32,
    parent: u32,
    start: u64,
    uids: Vec<u32>,
    executable: Identity,
    arguments: Vec<Vec<u8>>,
    cgroup: String,
}

#[derive(Debug, PartialEq, Eq)]
struct FilePin {
    identity: Identity,
    uid: u32,
    mode: u32,
    size: u64,
    modified_seconds: i64,
    modified_nanoseconds: i64,
    changed_seconds: i64,
    changed_nanoseconds: i64,
}

fn file_pin(path: &Path) -> Result<FilePin> {
    pinned_file(path, true)
}

/// The Store's pinned settings: owned by the operator account, not root (dregg-infra lib.sh
/// `tenant_access`: an app grain's resident reads it inside its user namespace, where outside root
/// is unmapped). Its bytes are what the proof pins (hashed at admission and again at the end), so
/// any owner is accepted; group- and other-writable is still refused.
fn settings_pin(path: &Path) -> Result<FilePin> {
    pinned_file(path, false)
}

fn pinned_file(path: &Path, owned: bool) -> Result<FilePin> {
    let metadata = fs::symlink_metadata(path).map_err(|e| format!("codec file pin: {e}"))?;
    if !metadata.is_file()
        || (owned && ![0, unsafe { libc::geteuid() }].contains(&metadata.uid()))
        || metadata.mode() & 0o022 != 0
    {
        return Err(if owned {
            format!("codec pin {} is not an owned, non-shared-writable regular file", path.display())
        } else {
            format!("settings pin {} is not a non-shared-writable regular file", path.display())
        });
    }
    Ok(FilePin {
        identity: Identity {
            device: metadata.dev(),
            inode: metadata.ino(),
        },
        uid: metadata.uid(),
        mode: metadata.mode(),
        size: metadata.len(),
        modified_seconds: metadata.mtime(),
        modified_nanoseconds: metadata.mtime_nsec(),
        changed_seconds: metadata.ctime(),
        changed_nanoseconds: metadata.ctime_nsec(),
    })
}

#[derive(Debug, PartialEq, Eq)]
struct CodecHostPin {
    selected_path: PathBuf,
    configured: FilePin,
    selected: FilePin,
    sha256: String,
}

fn codec_host_pin(config: &Config, environment: Option<&std::ffi::OsStr>) -> Result<CodecHostPin> {
    // Runtime Mini calls supply no explicit --local-host/toolchain override.
    // Follow the same environment/fallback resolver as the launched client.
    let selected_path = mini_sdk::host_selection::select_semantic_host(None, environment, &config.host)
        .map_err(|e| e.to_string())?;
    let configured = file_pin(&config.host)?;
    let selected = file_pin(&selected_path)?;
    let sha256 = sha256_file(&config.host)?;
    if selected.size != configured.size
        || (selected.identity != configured.identity && sha256_file(&selected_path)? != sha256)
    {
        return Err("selected local codec Host differs from configured Host bytes".into());
    }
    if file_pin(&config.host)? != configured || file_pin(&selected_path)? != selected {
        return Err("local codec Host changed during byte-equivalence inspection".into());
    }
    Ok(CodecHostPin {
        selected_path,
        configured,
        selected,
        sha256,
    })
}

fn codec_host_unchanged(
    config: &Config,
    environment: Option<&std::ffi::OsStr>,
    original: &CodecHostPin,
) -> Result<bool> {
    // Hash both images once at admission; subsequent snapshots retain their
    // file identity, size, mode and mtime/ctime instead of rereading the images.
    let selected_path = mini_sdk::host_selection::select_semantic_host(None, environment, &config.host)
        .map_err(|e| e.to_string())?;
    Ok(selected_path == original.selected_path
        && file_pin(&config.host)? == original.configured
        && file_pin(&selected_path)? == original.selected)
}

fn process_ids(root: &File) -> Result<Vec<u32>> {
    let text = read(root, "cgroup.procs")?;
    let mut ids = text
        .split_whitespace()
        .map(|v| {
            v.parse::<u32>()
                .map_err(|_| "invalid cgroup PID".to_owned())
        })
        .collect::<Result<Vec<_>>>()?;
    ids.sort_unstable();
    if ids.contains(&0) || ids.windows(2).any(|p| p[0] == p[1]) {
        return Err("invalid or repeated cgroup PID".into());
    }
    Ok(ids)
}

fn stat_identity(bytes: &str) -> Result<(u32, u64)> {
    let fields: Vec<_> = bytes
        .rsplit_once(')')
        .ok_or("process stat command absent")?
        .1
        .split_whitespace()
        .collect();
    let parent = fields
        .get(1)
        .ok_or("process parent absent")?
        .parse()
        .map_err(|_| "invalid process parent")?;
    let start = fields
        .get(19)
        .ok_or("process start absent")?
        .parse()
        .map_err(|_| "invalid process start")?;
    Ok((parent, start))
}

fn unified_group(text: &str) -> Result<String> {
    let groups: Vec<_> = text.lines().filter_map(|v| v.strip_prefix("0::")).collect();
    if groups.len() != 1 {
        return Err("process requires one unified cgroup".into());
    }
    Ok(groups[0].into())
}

fn observe_codec_process(pid: u32) -> Result<CodecProcess> {
    let root = PathBuf::from(format!("/proc/{pid}"));
    let text = |name: &str| -> Result<String> {
        let bytes = bounded_regular_file(&root.join(name), 65_536)?;
        String::from_utf8(bytes).map_err(|_| "process metadata is not UTF-8".into())
    };
    let before = stat_identity(&text("stat")?)?;
    let status = text("status")?;
    let uid_line = status
        .lines()
        .find_map(|v| v.strip_prefix("Uid:"))
        .ok_or("process UIDs absent")?;
    let uids = uid_line
        .split_whitespace()
        .map(|v| {
            v.parse::<u32>()
                .map_err(|_| "invalid process UID".to_owned())
        })
        .collect::<Result<Vec<_>>>()?;
    let command = bounded_regular_file(&root.join("cmdline"), 65_536)?;
    if command.last() != Some(&0) {
        return Err("process argv terminator absent".into());
    }
    let arguments = command[..command.len() - 1]
        .split(|v| *v == 0)
        .map(|v| v.to_vec())
        .collect();
    let exe = File::open(root.join("exe")).map_err(|e| format!("process executable: {e}"))?;
    let executable = identity(&exe)?;
    let cgroup = unified_group(&text("cgroup")?)?;
    if before != stat_identity(&text("stat")?)? {
        return Err("process identity changed during observation".into());
    }
    Ok(CodecProcess {
        pid,
        parent: before.0,
        start: before.1,
        uids,
        executable,
        arguments,
        cgroup,
    })
}

fn validate_codec_pair(
    processes: &[CodecProcess],
    config: &Config,
    mini: &FilePin,
    host: &FilePin,
    selected_host: &Path,
    group: &str,
) -> Result<()> {
    use std::os::unix::ffi::OsStrExt;
    if processes.len() != 2 {
        return Err("controller must have either no codec or one complete codec pair".into());
    }
    let bytes = |p: &Path| p.as_os_str().as_bytes().to_vec();
    let supervisor_args = vec![
        bytes(&config.mini),
        b"codec-resident".to_vec(),
        b"--host".to_vec(),
        bytes(selected_host),
        b"--settings".to_vec(),
        bytes(&config.host_config),
    ];
    let host_args = vec![
        bytes(selected_host),
        bytes(&config.host_config),
        b"codec".to_vec(),
    ];
    let supervisor = processes
        .iter()
        .find(|p| p.arguments == supervisor_args && p.executable == mini.identity)
        .ok_or("controller extra process is not its exact configured codec supervisor")?;
    let codec = processes
        .iter()
        .find(|p| p.arguments == host_args && p.executable == host.identity)
        .ok_or("controller codec lacks its exact configured pure Host child")?;
    let uid = unsafe { libc::geteuid() };
    if supervisor.pid == codec.pid
        || supervisor.parent != 1
        || codec.parent != supervisor.pid
        || processes
            .iter()
            .any(|p| p.uids != vec![uid; 4] || p.start == 0 || p.cgroup != group)
    {
        return Err("codec pair UID, parent, process epoch or cgroup differs".into());
    }
    Ok(())
}

/// Completion inspection may retain exactly the configured stateless codec
/// supervisor and its pure Host child. Startup and preparation recovery still
/// use the stricter sole-controller proof; worker-subtree proofs remain empty.
pub(super) fn prove_quiescent_controller(config: &Config) -> Result<()> {
    prove_controller_unit(&config.task)?;
    let group =
        unified_group(&fs::read_to_string("/proc/self/cgroup").map_err(|e| e.to_string())?)?;
    if !group.ends_with(&format!("/mini-grain-controller@{}.service", config.task))
        || group.contains("..")
    {
        return Err("controller cgroup is not its configured unit".into());
    }
    let path = PathBuf::from(format!("/sys/fs/cgroup{group}"));
    let root = native_root(&path)?;
    let expected_root = identity(&root)?;
    let ids = process_ids(&root)?;
    let controller = std::process::id();
    if !ids.contains(&controller) {
        return Err("controller is absent from its cgroup".into());
    }
    if ids == [controller] {
        return prove(&path, &config.task);
    }
    if ids.len() != 3 {
        return Err("controller cgroup holds processes beyond one stateless codec pair".into());
    }
    let mini = file_pin(&config.mini)?;
    let local_host_environment = std::env::var_os("MINI_LOCAL_HOST");
    let host = codec_host_pin(config, local_host_environment.as_deref())?;
    let settings = settings_pin(&config.host_config)?;
    let settings_hash = sha256_bytes(&bounded_regular_file(&config.host_config, 1_048_576)?)?;
    let observe = || -> Result<Vec<CodecProcess>> {
        ids.iter()
            .filter(|pid| **pid != controller)
            .map(|pid| observe_codec_process(*pid))
            .collect()
    };
    let original = observe()?;
    validate_codec_pair(
        &original,
        config,
        &mini,
        &host.selected,
        &host.selected_path,
        &group,
    )?;
    prove_tree_with(&path, RootPopulation::QuiescentController(&ids), || {
        prove_controller_unit(&config.task)?;
        if identity(&open_root(&path)?)? != expected_root
            || file_pin(&config.mini)? != mini
            || std::env::var_os("MINI_LOCAL_HOST") != local_host_environment
            || !codec_host_unchanged(config, local_host_environment.as_deref(), &host)?
            || settings_pin(&config.host_config)? != settings
            || sha256_bytes(&bounded_regular_file(&config.host_config, 1_048_576)?)?
                != settings_hash
            || observe()? != original
        {
            return Err(
                "configured codec identity or source pins changed during physical proof".into(),
            );
        }
        Ok(())
    })
}

/// Prove zero processes at a stopped worker root and every descendant, on
/// actual cgroup v2. The caller rechecks the recorded unit identity, inactive
/// state, MainPID=0 and unchanged ControlGroup on each callback. Missing or
/// replaced roots are not treated as evidence of an empty worker subtree.
pub(super) fn prove_worker_empty(
    path: &Path,
    mut recheck_unit: impl FnMut() -> Result<()>,
) -> Result<()> {
    let root = native_root(path)?;
    let expected = identity(&root)?;
    prove_tree_with(path, RootPopulation::EmptyWorker, || {
        if identity(&open_root(path)?)? != expected {
            return Err("worker cgroup identity changed during physical proof".into());
        }
        recheck_unit()
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture() -> PathBuf {
        let root = std::env::temp_dir().join(format!(
            "mini-cgroup-proof-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&root).unwrap();
        fs::write(root.join("cgroup.procs"), b"123\n").unwrap();
        fs::create_dir(root.join("empty")).unwrap();
        fs::write(root.join("empty/cgroup.procs"), b"").unwrap();
        fs::write(root.join("empty/cgroup.events"), b"populated 0\nfrozen 0\n").unwrap();
        root
    }
    #[test]
    fn stopped_controller_accepts_empty_descendants() {
        let root = fixture();
        let mut checks = 0;
        assert!(prove_with(&root, 123, || {
            checks += 1;
            Ok(())
        })
        .is_ok());
        assert_eq!(checks, 3);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn populated_or_unreadable_descendant_refuses() {
        let root = fixture();
        fs::write(root.join("empty/cgroup.events"), b"populated 1\n").unwrap();
        assert!(prove_with(&root, 123, || Ok(())).is_err());
        fs::write(root.join("empty/cgroup.events"), b"populated 0\n").unwrap();
        fs::write(root.join("empty/cgroup.procs"), b"456\n").unwrap();
        assert!(prove_with(&root, 123, || Ok(())).is_err());
        fs::write(root.join("empty/cgroup.procs"), b"").unwrap();
        fs::set_permissions(
            root.join("empty/cgroup.events"),
            fs::Permissions::from_mode(0),
        )
        .unwrap();
        if unsafe { libc::geteuid() } != 0 {
            assert!(prove_with(&root, 123, || Ok(())).is_err());
        }
        fs::remove_file(root.join("empty/cgroup.events")).unwrap();
        assert!(prove_with(&root, 123, || Ok(())).is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn changed_topology_root_or_process_set_refuses() {
        for mutation in [0, 1, 2, 3] {
            let root = fixture();
            let mut checks = 0;
            let result = prove_with(&root, 123, || {
                checks += 1;
                if checks == 2 {
                    if mutation == 0 {
                        fs::rename(root.join("empty"), root.join("renamed")).unwrap();
                    } else if mutation == 1 {
                        fs::write(root.join("cgroup.procs"), b"123\n456\n").unwrap();
                    } else if mutation == 2 {
                        fs::remove_dir_all(root.join("empty")).unwrap();
                    } else {
                        fs::rename(root.join("empty"), root.join("previous")).unwrap();
                        fs::create_dir(root.join("empty")).unwrap();
                        fs::write(root.join("empty/cgroup.procs"), b"").unwrap();
                        fs::write(root.join("empty/cgroup.events"), b"populated 0\n").unwrap();
                    }
                }
                Ok(())
            });
            assert!(result.is_err(), "mutation {mutation}");
            fs::remove_dir_all(root).unwrap();
        }
    }
    #[test]
    fn late_population_identity_or_unit_change_refuses() {
        let root = fixture();
        let mut checks = 0;
        assert!(prove_with(&root, 123, || {
            checks += 1;
            if checks == 2 {
                fs::write(root.join("empty/cgroup.events"), b"populated 1\n").unwrap();
            }
            Ok(())
        })
        .is_err());
        fs::write(root.join("empty/cgroup.events"), b"populated 0\n").unwrap();
        assert!(prove_with(&root, 123, || Err("MainPID changed".into())).is_err());
        fs::remove_dir_all(root).unwrap();
    }
    fn codec_fixture(tag: &str) -> (PathBuf, Config, FilePin, FilePin, Vec<CodecProcess>) {
        use std::os::unix::ffi::OsStrExt;
        let (root, rt) = crate::tests::restart_resolution_fixture(tag);
        let config = rt.config.clone();
        let pin = |inode| FilePin {
            identity: Identity { device: 1, inode },
            uid: unsafe { libc::geteuid() },
            mode: 0o100500,
            size: 123,
            modified_seconds: 1,
            modified_nanoseconds: 0,
            changed_seconds: 1,
            changed_nanoseconds: 0,
        };
        let mini = pin(1);
        let host = pin(2);
        let b = |p: &Path| p.as_os_str().as_bytes().to_vec();
        let process = |pid, parent, executable, arguments| CodecProcess {
            pid,
            parent,
            start: 1,
            uids: vec![unsafe { libc::geteuid() }; 4],
            executable,
            arguments,
            cgroup: "/controller".into(),
        };
        let pair = vec![
            process(
                456,
                1,
                mini.identity.clone(),
                vec![
                    b(&config.mini),
                    b"codec-resident".to_vec(),
                    b"--host".to_vec(),
                    b(&config.host),
                    b"--settings".to_vec(),
                    b(&config.host_config),
                ],
            ),
            process(
                457,
                456,
                host.identity.clone(),
                vec![b(&config.host), b(&config.host_config), b"codec".to_vec()],
            ),
        ];
        drop(rt);
        (root, config, mini, host, pair)
    }

    #[test]
    fn quiescent_codec_accepts_only_exact_pure_pair_and_refuses_effect_roles() {
        let (root, config, mini, host, pair) = codec_fixture("codec-role-proof");
        validate_codec_pair(&pair, &config, &mini, &host, &config.host, "/controller").unwrap();
        assert!(validate_codec_pair(
            &pair[..1],
            &config,
            &mini,
            &host,
            &config.host,
            "/controller"
        )
        .is_err());
        let mut extra = pair.clone();
        extra.push(pair[0].clone());
        assert!(
            validate_codec_pair(&extra, &config, &mini, &host, &config.host, "/controller")
                .is_err()
        );
        for change in 0..9 {
            let mut bad = pair.clone();
            match change {
                0 => bad[0].arguments[1] = b"consent-resident".to_vec(),
                1 => bad[1].arguments[2] = b"stdio".to_vec(),
                2 => bad[1].parent = 999,
                3 => bad[0].parent = 999,
                4 => bad[0].uids[0] = unsafe { libc::geteuid() } + 1,
                5 => bad[1].executable.inode += 1,
                6 => bad[1].cgroup = "/other".into(),
                7 => bad[0].arguments[5] = b"/other/settings".to_vec(),
                _ => bad[1].start = 0,
            }
            assert!(
                validate_codec_pair(&bad, &config, &mini, &host, &config.host, "/controller")
                    .is_err(),
                "mutation {change}"
            );
        }
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn installed_codec_home_copy_matches_configured_base_host_by_bytes() {
        use std::os::unix::ffi::OsStrExt;
        let (root, mut config, _, _, mut pair) = codec_fixture("installed-codec-host");
        // Captured q2 diagnostic229/230: the installer emits MINI_LOCAL_HOST
        // under HOME while controller config retains BASE/bin/minidregg-host.
        // The supervisor uses BASE Mini; both processes use HOME settings.
        let base = root.join("base/bin");
        let home = root.join("home");
        fs::create_dir_all(&base).unwrap();
        fs::create_dir_all(home.join("bin")).unwrap();
        config.mini = base.join("mini");
        config.host = base.join("minidregg-host");
        config.host_config = home.join("host-config.json");
        let local_host = home.join("bin/minidregg-host");
        for path in [&config.mini, &config.host, &local_host] {
            fs::write(path, b"same reviewed executable").unwrap();
            fs::set_permissions(path, fs::Permissions::from_mode(0o500)).unwrap();
        }
        fs::write(&config.host_config, b"{}").unwrap();
        fs::set_permissions(&config.host_config, fs::Permissions::from_mode(0o600)).unwrap();
        let host = codec_host_pin(&config, Some(local_host.as_os_str())).unwrap();
        let mini = file_pin(&config.mini).unwrap();
        assert!(codec_host_unchanged(&config, Some(local_host.as_os_str()), &host).unwrap());
        assert!(!codec_host_unchanged(&config, None, &host).unwrap());
        assert_eq!(host.selected_path, local_host);
        assert_ne!(host.configured.identity, host.selected.identity);
        let bytes = |path: &Path| path.as_os_str().as_bytes().to_vec();
        pair[0].executable = mini.identity.clone();
        pair[0].arguments = vec![
            bytes(&config.mini),
            b"codec-resident".to_vec(),
            b"--host".to_vec(),
            bytes(&local_host),
            b"--settings".to_vec(),
            bytes(&config.host_config),
        ];
        pair[1].executable = host.selected.identity.clone();
        pair[1].arguments = vec![
            bytes(&local_host),
            bytes(&config.host_config),
            b"codec".to_vec(),
        ];
        validate_codec_pair(
            &pair,
            &config,
            &mini,
            &host.selected,
            &host.selected_path,
            "/controller",
        )
        .unwrap();
        assert!(validate_codec_pair(
            &pair,
            &config,
            &mini,
            &host.configured,
            &config.host,
            "/controller"
        )
        .is_err());
        assert_eq!(
            codec_host_pin(&config, Some(local_host.as_os_str())).unwrap(),
            host
        );

        // A copied replacement with identical bytes is still a new file epoch.
        let replacement = home.join("bin/replacement");
        fs::copy(&local_host, &replacement).unwrap();
        fs::rename(&replacement, &local_host).unwrap();
        let replaced = codec_host_pin(&config, Some(local_host.as_os_str())).unwrap();
        assert_ne!(replaced, host);
        assert!(!codec_host_unchanged(&config, Some(local_host.as_os_str()), &host).unwrap());
        assert!(validate_codec_pair(
            &pair,
            &config,
            &mini,
            &replaced.selected,
            &replaced.selected_path,
            "/controller"
        )
        .is_err());

        fs::set_permissions(&local_host, fs::Permissions::from_mode(0o700)).unwrap();
        // Same length defeats an accidental size-only equivalence check.
        fs::write(&local_host, b"evil reviewed executable").unwrap();
        assert!(!codec_host_unchanged(&config, Some(local_host.as_os_str()), &replaced).unwrap());
        assert!(codec_host_pin(&config, Some(local_host.as_os_str()))
            .unwrap_err()
            .contains("differs from configured Host bytes"));
        fs::write(&local_host, b"same reviewed executable").unwrap();
        fs::set_permissions(&local_host, fs::Permissions::from_mode(0o722)).unwrap();
        assert!(codec_host_pin(&config, Some(local_host.as_os_str())).is_err());
        fs::remove_file(&local_host).unwrap();
        std::os::unix::fs::symlink(&config.host, &local_host).unwrap();
        assert!(codec_host_pin(&config, Some(local_host.as_os_str())).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn codec_inventory_keeps_descendants_empty_and_detects_replacement() {
        let root = fixture();
        let ids = [123, 456, 457];
        fs::write(root.join("cgroup.procs"), b"457\n123\n456\n").unwrap();
        prove_tree_with(&root, RootPopulation::QuiescentController(&ids), || Ok(())).unwrap();
        assert!(
            prove_with(&root, 123, || Ok(())).is_err(),
            "startup remains sole-controller"
        );
        let mut calls = 0;
        assert!(
            prove_tree_with(&root, RootPopulation::QuiescentController(&ids), || {
                calls += 1;
                if calls == 2 {
                    fs::write(root.join("cgroup.procs"), b"123\n456\n458\n").unwrap();
                }
                Ok(())
            })
            .is_err()
        );
        fs::write(root.join("cgroup.procs"), b"123\n456\n457\n").unwrap();
        fs::write(root.join("empty/cgroup.procs"), b"789\n").unwrap();
        assert!(
            prove_tree_with(&root, RootPopulation::QuiescentController(&ids), || Ok(())).is_err()
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn codec_observation_reads_real_linux_process_identity() {
        let process = observe_codec_process(std::process::id()).unwrap();
        assert_eq!(process.pid, std::process::id());
        assert_eq!(process.uids, vec![unsafe { libc::geteuid() }; 4]);
        assert!(process.start > 0);
        assert!(!process.arguments.is_empty());
        assert_eq!(
            process.executable,
            identity(&File::open(std::env::current_exe().unwrap()).unwrap()).unwrap()
        );
        assert_eq!(
            process.cgroup,
            unified_group(&fs::read_to_string("/proc/self/cgroup").unwrap()).unwrap()
        );
    }

    #[test]
    fn codec_file_pin_refuses_aliases_and_detects_replaced_executable() {
        use std::os::unix::fs::symlink;
        let root = fixture();
        let path = root.join("program");
        write_new(&path, b"old").unwrap();
        let old = file_pin(&path).unwrap();
        let replacement = root.join("replacement");
        write_new(&replacement, b"new").unwrap();
        fs::rename(replacement, &path).unwrap();
        assert_ne!(file_pin(&path).unwrap(), old);
        symlink(&path, root.join("alias")).unwrap();
        assert!(file_pin(&root.join("alias")).is_err());
        assert_eq!(settings_pin(&path).unwrap(), file_pin(&path).unwrap());
        assert!(settings_pin(&root.join("alias")).is_err());
        fs::set_permissions(&path, fs::Permissions::from_mode(0o666)).unwrap();
        assert!(file_pin(&path).is_err());
        assert!(settings_pin(&path).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    fn worker_fixture() -> PathBuf {
        let root = fixture();
        fs::write(root.join("cgroup.procs"), b"").unwrap();
        fs::write(root.join("cgroup.events"), b"populated 0\nfrozen 0\n").unwrap();
        fs::create_dir(root.join("empty/nested")).unwrap();
        fs::write(root.join("empty/nested/cgroup.procs"), b"").unwrap();
        fs::write(root.join("empty/nested/cgroup.events"), b"populated 0\n").unwrap();
        root
    }
    #[test]
    fn stopped_worker_accepts_empty_root_and_nested_descendants() {
        let root = worker_fixture();
        let mut checks = 0;
        prove_tree_with(&root, RootPopulation::EmptyWorker, || {
            checks += 1;
            Ok(())
        })
        .unwrap();
        assert_eq!(checks, 3);
        // Zero is not a PID sentinel: the existing controller proof still
        // requires its one actual process, and worker proof requires none.
        assert!(prove_with(&root, 123, || Ok(())).is_err());
        fs::write(root.join("cgroup.procs"), b"0\n").unwrap();
        assert!(prove_tree_with(&root, RootPopulation::EmptyWorker, || Ok(())).is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn worker_root_or_nested_population_refuses() {
        for relative in ["", "empty", "empty/nested"] {
            let root = worker_fixture();
            let directory = root.join(relative);
            fs::write(directory.join("cgroup.events"), b"populated 1\n").unwrap();
            assert!(prove_tree_with(&root, RootPopulation::EmptyWorker, || Ok(())).is_err());
            fs::write(directory.join("cgroup.events"), b"populated 0\n").unwrap();
            fs::write(directory.join("cgroup.procs"), b"456\n").unwrap();
            assert!(prove_tree_with(&root, RootPopulation::EmptyWorker, || Ok(())).is_err());
            fs::remove_dir_all(root).unwrap();
        }
    }
    #[test]
    fn worker_symlink_missing_or_unreadable_observation_refuses() {
        use std::os::unix::fs::symlink;
        let root = worker_fixture();
        symlink("empty", root.join("alias")).unwrap();
        assert!(prove_tree_with(&root, RootPopulation::EmptyWorker, || Ok(())).is_err());
        fs::remove_file(root.join("alias")).unwrap();
        fs::remove_file(root.join("cgroup.events")).unwrap();
        symlink("empty/cgroup.events", root.join("cgroup.events")).unwrap();
        assert!(prove_tree_with(&root, RootPopulation::EmptyWorker, || Ok(())).is_err());
        fs::remove_file(root.join("cgroup.events")).unwrap();
        assert!(prove_tree_with(&root, RootPopulation::EmptyWorker, || Ok(())).is_err());
        fs::write(root.join("cgroup.events"), b"populated 0\n").unwrap();
        fs::set_permissions(root.join("cgroup.events"), fs::Permissions::from_mode(0)).unwrap();
        if unsafe { libc::geteuid() } != 0 {
            assert!(prove_tree_with(&root, RootPopulation::EmptyWorker, || Ok(())).is_err());
        }
        // Public entry point additionally rejects a synthetic non-cgroup root.
        assert!(prove_worker_empty(&root, || Ok(())).is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn worker_changed_inventory_population_or_unit_refuses() {
        for mutation in [0, 1, 2] {
            let root = worker_fixture();
            let mut checks = 0;
            let result = prove_tree_with(&root, RootPopulation::EmptyWorker, || {
                checks += 1;
                if checks == 2 {
                    match mutation {
                        0 => fs::rename(root.join("empty"), root.join("renamed")).unwrap(),
                        1 => fs::write(root.join("empty/nested/cgroup.procs"), b"456\n").unwrap(),
                        _ => return Err("worker unit identity changed".into()),
                    }
                }
                Ok(())
            });
            assert!(result.is_err(), "worker mutation {mutation}");
            fs::remove_dir_all(root).unwrap();
        }
        let root = worker_fixture();
        let mut checks = 0;
        assert!(prove_tree_with(&root, RootPopulation::EmptyWorker, || {
            checks += 1;
            if checks == 3 {
                Err("worker unit became active".into())
            } else {
                Ok(())
            }
        })
        .is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn worker_replaced_root_refuses() {
        let root = worker_fixture();
        let previous = root.with_extension("previous");
        let mut checks = 0;
        assert!(prove_tree_with(&root, RootPopulation::EmptyWorker, || {
            checks += 1;
            if checks == 2 {
                fs::rename(&root, &previous).unwrap();
                fs::create_dir(&root).unwrap();
                fs::write(root.join("cgroup.events"), b"populated 0\n").unwrap();
                fs::write(root.join("cgroup.procs"), b"").unwrap();
            }
            Ok(())
        })
        .is_err());
        fs::remove_dir_all(root).unwrap();
        fs::remove_dir_all(previous).unwrap();
    }
    #[test]
    #[ignore = "requires an isolated systemd user controller service"]
    fn native_scope_proves_empty_and_rejects_populated_descendant() {
        let task = std::env::var("MINI_CGROUP_TEST_TASK").expect("explicit fixture task");
        prove_prior_run_stopped(&task).unwrap();
        let line = fs::read_to_string("/proc/self/cgroup").unwrap();
        let group = line
            .lines()
            .find_map(|line| line.strip_prefix("0::"))
            .unwrap();
        let directory = PathBuf::from(format!("/sys/fs/cgroup{group}/proof-child"));
        fs::create_dir(&directory).unwrap();
        let result = (|| -> Result<()> {
            prove_prior_run_stopped(&task)?;
            let mut process = Command::new("/usr/bin/sleep")
                .arg("30")
                .spawn()
                .map_err(|e| e.to_string())?;
            let observed = (|| -> Result<()> {
                fs::write(directory.join("cgroup.procs"), process.id().to_string())
                    .map_err(|e| e.to_string())?;
                if prove_prior_run_stopped(&task).is_ok() {
                    return Err("populated native descendant was accepted".into());
                }
                Ok(())
            })();
            let _ = process.kill();
            let _ = process.wait();
            observed?;
            prove_prior_run_stopped(&task)
        })();
        fs::remove_dir(&directory).unwrap();
        result.unwrap();
        prove_prior_run_stopped(&task).unwrap();
    }
}
