//! Read-only physical snapshot of a controller or stopped worker subtree.
//! Callers exclude their own concurrent launches. This is not a freeze or a
//! claim against an administrator moving processes after the final observation.
use super::*;
use std::collections::BTreeMap;
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::fs::MetadataExt;

#[derive(Debug, PartialEq, Eq)]
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
enum RootPopulation {
    SoleController(u32),
    EmptyWorker,
}
fn root_population(file: &File, expected: RootPopulation) -> Result<()> {
    match expected {
        RootPopulation::SoleController(pid) => {
            let procs = read(file, "cgroup.procs")?;
            if procs.split_whitespace().collect::<Vec<_>>() != vec![pid.to_string().as_str()] {
                return Err("controller cgroup does not contain only its current process".into());
            }
            Ok(())
        }
        RootPopulation::EmptyWorker => empty_population(file),
    }
}
fn snapshot(
    file: &File,
    prefix: &Path,
    depth: usize,
    tree: &mut BTreeMap<PathBuf, Identity>,
    population: RootPopulation,
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
    population: RootPopulation,
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
        assert!(prove_with(&root, 123, || Ok(())).is_err());
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
