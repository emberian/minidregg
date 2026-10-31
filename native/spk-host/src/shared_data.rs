//! Operator custody for public, immutable application data. This is not an
//! authorization scheme: Mini admits the signed SPK; its exact signed attachment
//! selects an operator-published public inventory. Private data is not supported.
//!
//! Publication hashes every copied byte once. Protected receipts retain inode,
//! size, mode and timestamps; opening/rechecking a mount checks the complete tree
//! against those receipts without hashing multi-gigabyte data again. This trusts
//! the operator and filesystem custody, just like the protected SPK image store.
//! Mode bits do not stop a privileged operator rewriting both data and receipt.

use crate::io_context::IoContext;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{CStr, CString};
use std::fs::{self, File, Metadata};
use std::io::{self, Read, Write};
use std::os::fd::{AsFd, AsRawFd, BorrowedFd, FromRawFd};
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::{Component, Path, PathBuf};
use crate::canonical::hex;

pub const SIGNED_MEMBER: &str = "minidregg-data.json";
pub const MOUNT_TARGET: &str = "/opt/oracle-data";
pub const MAX_ATTACHMENT_BYTES: usize = 4096;
pub const MAX_INVENTORY_BYTES: usize = 1024 * 1024;
pub const MAX_FILES: usize = 4096;
pub const MAX_DATA_BYTES: u64 = 64 * 1024 * 1024 * 1024;
const MAX_RECEIPT_BYTES: usize = 32 * 1024 * 1024;
const MAX_DEPTH: usize = 16;
const MAX_PATH_BYTES: usize = 1024;
const MAX_NODES: usize = MAX_FILES * MAX_DEPTH + 1;
const INVENTORY_SCHEMA: &str = "minidregg-public-data-inventory-v1";
const ATTACHMENT_SCHEMA: &str = "minidregg-public-data-v1";
const RECEIPT_SCHEMA: &str = "minidregg-public-data-custody-v1";

fn invalid(reason: impl std::fmt::Display) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason.to_string())
}
fn digest(text: &str) -> io::Result<[u8; 32]> {
    if !crate::canonical::hex64(&text)
    {
        return Err(invalid(
            "digest must be 64 lowercase hexadecimal characters",
        ));
    }
    let mut result = [0; 32];
    for (i, pair) in text.as_bytes().chunks_exact(2).enumerate() {
        let digit = |b: u8| {
            if b.is_ascii_digit() {
                b - b'0'
            } else {
                b - b'a' + 10
            }
        };
        result[i] = digit(pair[0]) * 16 + digit(pair[1]);
    }
    Ok(result)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SharedDataRequirement {
    inventory_sha256: [u8; 32],
}
impl SharedDataRequirement {
    pub fn inventory_sha256(&self) -> [u8; 32] {
        self.inventory_sha256
    }
    pub fn inventory_sha256_hex(&self) -> String {
        hex(&self.inventory_sha256)
    }
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Attachment {
    schema: String,
    inventory_sha256: String,
}
pub fn parse_signed_attachment(bytes: &[u8]) -> io::Result<SharedDataRequirement> {
    if bytes.is_empty() || bytes.len() > MAX_ATTACHMENT_BYTES {
        return Err(invalid("public data attachment exceeds bound"));
    }
    let value: Attachment = serde_json::from_slice(bytes)?;
    if value.schema != ATTACHMENT_SCHEMA {
        return Err(invalid("unsupported public data attachment schema"));
    }
    Ok(SharedDataRequirement {
        inventory_sha256: digest(&value.inventory_sha256)?,
    })
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Inventory {
    schema: String,
    visibility: String,
    files: Vec<InventoryFile>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct InventoryFile {
    path: String,
    size: u64,
    sha256: String,
}
struct CheckedInventory {
    value: Inventory,
    requirement: SharedDataRequirement,
    total: u64,
    // Includes the data root (empty relative path) and every implied directory.
    expected: BTreeMap<String, NodeKind>,
    children: BTreeMap<String, BTreeSet<String>>,
}
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
enum NodeKind {
    Directory,
    File,
}

fn validate_path(path: &str) -> io::Result<()> {
    if path.is_empty() || path.len() > MAX_PATH_BYTES || path.split('/').count() > MAX_DEPTH {
        return Err(invalid("public data path length/depth exceeds bound"));
    }
    for part in path.split('/') {
        if part.is_empty()
            || matches!(part, "." | "..")
            || part.len() > 255
            || !part
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'-' | b'.'))
        {
            return Err(invalid("public data path is not normalized relative ASCII"));
        }
    }
    Ok(())
}
fn inventory(bytes: &[u8]) -> io::Result<CheckedInventory> {
    if bytes.is_empty() || bytes.len() > MAX_INVENTORY_BYTES {
        return Err(invalid("inventory exceeds bound"));
    }
    let value: Inventory = serde_json::from_slice(bytes)?;
    if value.schema != INVENTORY_SCHEMA
        || value.visibility != "public"
        || value.files.is_empty()
        || value.files.len() > MAX_FILES
    {
        return Err(invalid(
            "inventory must describe bounded, explicitly public data",
        ));
    }
    let mut expected = BTreeMap::from([(String::new(), NodeKind::Directory)]);
    let mut total = 0u64;
    let mut previous: Option<&str> = None;
    for file in &value.files {
        validate_path(&file.path)?;
        digest(&file.sha256)?;
        if previous.is_some_and(|old| old >= file.path.as_str()) {
            return Err(invalid("inventory paths must be sorted and unique"));
        }
        previous = Some(&file.path);
        total = total
            .checked_add(file.size)
            .ok_or_else(|| invalid("inventory size overflow"))?;
        if total > MAX_DATA_BYTES {
            return Err(invalid("public data exceeds operator size bound"));
        }
        let mut parent = String::new();
        let parts: Vec<_> = file.path.split('/').collect();
        for part in &parts[..parts.len() - 1] {
            if !parent.is_empty() {
                parent.push('/');
            }
            parent.push_str(part);
            if expected.insert(parent.clone(), NodeKind::Directory) == Some(NodeKind::File) {
                return Err(invalid("inventory file/directory collision"));
            }
        }
        if expected.insert(file.path.clone(), NodeKind::File).is_some() {
            return Err(invalid("inventory file/directory collision"));
        }
    }
    if expected.len() > MAX_NODES
        || expected.keys().map(String::len).sum::<usize>() > 16 * 1024 * 1024
    {
        return Err(invalid("inventory tree index exceeds bound"));
    }
    let mut children: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for path in expected.keys().filter(|path| !path.is_empty()) {
        let (parent, name) = path.rsplit_once('/').unwrap_or(("", path.as_str()));
        children
            .entry(parent.to_owned())
            .or_default()
            .insert(name.to_owned());
    }
    Ok(CheckedInventory {
        value,
        total,
        expected,
        children,
        requirement: SharedDataRequirement {
            inventory_sha256: Sha256::digest(bytes).into(),
        },
    })
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Identity {
    dev: u64,
    ino: u64,
    size: u64,
    uid: u32,
    gid: u32,
    mode: u32,
    links: u64,
    mtime: i64,
    mtime_nsec: i64,
    ctime: i64,
    ctime_nsec: i64,
}
impl Identity {
    fn of(meta: &Metadata) -> Self {
        // UID and GID can each become overflow values in the resident namespace.
        // Restore them only from the exact unchanged pre-entry held inode.
        let (uid,gid)=crate::namespace_identity::original_owner(meta).unwrap_or((meta.uid(),meta.gid()));
        Self {
            dev: meta.dev(),
            ino: meta.ino(),
            size: meta.len(),
            uid,
            gid,
            mode: meta.mode(),
            links: meta.nlink(),
            mtime: meta.mtime(),
            mtime_nsec: meta.mtime_nsec(),
            ctime: meta.ctime(),
            ctime_nsec: meta.ctime_nsec(),
        }
    }
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct NodeReceipt {
    path: String,
    kind: NodeKind,
    identity: Identity,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Receipt {
    schema: String,
    inventory_sha256: String,
    nodes: Vec<NodeReceipt>,
}

fn cstring(name: &str) -> io::Result<CString> {
    CString::new(name).map_err(invalid)
}
fn open_at(parent: &File, name: &str, flags: i32, mode: u32) -> io::Result<File> {
    let name = cstring(name)?;
    // SAFETY: name is terminated; successful openat transfers a new owned descriptor.
    let fd = unsafe {
        libc::openat(
            parent.as_raw_fd(),
            name.as_ptr(),
            flags | libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK,
            mode as libc::mode_t,
        )
    };
    if fd < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(unsafe { File::from_raw_fd(fd) })
    }
}
fn directory_at(parent: &File, name: &str) -> io::Result<File> {
    open_at(parent, name, libc::O_RDONLY | libc::O_DIRECTORY, 0)
}
fn mkdir_at(parent: &File, name: &str, mode: u32) -> io::Result<File> {
    let cname = cstring(name)?;
    if unsafe { libc::mkdirat(parent.as_raw_fd(), cname.as_ptr(), mode as libc::mode_t) } != 0 {
        return Err(io::Error::last_os_error());
    }
    directory_at(parent, name)
}
fn trusted(meta: &Metadata, app_uid: Option<u32>) -> bool {
    crate::namespace_identity::original_owner(meta).is_some_and(|(uid,_)| {
        (uid == 0 || uid == unsafe { libc::geteuid() }) && app_uid != Some(uid)
    }) && meta.permissions().mode() & 0o022 == 0
}
fn check_node(file: &File, kind: NodeKind, app_uid: Option<u32>) -> io::Result<Identity> {
    let meta = file.metadata()?;
    let correct = match kind {
        NodeKind::Directory => meta.is_dir() && meta.mode() & 0o7777 == 0o555,
        NodeKind::File => meta.is_file() && meta.nlink() == 1 && meta.mode() & 0o7777 == 0o444,
    };
    if !correct || !trusted(&meta, app_uid) {
        return Err(invalid("published data entry custody changed"));
    }
    Ok(Identity::of(&meta))
}
fn open_directory_path(path: &Path, protected: bool, app_uid: Option<u32>) -> io::Result<File> {
    if !path.is_absolute() {
        return Err(invalid("data directory must be absolute"));
    }
    let mut current = File::open("/").ctx("open", &"/")?;
    for part in path.components().skip(1) {
        let Component::Normal(part) = part else {
            return Err(invalid("directory path must be normalized"));
        };
        current = directory_at(
            &current,
            part.to_str()
                .ok_or_else(|| invalid("directory path is not UTF-8"))?,
        )?;
        if protected && !trusted(&current.metadata()?, app_uid) {
            return Err(invalid("operator data directory ancestry custody refused"));
        }
    }
    Ok(current)
}
fn open_store(path: &Path, create: bool, app_uid: Option<u32>) -> io::Result<File> {
    if create {
        let parent = path
            .parent()
            .ok_or_else(|| invalid("public data store parent absent"))?;
        let parent = open_directory_path(parent, true, app_uid)?;
        let name = path
            .file_name()
            .and_then(|v| v.to_str())
            .ok_or_else(|| invalid("public data store name absent"))?;
        match mkdir_at(&parent, name, 0o755) {
            Ok(created) => {
                // This dedicated registry contains deliberately public data.
                // mkdir's mode is filtered by umask; bubblewrap resolves the
                // passed directory FD through its backing pathname as the app.
                // Never widen an existing directory or any ancestor here.
                created.set_permissions(fs::Permissions::from_mode(0o755))?;
            }
            Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {}
            Err(e) => return Err(e),
        }
    }
    open_directory_path(path, true, app_uid)
}
fn open_relative(root: &File, path: &str, directory: bool) -> io::Result<File> {
    if path.is_empty() {
        return root.try_clone();
    }
    validate_path(path)?;
    let mut current = root.try_clone()?;
    let parts: Vec<_> = path.split('/').collect();
    for part in &parts[..parts.len() - 1] {
        current = directory_at(&current, part)?;
    }
    if directory {
        directory_at(&current, parts[parts.len() - 1])
    } else {
        open_at(&current, parts[parts.len() - 1], libc::O_RDONLY, 0)
    }
}
fn names(directory: &File) -> io::Result<BTreeSet<String>> {
    // Open a distinct description so readdir does not alter a retained directory's offset.
    let scan = directory_at(directory, ".")?;
    use std::os::fd::IntoRawFd;
    let fd = scan.into_raw_fd();
    let dir = unsafe { libc::fdopendir(fd) };
    if dir.is_null() {
        unsafe {
            libc::close(fd);
        }
        return Err(io::Error::last_os_error());
    }
    struct Directory(*mut libc::DIR);
    impl Drop for Directory {
        fn drop(&mut self) {
            unsafe {
                libc::closedir(self.0);
            }
        }
    }
    let _close = Directory(dir);
    let mut result = BTreeSet::new();
    loop {
        unsafe {
            *libc::__errno_location() = 0;
        }
        let entry = unsafe { libc::readdir(dir) };
        if entry.is_null() {
            let errno = io::Error::last_os_error();
            if errno.raw_os_error() != Some(0) {
                return Err(errno);
            }
            break;
        }
        let name = unsafe { CStr::from_ptr((*entry).d_name.as_ptr()) }
            .to_str()
            .map_err(invalid)?;
        if matches!(name, "." | "..") {
            continue;
        }
        if result.len() >= MAX_FILES + 3 {
            return Err(invalid("directory entry count exceeds bound"));
        }
        result.insert(name.to_owned());
    }
    Ok(result)
}
fn read_fixed(
    parent: &File,
    name: &str,
    max: usize,
    app_uid: Option<u32>,
) -> io::Result<(Vec<u8>, Identity)> {
    let mut file = open_at(parent, name, libc::O_RDONLY, 0)?;
    let identity = check_node(&file, NodeKind::File, app_uid)?;
    if identity.size == 0 || identity.size > max as u64 {
        return Err(invalid("published metadata exceeds bound"));
    }
    let mut bytes = Vec::new();
    Read::by_ref(&mut file)
        .take(max as u64 + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 != identity.size || Identity::of(&file.metadata()?) != identity {
        return Err(invalid("published metadata mutated while reading"));
    }
    Ok((bytes, identity))
}
fn write_fixed(parent: &File, name: &str, bytes: &[u8]) -> io::Result<()> {
    let mut file = open_at(
        parent,
        name,
        libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL,
        0o600,
    )?;
    file.write_all(bytes)?;
    file.set_permissions(fs::Permissions::from_mode(0o444))?;
    Ok(())
}
fn stream_hash(
    file: &mut File,
    mut output: Option<&mut File>,
    expected_size: u64,
) -> io::Result<[u8; 32]> {
    let before = file.metadata()?;
    if !before.is_file() || before.len() != expected_size {
        return Err(invalid("data file size/type differs from inventory"));
    }
    let identity = Identity::of(&before);
    let mut hash = Sha256::new();
    let mut size = 0u64;
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let n = file.read(&mut buffer)?;
        if n == 0 {
            break;
        }
        size = size
            .checked_add(n as u64)
            .ok_or_else(|| invalid("data file size overflow"))?;
        if size > expected_size {
            return Err(invalid("data file grew while copying"));
        }
        hash.update(&buffer[..n]);
        if let Some(out) = output.as_deref_mut() {
            out.write_all(&buffer[..n])?;
        }
    }
    if size != expected_size || Identity::of(&file.metadata()?) != identity {
        return Err(invalid("data file mutated while copying"));
    }
    Ok(hash.finalize().into())
}

fn collect_tree(
    root: &File,
    checked: &CheckedInventory,
    app_uid: Option<u32>,
) -> io::Result<Vec<NodeReceipt>> {
    let mut nodes = Vec::with_capacity(checked.expected.len());
    for (path, kind) in &checked.expected {
        let node = open_relative(root, path, *kind == NodeKind::Directory)?;
        let identity = check_node(&node, *kind, app_uid)?;
        if *kind == NodeKind::Directory {
            let empty = BTreeSet::new();
            let expected = checked.children.get(path).unwrap_or(&empty);
            if names(&node)? != *expected {
                return Err(invalid("published data has missing or extra entries"));
            }
        } else {
            let expected = checked
                .value
                .files
                .binary_search_by(|file| file.path.as_str().cmp(path.as_str()))
                .map_err(|_| invalid("unlisted data file"))?;
            if identity.size != checked.value.files[expected].size {
                return Err(invalid("published data length differs from inventory"));
            }
        }
        nodes.push(NodeReceipt {
            path: path.clone(),
            kind: *kind,
            identity,
        });
    }
    Ok(nodes)
}

#[derive(Debug, Serialize)]
pub struct PublishedDataset {
    pub schema: &'static str,
    pub inventory_sha256: String,
    pub directory: PathBuf,
    pub total_bytes: u64,
    pub file_count: usize,
    pub reused: bool,
}
fn result(store: &Path, checked: &CheckedInventory, reused: bool) -> PublishedDataset {
    PublishedDataset {
        schema: "mini-spk-public-data-publication-v1",
        inventory_sha256: checked.requirement.inventory_sha256_hex(),
        directory: store.join(format!(
            "sha256-{}",
            checked.requirement.inventory_sha256_hex()
        )),
        total_bytes: checked.total,
        file_count: checked.value.files.len(),
        reused,
    }
}
/// Stream verified copies into a new publication. Sources may be hardlinked, but
/// destination files are independent, single-link copies. No source URL is fetched.
/// Existing exact publications are checked and reused; failed named stages remain
/// for the operator to inspect, and are identified in the error. No GC runs here.
pub fn publish(
    store: &Path,
    source: &Path,
    inventory_bytes: &[u8],
) -> io::Result<PublishedDataset> {
    let checked = inventory(inventory_bytes)?;
    let store_fd = open_store(store, true, None)?;
    let lock = open_at(
        &store_fd,
        ".publish.lock",
        libc::O_RDWR | libc::O_CREAT,
        0o600,
    )?;
    let lock_meta = lock.metadata()?;
    if !lock_meta.is_file()
        || lock_meta.nlink() != 1
        || !trusted(&lock_meta, None)
        || lock_meta.mode() & 0o7777 != 0o600
    {
        return Err(invalid("public data publication lock custody refused"));
    }
    if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let final_name = format!("sha256-{}", checked.requirement.inventory_sha256_hex());
    match directory_at(&store_fd, &final_name) {
        Ok(_) => {
            open_published_internal(store, &checked.requirement, None)?.recheck()?;
            return Ok(result(store, &checked, true));
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        Err(e) => return Err(e),
    }
    let source_fd = open_directory_path(source, false, None)?;
    let mut space = std::mem::MaybeUninit::<libc::statvfs>::uninit();
    if unsafe { libc::fstatvfs(store_fd.as_raw_fd(), space.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let space = unsafe { space.assume_init() };
    if u128::from(space.f_bavail) * u128::from(space.f_frsize)
        < u128::from(checked.total) + MAX_RECEIPT_BYTES as u128 + MAX_INVENTORY_BYTES as u128
    {
        return Err(invalid(
            "insufficient public data publication workspace (preflight, not reservation)",
        ));
    }
    let mut random = [0u8; 16];
    File::open("/dev/urandom").ctx("open", &"/dev/urandom")?.read_exact(&mut random)?;
    let stage_name = format!(".publish-{}-{}", std::process::id(), hex(&random));
    let stage = mkdir_at(&store_fd, &stage_name, 0o700)?;
    let attempt = (|| -> io::Result<()> {
        let data = mkdir_at(&stage, "data", 0o700)?;
        for (path, kind) in &checked.expected {
            if path.is_empty() || *kind != NodeKind::Directory {
                continue;
            }
            let (parent, name) = path.rsplit_once('/').unwrap_or(("", path.as_str()));
            let parent = open_relative(&data, parent, true)?;
            mkdir_at(&parent, name, 0o700)?;
        }
        for spec in &checked.value.files {
            let mut input = open_relative(&source_fd, &spec.path, false)?;
            let (parent, name) = spec
                .path
                .rsplit_once('/')
                .unwrap_or(("", spec.path.as_str()));
            let parent = open_relative(&data, parent, true)?;
            let mut output = open_at(
                &parent,
                name,
                libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL,
                0o600,
            )?;
            if stream_hash(&mut input, Some(&mut output), spec.size)? != digest(&spec.sha256)? {
                return Err(invalid(format!(
                    "source hash differs from inventory: {}",
                    spec.path
                )));
            }
            output.set_permissions(fs::Permissions::from_mode(0o444))?;
        }
        for (path, kind) in checked.expected.iter().rev() {
            if *kind == NodeKind::Directory {
                let dir = open_relative(&data, path, true)?;
                dir.set_permissions(fs::Permissions::from_mode(0o555))?;
            }
        }
        let receipt = Receipt {
            schema: RECEIPT_SCHEMA.into(),
            inventory_sha256: checked.requirement.inventory_sha256_hex(),
            nodes: collect_tree(&data, &checked, None)?,
        };
        let receipt_bytes = serde_json::to_vec(&receipt)?;
        if receipt_bytes.len() > MAX_RECEIPT_BYTES {
            return Err(invalid("publication receipt exceeds bound"));
        }
        write_fixed(&stage, "inventory.json", inventory_bytes)?;
        write_fixed(&stage, "receipt.json", &receipt_bytes)?;
        stage.set_permissions(fs::Permissions::from_mode(0o555))?;
        let from = cstring(&stage_name)?;
        let to = cstring(&final_name)?;
        if unsafe {
            libc::syscall(
                libc::SYS_renameat2,
                store_fd.as_raw_fd(),
                from.as_ptr(),
                store_fd.as_raw_fd(),
                to.as_ptr(),
                libc::RENAME_NOREPLACE,
            )
        } != 0
        {
            return Err(io::Error::last_os_error());
        }
        Ok(())
    })();
    attempt.map_err(|error| {
        io::Error::new(
            error.kind(),
            format!(
                "{error}; publication attempt {} (no automatic cleanup/retry)",
                store.join(&stage_name).display()
            ),
        )
    })?;
    open_published_internal(store, &checked.requirement, None)?.recheck()?;
    Ok(result(store, &checked, false))
}

/// Pins one immutable public revision by file descriptors. A new revision has a
/// new inventory hash; publication never changes this handle or removes old data.
pub struct SharedDataHandle {
    publication: File,
    root: File,
    checked: CheckedInventory,
    nodes: Vec<NodeReceipt>,
    inventory_identity: Identity,
    receipt_identity: Identity,
    app_uid: Option<u32>,
}
impl SharedDataHandle {
    pub fn root_fd(&self) -> BorrowedFd<'_> {
        self.root.as_fd()
    }
    pub fn inventory_sha256(&self) -> [u8; 32] {
        self.checked.requirement.inventory_sha256()
    }
    /// Recheck complete tree and metadata custody immediately before passing the
    /// read-only directory descriptor into the sandbox. This does not read payloads.
    pub fn recheck(&self) -> io::Result<()> {
        check_node(&self.publication, NodeKind::Directory, self.app_uid)?;
        if names(&self.publication)?
            != BTreeSet::from([
                "data".to_owned(),
                "inventory.json".to_owned(),
                "receipt.json".to_owned(),
            ])
        {
            return Err(invalid("publication has missing or extra metadata"));
        }
        let named_root = directory_at(&self.publication, "data")?;
        let root_meta = self.root.metadata()?;
        let named_meta = named_root.metadata()?;
        if (root_meta.dev(), root_meta.ino()) != (named_meta.dev(), named_meta.ino()) {
            return Err(invalid("published data root was replaced"));
        }
        for (name, expected) in [
            ("inventory.json", &self.inventory_identity),
            ("receipt.json", &self.receipt_identity),
        ] {
            let file = open_at(&self.publication, name, libc::O_RDONLY, 0)?;
            if check_node(&file, NodeKind::File, self.app_uid)? != *expected {
                return Err(invalid("publication metadata was replaced or mutated"));
            }
        }
        if collect_tree(&self.root, &self.checked, self.app_uid)? != self.nodes {
            return Err(invalid("published data identity or timestamps changed"));
        }
        Ok(())
    }
}
pub fn open_published(
    store: &Path,
    requirement: &SharedDataRequirement,
    app_uid: u32,
) -> io::Result<SharedDataHandle> {
    if app_uid == 0 || app_uid == unsafe { libc::geteuid() } {
        return Err(invalid(
            "application UID must differ from root and operator",
        ));
    }
    open_published_internal(store, requirement, Some(app_uid))
}
fn open_published_internal(
    store: &Path,
    requirement: &SharedDataRequirement,
    app_uid: Option<u32>,
) -> io::Result<SharedDataHandle> {
    let store_fd = open_store(store, false, app_uid)?;
    let publication = directory_at(
        &store_fd,
        &format!("sha256-{}", requirement.inventory_sha256_hex()),
    )?;
    check_node(&publication, NodeKind::Directory, app_uid)?;
    let (bytes, inventory_identity) =
        read_fixed(&publication, "inventory.json", MAX_INVENTORY_BYTES, app_uid)?;
    let checked = inventory(&bytes)?;
    if checked.requirement != *requirement {
        return Err(invalid(
            "published inventory differs from signed attachment digest",
        ));
    }
    let (receipt_bytes, receipt_identity) =
        read_fixed(&publication, "receipt.json", MAX_RECEIPT_BYTES, app_uid)?;
    let receipt: Receipt = serde_json::from_slice(&receipt_bytes)?;
    if receipt.schema != RECEIPT_SCHEMA
        || receipt.inventory_sha256 != requirement.inventory_sha256_hex()
        || receipt.nodes.len() != checked.expected.len()
    {
        return Err(invalid("public data receipt differs from inventory"));
    }
    let root = directory_at(&publication, "data")?;
    let actual = collect_tree(&root, &checked, app_uid)?;
    if actual != receipt.nodes {
        return Err(invalid("public data publication receipt identity differs"));
    }
    let handle = SharedDataHandle {
        publication,
        root,
        checked,
        nodes: actual,
        inventory_identity,
        receipt_identity,
        app_uid,
    };
    handle.recheck()?;
    Ok(handle)
}
/// Optional operator audit: re-hash payloads, including bit-rot which metadata
/// checks cannot detect. Auditing does not repair, republish, or delete anything.
pub fn audit(store: &Path, requirement: &SharedDataRequirement, app_uid: u32) -> io::Result<()> {
    let handle = open_published(store, requirement, app_uid)?;
    for spec in &handle.checked.value.files {
        let mut file = open_relative(&handle.root, &spec.path, false)?;
        if stream_hash(&mut file, None, spec.size)? != digest(&spec.sha256)? {
            return Err(invalid(format!(
                "published data hash differs: {}",
                spec.path
            )));
        }
    }
    handle.recheck()
}

#[cfg(test)]
mod tests {
    use super::*;
    struct Fixture {
        base: PathBuf,
        source: PathBuf,
        store: PathBuf,
    }
    impl Fixture {
        fn new() -> Self {
            let home =
                PathBuf::from(std::env::var_os("HOME").expect("tests require protected HOME"));
            let mut random = [0u8; 8];
            File::open("/dev/urandom")
                .unwrap()
                .read_exact(&mut random)
                .unwrap();
            let base = home.join(format!(
                ".shared-data-test-{}-{}",
                std::process::id(),
                hex(&random)
            ));
            fs::create_dir(&base).unwrap();
            fs::set_permissions(&base, fs::Permissions::from_mode(0o700)).unwrap();
            let source = base.join("source");
            fs::create_dir(&source).unwrap();
            Self {
                store: base.join("public-data"),
                base,
                source,
            }
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            fn writable(path: &Path) {
                if fs::symlink_metadata(path).is_ok_and(|m| m.is_dir()) {
                    let _ = fs::set_permissions(path, fs::Permissions::from_mode(0o700));
                    if let Ok(entries) = fs::read_dir(path) {
                        for entry in entries.flatten() {
                            writable(&entry.path());
                        }
                    }
                }
            }
            writable(&self.base);
            let _ = fs::remove_dir_all(&self.base);
        }
    }
    fn bytes(files: &[(&str, &[u8])]) -> Vec<u8> {
        serde_json::to_vec(&serde_json::json!({"schema":INVENTORY_SCHEMA,"visibility":"public","files":files.iter().map(|(path,data)|
            serde_json::json!({"path":path,"size":data.len(),"sha256":hex(&Sha256::digest(data))})).collect::<Vec<_>>()})).unwrap()
    }
    fn app_uid() -> u32 {
        unsafe { libc::geteuid() }.checked_add(1).unwrap()
    }
    #[test]
    fn declarations_and_inventory_have_closed_bounded_shapes() {
        let hash = "a".repeat(64);
        let valid = format!(r#"{{"schema":"{ATTACHMENT_SCHEMA}","inventory_sha256":"{hash}"}}"#);
        assert!(parse_signed_attachment(valid.as_bytes()).is_ok());
        for bad in [
            format!(
                r#"{{"schema":"{ATTACHMENT_SCHEMA}","inventory_sha256":"{hash}","url":"https://example.invalid"}}"#
            ),
            format!(
                r#"{{"schema":"{ATTACHMENT_SCHEMA}","inventory_sha256":"{hash}","inventory_sha256":"{hash}"}}"#
            ),
            valid.replace(&hash, &hash.to_uppercase()),
        ] {
            assert!(parse_signed_attachment(bad.as_bytes()).is_err());
        }
        assert!(parse_signed_attachment(&vec![b' '; MAX_ATTACHMENT_BYTES + 1]).is_err());
        for path in [
            "../escape",
            "/absolute",
            "a//b",
            "a/./b",
            "a\\b",
            "a b",
            "a:",
            ".",
            "",
            "a/../b",
        ] {
            assert!(inventory(&bytes(&[(path, b"x")])).is_err(), "{path:?}");
        }
        assert!(inventory(&bytes(&[("z", b"x"), ("a", b"x")])).is_err());
        assert!(inventory(&bytes(&[("a", b"x"), ("a/b", b"x")])).is_err());
        assert!(inventory(&bytes(&[("a", b"x"), ("a", b"x")])).is_err());
        let private = String::from_utf8(bytes(&[("a", b"x")]))
            .unwrap()
            .replace("public\"", "private\"");
        assert!(inventory(private.as_bytes()).is_err());
    }
    #[test]
    fn source_hardlinks_become_independent_verified_public_files_and_reuse_is_safe() {
        let f = Fixture::new();
        fs::write(f.source.join("a"), b"public bytes").unwrap();
        fs::hard_link(f.source.join("a"), f.source.join("b")).unwrap();
        let data = bytes(&[("a", b"public bytes"), ("b", b"public bytes")]);
        let checked = inventory(&data).unwrap();
        let published = publish(&f.store, &f.source, &data).unwrap();
        assert!(!published.reused);
        let a = fs::metadata(published.directory.join("data/a")).unwrap();
        let b = fs::metadata(published.directory.join("data/b")).unwrap();
        assert_eq!((a.nlink(), b.nlink()), (1, 1));
        assert_ne!(a.ino(), b.ino());
        assert_eq!(
            fs::read(published.directory.join("inventory.json")).unwrap(),
            data
        );
        let held = open_published(&f.store, &checked.requirement, app_uid()).unwrap();
        held.recheck().unwrap();
        audit(&f.store, &checked.requirement, app_uid()).unwrap();
        assert!(
            publish(&f.store, Path::new("/source-no-longer-present"), &data)
                .unwrap()
                .reused
        );
        fs::write(f.source.join("a"), b"new public bytes").unwrap();
        let next = bytes(&[("a", b"new public bytes"), ("b", b"new public bytes")]);
        let replacement = publish(&f.store, &f.source, &next).unwrap();
        assert_ne!(published.inventory_sha256, replacement.inventory_sha256);
        held.recheck().unwrap();
        assert_eq!(
            fs::read(published.directory.join("data/a")).unwrap(),
            b"public bytes"
        );
    }
    #[test]
    fn bad_copy_does_not_publish_or_destroy_source_and_keeps_named_attempt() {
        let f = Fixture::new();
        fs::write(f.source.join("a"), b"actual").unwrap();
        let data = bytes(&[("a", b"forged")]);
        let error = publish(&f.store, &f.source, &data).unwrap_err().to_string();
        assert!(error.contains("source hash differs"));
        assert!(error.contains("publication attempt"));
        assert!(!f
            .store
            .join(format!("sha256-{}", hex(&Sha256::digest(&data))))
            .exists());
        assert_eq!(fs::read(f.source.join("a")).unwrap(), b"actual");
        assert!(fs::read_dir(&f.store)
            .unwrap()
            .flatten()
            .any(|e| e.file_name().to_string_lossy().starts_with(".publish-")));
    }
    #[test]
    #[ignore = "writes a 513 MiB independent destination; run explicitly in bounded Linux fixture"]
    fn member_larger_than_spk_data_limit_streams_without_archive_sized_allocation() {
        let f = Fixture::new();
        let size = 513u64 * 1024 * 1024;
        File::create(f.source.join("large.sqlite"))
            .unwrap()
            .set_len(size)
            .unwrap();
        let buffer = [0u8; 64 * 1024];
        let mut hash = Sha256::new();
        for _ in 0..size / buffer.len() as u64 {
            hash.update(buffer);
        }
        let data=serde_json::to_vec(&serde_json::json!({"schema":INVENTORY_SCHEMA,"visibility":"public","files":[{"path":"large.sqlite","size":size,"sha256":hex(&hash.finalize())}]})).unwrap();
        let published = publish(&f.store, &f.source, &data).unwrap();
        assert_eq!(published.total_bytes, size);
        let checked = inventory(&data).unwrap();
        open_published(&f.store, &checked.requirement, app_uid())
            .unwrap()
            .recheck()
            .unwrap();
        assert_eq!(
            fs::metadata(published.directory.join("data/large.sqlite"))
                .unwrap()
                .len(),
            size
        );
    }
}
