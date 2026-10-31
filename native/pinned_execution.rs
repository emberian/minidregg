//! Shared Linux sealed image/settings execution. Byte custody only: this module
//! does not select source authority or interpret a native verifier's output.
//! The kernel, dynamic loader/runtime and fixed timeout executable remain trusted.
// Non-Linux builds compile only the refusals.
#![cfg_attr(not(target_os = "linux"), allow(dead_code, unused_imports))]
use sha2::{Digest, Sha256};
use std::{
    fs::File,
    io::{Read, Result, Write},
    path::Path,
    process::{Command, Stdio},
};
pub const MAX_IMAGE: u64 = 128 * 1024 * 1024;
const MAX_SETTINGS: usize = 16 * 1024 * 1024;
fn bad(s: &str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidData, s)
}
/// Files cannot escape independently of the synchronous child lifetime.
pub struct SealedInvocation {
    image: File,
    settings: File,
}
/// Copy `source` (at most `maximum` bytes) into a sealed memfd, rewound for
/// reading. The one copy of this mechanism: private-backend's `SealedInvocation`
/// and resource-client's Host launch both execute these descriptors.
#[cfg(target_os = "linux")]
pub fn snapshot<R: Read>(source: R, executable: bool, maximum: u64) -> Result<File> {
    use std::{
        io::{Seek, SeekFrom},
        os::fd::FromRawFd,
    };
    let base = libc::MFD_CLOEXEC | libc::MFD_ALLOW_SEALING;
    let intent = if executable { 0x10 } else { 0x08 };
    let name = if executable {
        c"mini-pinned-image"
    } else {
        c"mini-pinned-settings"
    };
    let mut fd = unsafe { libc::memfd_create(name.as_ptr(), base | intent) };
    if fd < 0 && std::io::Error::last_os_error().raw_os_error() == Some(libc::EINVAL) {
        fd = unsafe { libc::memfd_create(name.as_ptr(), base) };
    }
    if fd < 0 {
        return Err(std::io::Error::last_os_error());
    }
    let mut held = unsafe { File::from_raw_fd(fd) };
    if unsafe { libc::fchmod(fd, if executable { 0o700 } else { 0o400 }) } != 0 {
        return Err(std::io::Error::last_os_error());
    }
    let n = std::io::copy(&mut source.take(maximum + 1), &mut held)?;
    if n > maximum {
        return Err(bad("sealed execution snapshot capacity"));
    }
    let seals = libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL;
    if unsafe { libc::fcntl(fd, libc::F_ADD_SEALS, seals) } != 0 {
        return Err(std::io::Error::last_os_error());
    }
    held.seek(SeekFrom::Start(0))?;
    Ok(held)
}
impl SealedInvocation {
    /// Copy then SEAL then hash. A writer racing the copy can cause refusal,
    /// but cannot change an admitted snapshot after digest verification.
    /// Settings bytes must come from the caller's protected original profile.
    pub fn new(
        program: &Path,
        expected_image: &[u8; 32],
        expected_settings: &[u8],
    ) -> Result<Self> {
        #[cfg(not(target_os = "linux"))]
        {
            let _ = (program, expected_image, expected_settings);
            return Err(bad("sealed execution requires Linux"));
        }
        #[cfg(target_os = "linux")]
        {
            if expected_settings.is_empty() || expected_settings.len() > MAX_SETTINGS {
                return Err(bad("sealed settings capacity"));
            }
            let source = File::open(program)?;
            if !source.metadata()?.is_file() || source.metadata()?.len() > MAX_IMAGE {
                return Err(bad("sealed image must be bounded regular file"));
            }
            let mut image = snapshot(source, true, MAX_IMAGE)?;
            let mut hash = Sha256::new();
            let mut buf = [0; 65536];
            loop {
                let n = image.read(&mut buf)?;
                if n == 0 {
                    break;
                }
                hash.update(&buf[..n]);
            }
            if hash.finalize().as_slice() != expected_image {
                return Err(bad("sealed image digest refused"));
            }
            let settings = snapshot(
                std::io::Cursor::new(expected_settings),
                false,
                MAX_SETTINGS as u64,
            )?;
            Ok(Self { image, settings })
        }
    }
    /// The original settings FD is the FIRST native argument. Other fixed
    /// operator arguments follow. Request bytes and captured response are bounded;
    /// paths, roster/policy and successful-byte meanings remain caller-owned.
    pub fn output_with_input(
        &self,
        arguments: &[String],
        input: &[u8],
        timeout_seconds: u16,
        maximum_input: usize,
        maximum_output: usize,
    ) -> Result<Vec<u8>> {
        #[cfg(not(target_os = "linux"))]
        {
            let _ = (
                arguments,
                input,
                timeout_seconds,
                maximum_input,
                maximum_output,
            );
            return Err(bad("sealed execution requires Linux"));
        }
        #[cfg(target_os = "linux")]
        {
            use std::os::fd::AsRawFd;
            if input.len() > maximum_input
                || maximum_input > MAX_SETTINGS
                || maximum_output > MAX_SETTINGS
                || timeout_seconds == 0
                || timeout_seconds > 300
            {
                return Err(bad("sealed execution input/output/time capacity"));
            }
            let fdpath = |f: &File| format!("/proc/{}/fd/{}", std::process::id(), f.as_raw_fd());
            let mut child = Command::new("/usr/bin/timeout")
                .arg("--kill-after=2s")
                .arg(format!("{timeout_seconds}s"))
                .arg(fdpath(&self.image))
                .arg(fdpath(&self.settings))
                .args(arguments)
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::null())
                .spawn()?;
            // Write stdin on its own thread so a child that fills its stdout
            // before reading all of stdin cannot deadlock us. Always kill/reap
            // on an IO refusal. No Child or Command escapes.
            let stdin = child.stdin.take();
            let stdout = child.stdout.take();
            let (Some(mut stdin), Some(stdout)) = (stdin, stdout) else {
                let _ = child.kill();
                let _ = child.wait();
                return Err(bad("sealed execution pipes"));
            };
            let request = input.to_vec();
            let writer = std::thread::spawn(move || stdin.write_all(&request));
            let mut output = vec![];
            let read = stdout
                .take(maximum_output as u64 + 1)
                .read_to_end(&mut output);
            let mut refusal = read.err().or_else(|| {
                (output.len() > maximum_output).then(|| bad("sealed execution output capacity"))
            });
            if refusal.is_some() {
                // Unblocks the writer (EPIPE) and any child stuck on a full pipe.
                let _ = child.kill();
            }
            let status = child.wait();
            let written = writer
                .join()
                .unwrap_or_else(|_| Err(bad("sealed execution writer")));
            if refusal.is_none() {
                refusal = written.err();
            }
            if let Some(error) = refusal {
                return Err(error);
            }
            if !status?.success() {
                return Err(bad("sealed execution child refused"));
            }
            Ok(output)
        }
    }
}
#[cfg(all(test, target_os = "linux"))]
mod tests {
    use super::*;
    use std::{fs, os::unix::fs::OpenOptionsExt};
    fn fixture() -> (std::path::PathBuf, std::path::PathBuf, Vec<u8>) {
        let root = std::env::temp_dir().join(format!(
            "sealed-invoke-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&root).unwrap();
        let image = root.join("image");
        let original = fs::read("/usr/bin/dash").unwrap();
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o700)
            .open(&image)
            .unwrap();
        file.write_all(&original).unwrap();
        (root, image, original)
    }
    #[test]
    fn sealed_original_image_and_settings_survive_inplace_and_rename_replacements() {
        let (root, image, original) = fixture();
        let settings = b"printf '%s\\n' 'original exact settings'\n";
        let wanted = b"original exact settings\n";
        let config = root.join("config");
        fs::write(&config, settings).unwrap();
        let pin: [u8; 32] = Sha256::digest(&original).into();
        let held = SealedInvocation::new(&image, &pin, &fs::read(&config).unwrap()).unwrap();
        fs::write(&image, fs::read("/usr/bin/false").unwrap()).unwrap();
        fs::write(&config, b"hostile replacement settings").unwrap();
        assert_eq!(
            held.output_with_input(&[], b"", 5, 1024, 1024).unwrap(),
            wanted
        );
        fs::rename(&image, root.join("old-image")).unwrap();
        fs::write(&image, fs::read("/usr/bin/false").unwrap()).unwrap();
        fs::rename(&config, root.join("old-config")).unwrap();
        fs::write(&config, b"other").unwrap();
        assert_eq!(
            held.output_with_input(&[], b"", 5, 1024, 1024).unwrap(),
            wanted
        );
        assert!(SealedInvocation::new(&image, &pin, settings).is_err());
    }
    #[test]
    fn sealed_descriptors_refuse_writes_and_bound_io_refuses_without_success() {
        use std::{os::fd::AsRawFd, os::unix::fs::FileExt};
        let (_root, image, original) = fixture();
        let pin: [u8; 32] = Sha256::digest(&original).into();
        let held = SealedInvocation::new(&image, &pin, b"printf '123456789'\n").unwrap();
        assert!(held.image.write_at(b"x", 0).is_err());
        assert!(held.settings.write_at(b"x", 0).is_err());
        let required =
            libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL;
        assert_eq!(
            unsafe { libc::fcntl(held.image.as_raw_fd(), libc::F_GET_SEALS) } & required,
            required
        );
        assert!(held.output_with_input(&[], b"", 5, 1, 3).is_err());
        assert!(held
            .output_with_input(&[], b"too long", 5, 1, 1024)
            .is_err());
        assert!(SealedInvocation::new(&image, &pin, b"").is_err());
    }

    #[test]
    fn a_child_that_fills_stdout_before_reading_stdin_does_not_deadlock() {
        let (_root, image, original) = fixture();
        let pin: [u8; 32] = Sha256::digest(&original).into();
        // Far more than one 64 KiB pipe buffer each way; the child writes all of
        // its output before it reads any input.
        let held = SealedInvocation::new(
            &image,
            &pin,
            b"head -c 300000 /dev/zero; cat >/dev/null\n",
        )
        .unwrap();
        let input = vec![7u8; 400_000];
        let (tx, rx) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let _ = tx.send(held.output_with_input(&[], &input, 20, 400_000, 400_000));
        });
        let output = rx
            .recv_timeout(std::time::Duration::from_secs(10))
            .expect("deadlocked: no result within the test timeout")
            .unwrap();
        assert_eq!(output, vec![0u8; 300_000]);
    }
}
