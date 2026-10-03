//! Resident-key join to a separately qualified current-authority native driver.
//! Deployment pins the trusted driver; it must confirm the actual release
//! journal before returning exact ReturnSlot bytes. No receipt is forged here.
use minidregg_fhe_bend::{digest, ensure, read, Context, Result};
use sha2::{Digest, Sha256};
use std::{
    fs,
    io::Read,
    path::{Path, PathBuf},
    process::Command,
};
pub struct Driver {
    executable: PathBuf,
    pin: String,
    source_artifact: Vec<u8>,
    session_config: PathBuf,
    key_record: Option<Vec<u8>>,
}
fn executable_digest(path: &Path) -> Result<String> {
    let mut file = fs::File::open(path)?;
    let mut hash = Sha256::new();
    let mut buf = [0u8; 65536];
    loop {
        let n = file.read(&mut buf)?;
        if n == 0 {
            break;
        }
        hash.update(&buf[..n]);
    }
    Ok(minidregg_fhe_bend::hex(&hash.finalize()))
}
impl Driver {
    pub fn parse(args: &[String]) -> Result<Option<Self>> {
        if args.is_empty() {
            return Ok(None);
        }
        ensure(
            args.len() == 5 && args[0] == "--governed",
            "expected --governed SOURCE_ARTIFACT DRIVER DRIVER_SHA256 NATIVE_SESSION_CONFIG",
        )?;
        let driver = Self {
            source_artifact: read(Path::new(&args[1]))?,
            executable: PathBuf::from(&args[2]),
            pin: args[3].clone(),
            session_config: PathBuf::from(&args[4]),
            key_record: None,
        };
        ensure(
            driver.pin.len() == 64
                && driver
                    .pin
                    .bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),
            "noncanonical native driver SHA256",
        )?;
        ensure(
            executable_digest(&driver.executable)? == driver.pin,
            "unqualified native release driver",
        )?;
        Ok(Some(driver))
    }
    pub fn register(&mut self, manifest: &[u8], run: &Path) -> Result<()> {
        ensure(
            executable_digest(&self.executable)? == self.pin,
            "native driver changed",
        )?;
        let dir = run.join("key-registration");
        fs::create_dir(&dir)?;
        let source = dir.join("source-artifact.bytes");
        let material = dir.join("owner-public-material.json");
        let record = dir.join("key-record.json");
        fs::write(&source, &self.source_artifact)?;
        fs::write(&material, manifest)?;
        let status = Command::new(&self.executable)
            .arg("register-key")
            .arg(&source)
            .arg(&material)
            .arg(&self.session_config)
            .arg(&record)
            .status()?;
        ensure(
            status.success(),
            "native key custody attribution unconfirmed",
        )?;
        self.key_record = Some(read(&record)?);
        Ok(())
    }
    pub fn prepare(&self, compiler: &[u8], run: &Path, index: usize) -> Result<Context> {
        ensure(
            executable_digest(&self.executable)? == self.pin,
            "native driver changed",
        )?;
        let dir = run.join(format!("prepare-{index}"));
        fs::create_dir(&dir)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&dir, fs::Permissions::from_mode(0o700))?;
        }
        let source = dir.join("source-artifact.bytes");
        let plan = dir.join("compiler-artifact.json");
        let key = dir.join("key-record.json");
        fs::write(
            &key,
            self.key_record
                .as_ref()
                .ok_or("no native key registration")?,
        )?;
        let context = dir.join("context.json");
        fs::write(&source, &self.source_artifact)?;
        fs::write(&plan, compiler)?;
        let status = Command::new(&self.executable)
            .arg("prepare-context")
            .arg(&source)
            .arg(&plan)
            .arg(&key)
            .arg(&self.session_config)
            .arg(&context)
            .status()?;
        ensure(
            status.success(),
            "current native context could not be prepared",
        )?;
        let value: Context = serde_json::from_slice(&read(&context)?)?;
        ensure(
            value.canonical_charge.len() == 10 && !value.invocation.is_empty(),
            "native context has wrong capacity/invocation shape",
        )?;
        Ok(value)
    }
    pub fn release(
        &self,
        compiler: &[u8],
        request: &[u8],
        candidate: &[u8],
        run: &Path,
        index: usize,
    ) -> Result<()> {
        ensure(
            executable_digest(&self.executable)? == self.pin,
            "native driver changed",
        )?;
        let dir = run.join(format!("release-{index}"));
        fs::create_dir(&dir)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&dir, fs::Permissions::from_mode(0o700))?;
        }
        let source = dir.join("source-artifact.bytes");
        let plan = dir.join("compiler-artifact.json");
        let key = dir.join("key-record.json");
        fs::write(
            &key,
            self.key_record
                .as_ref()
                .ok_or("no native key registration")?,
        )?;
        let inputs = dir.join("request.json");
        let completion = dir.join("completion.json");
        let released = dir.join("released-completion.json");
        fs::write(&source, &self.source_artifact)?;
        fs::write(&plan, compiler)?;
        fs::write(&inputs, request)?;
        fs::write(&completion, candidate)?;
        let status = Command::new(&self.executable)
            .arg("commit-release")
            .arg(&source)
            .arg(&plan)
            .arg(&key)
            .arg(&inputs)
            .arg(&completion)
            .arg(&self.session_config)
            .arg(&released)
            .status()?;
        ensure(
            status.success(),
            "native release unconfirmed; owner decode withheld",
        )?;
        let returned = read(&released)?;
        ensure(
            returned == candidate,
            "different released bytes; owner decode withheld",
        )?;
        fs::write(dir.join("release-driver-sha256.txt"), &self.pin)?;
        fs::write(
            dir.join("released-completion-sha256.txt"),
            digest(&returned),
        )?;
        Ok(())
    }
}
