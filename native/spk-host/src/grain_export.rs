//! Grain export and import: a stopped volume's exact bytes bound to the STOP
//! receipt that fenced them, signed by the exporting Store's completion
//! custodian. Import checks the signature, the image bytes, the package and
//! the class before any Mini effect, and the restored grain is always a new
//! application resource (Mini: recreating a grain needs a new resource ID).
//!
//! Kernel-side, `import_binds_stop_receipt` (K-SPK, `ApplicationGrainExport`)
//! makes the STOP receipt a checked fact on the importing Store; until then
//! the binding is the exporter's signature over the receipt bytes.

use ed25519_dalek::{Signature, Signer, VerifyingKey};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::path::Path;

const MAX_MANIFEST: u64 = 64 * 1024;

fn invalid(reason: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason.into())
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn unhex<const N: usize>(text: &str) -> io::Result<[u8; N]> {
    let text = text.trim();
    if text.len() != N * 2 {
        return Err(invalid("hex length refused"));
    }
    let mut out = [0u8; N];
    for (index, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&text[index * 2..index * 2 + 2], 16)
            .map_err(|_| invalid("hex refused"))?;
    }
    Ok(out)
}

fn sha256_file(path: &Path) -> io::Result<String> {
    let mut file = File::open(path)?;
    let mut digest = Sha256::new();
    let mut chunk = vec![0u8; 1 << 20];
    loop {
        let count = file.read(&mut chunk)?;
        if count == 0 {
            break;
        }
        digest.update(&chunk[..count]);
    }
    Ok(format!("{:x}", digest.finalize()))
}

fn bounded(path: &Path, max: u64) -> io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    File::open(path)?.take(max + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 > max {
        return Err(invalid(format!("{} exceeds its bound", path.display())));
    }
    Ok(bytes)
}

fn write_new(path: &Path, bytes: &[u8]) -> io::Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)?;
    file.write_all(bytes)?;
    file.sync_all()
}

/// Lay out `OUT/{var.ext4, manifest.json, manifest.sig}` from the broker's
/// copy of a stopped volume.
pub(crate) fn write_export(
    out: &Path,
    copied: &Value,
    base: &Value,
    stop_receipt: &[u8],
    custodian_seed: &Path,
) -> io::Result<Value> {
    let source = copied
        .get("image")
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("broker export reply lacks image"))?;
    let sha = copied
        .get("sha256")
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("broker export reply lacks sha256"))?;
    let receipt: Value =
        serde_json::from_slice(stop_receipt).map_err(|_| invalid("STOP receipt is not JSON"))?;
    DirBuilder::new().mode(0o700).create(out)?;
    let image = out.join("var.ext4");
    if fs::rename(source, &image).is_err() {
        fs::copy(source, &image)?;
        fs::remove_file(source)?;
    }
    if sha256_file(&image)? != sha {
        return Err(invalid("exported image differs from the broker's digest"));
    }
    let mut manifest = base.clone();
    manifest["protocol"] = json!("mini-spk-grain-export-v1");
    manifest["image"] = json!({"file":"var.ext4","sha256":sha,
        "bytes":fs::metadata(&image)?.len().to_string()});
    manifest["stopReceipt"] = receipt;
    manifest["stopReceiptSha256"] = json!(format!("{:x}", Sha256::digest(stop_receipt)));
    let bytes = serde_json::to_vec_pretty(&manifest)?;
    let key = crate::dispatch_author::private_signing_key(custodian_seed)?;
    let signature = key.sign(&bytes);
    write_new(&out.join("manifest.json"), &bytes)?;
    write_new(
        &out.join("manifest.sig"),
        hex(&signature.to_bytes()).as_bytes(),
    )?;
    write_new(
        &out.join("exporter.pub"),
        hex(key.verifying_key().as_bytes()).as_bytes(),
    )?;
    Ok(
        json!({"protocol":"mini-spk-grain-export-result-v1","dir":out,
        "manifestSha256":format!("{:x}", Sha256::digest(&bytes)),
        "imageSha256":sha,"stopReceiptSha256":manifest["stopReceiptSha256"],
        "exporterKey":hex(key.verifying_key().as_bytes())}),
    )
}

pub(crate) struct Imported {
    pub(crate) record: Value,
    pub(crate) image_sha256: String,
}

/// Every refusal names what failed; nothing reaches Mini or the broker first.
pub(crate) fn verify_import(
    dir: &Path,
    exporter_key: &str,
    raw_sha256: &str,
    class: &str,
    imports: &Path,
) -> io::Result<Imported> {
    let bytes = bounded(&dir.join("manifest.json"), MAX_MANIFEST)?;
    let signature = Signature::from_bytes(&unhex::<64>(&String::from_utf8_lossy(&bounded(
        &dir.join("manifest.sig"),
        256,
    )?))?);
    let key = VerifyingKey::from_bytes(&unhex::<32>(exporter_key)?)
        .map_err(|_| invalid("exporter key refused"))?;
    key.verify_strict(&bytes, &signature)
        .map_err(|_| invalid("import refused: exporter signature does not verify"))?;
    let manifest: Value = serde_json::from_slice(&bytes)?;
    let text = |pointer: &str| -> io::Result<String> {
        manifest
            .pointer(pointer)
            .and_then(Value::as_str)
            .map(str::to_owned)
            .ok_or_else(|| invalid(format!("import manifest lacks {pointer}")))
    };
    if text("/protocol")? != "mini-spk-grain-export-v1" {
        return Err(invalid("import manifest protocol refused"));
    }
    if text("/packageRawSha256")? != raw_sha256 {
        return Err(invalid("import refused: archive is of a different package"));
    }
    if text("/class")? != class {
        return Err(invalid("import refused: archive size class differs"));
    }
    let receipt = serde_json::to_vec(
        manifest
            .get("stopReceipt")
            .ok_or_else(|| invalid("import manifest lacks the STOP receipt"))?,
    )?;
    if receipt.is_empty() || text("/stopReceiptSha256")?.len() != 64 {
        return Err(invalid("import manifest STOP binding refused"));
    }
    let image_sha = text("/image/sha256")?;
    if sha256_file(&dir.join("var.ext4"))? != image_sha {
        return Err(invalid(
            "import refused: image bytes differ from the signed manifest",
        ));
    }
    match DirBuilder::new().mode(0o700).create(imports) {
        Ok(()) => {}
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
        Err(error) => return Err(error),
    }
    let staged = imports.join(format!("{image_sha}.ext4"));
    if !staged.exists() {
        let temp = imports.join(format!(".{image_sha}.tmp"));
        let _ = fs::remove_file(&temp);
        fs::copy(dir.join("var.ext4"), &temp)?;
        File::open(&temp)?.sync_all()?;
        fs::rename(&temp, &staged)?;
    }
    if sha256_file(&staged)? != image_sha {
        return Err(invalid("staged import differs from the signed manifest"));
    }
    Ok(Imported {
        record: json!({"protocol":"mini-spk-grain-import-v1","exporterKey":exporter_key,
            "manifestSha256":format!("{:x}", Sha256::digest(&bytes)),"manifest":manifest,
            "signature":"verified"}),
        image_sha256: image_sha,
    })
}

/// The host side of Mini's `reconcileFailedStart` (phase 9 -> 2, kernel
/// `ApplicationGrain.Operation.reconcileFailedStart`). The kernel edge exists;
/// its receiver does not (K-SPK). Until it lands, a START that failed after
/// its claim is reported, never retried, and never papered over.
pub(crate) fn reconcile_failed_start(app: &str, generation: u64) -> io::Result<Value> {
    Err(io::Error::other(format!(
        "UNRESOLVED: app {app} generation {generation} failed after its START claim; \
         Mini's reconcileFailedStart receiver is absent (K-SPK), so the app stays \
         claimed-START"
    )))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ed25519_dalek::SigningKey;

    fn scratch(name: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "grain-export-{name}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        DirBuilder::new().mode(0o700).create(&dir).unwrap();
        dir
    }

    fn export_fixture(key: &SigningKey) -> std::path::PathBuf {
        let dir = scratch("export");
        let image = vec![7u8; 4096];
        fs::write(dir.join("var.ext4"), &image).unwrap();
        let receipt = br#"{"receipt":{"acceptedCount":"31"}}"#;
        let manifest = json!({"protocol":"mini-spk-grain-export-v1","app":"7701",
            "packageRawSha256":"a".repeat(64),"class":"S",
            "image":{"file":"var.ext4","sha256":format!("{:x}", Sha256::digest(&image)),"bytes":"4096"},
            "stopReceipt":serde_json::from_slice::<Value>(receipt).unwrap(),
            "stopReceiptSha256":format!("{:x}", Sha256::digest(receipt))});
        let bytes = serde_json::to_vec_pretty(&manifest).unwrap();
        fs::write(dir.join("manifest.json"), &bytes).unwrap();
        fs::write(dir.join("manifest.sig"), hex(&key.sign(&bytes).to_bytes())).unwrap();
        dir
    }

    #[test]
    fn import_binds_signature_bytes_package_and_class() {
        let key = SigningKey::from_bytes(&[5u8; 32]);
        let public = hex(key.verifying_key().as_bytes());
        let dir = export_fixture(&key);
        let imports = scratch("imports").join("imports");
        let ok = verify_import(&dir, &public, &"a".repeat(64), "S", &imports).unwrap();
        assert_eq!(ok.record["signature"], "verified");
        // a different package, a different class, another exporter
        assert!(verify_import(&dir, &public, &"b".repeat(64), "S", &imports).is_err());
        assert!(verify_import(&dir, &public, &"a".repeat(64), "M", &imports).is_err());
        let other = hex(SigningKey::from_bytes(&[6u8; 32])
            .verifying_key()
            .as_bytes());
        assert!(verify_import(&dir, &other, &"a".repeat(64), "S", &imports).is_err());
        // one flipped image byte
        let mut image = fs::read(dir.join("var.ext4")).unwrap();
        image[100] ^= 1;
        fs::write(dir.join("var.ext4"), &image).unwrap();
        let error = verify_import(&dir, &public, &"a".repeat(64), "S", &imports)
            .err()
            .unwrap()
            .to_string();
        assert!(error.contains("image bytes differ"), "{error}");
        // one flipped manifest byte
        let dir = export_fixture(&key);
        let mut manifest = fs::read(dir.join("manifest.json")).unwrap();
        let at = manifest.iter().position(|b| *b == b'7').unwrap();
        manifest[at] = b'8';
        fs::write(dir.join("manifest.json"), &manifest).unwrap();
        let error = verify_import(&dir, &public, &"a".repeat(64), "S", &imports)
            .err()
            .unwrap()
            .to_string();
        assert!(error.contains("signature"), "{error}");
    }
}
