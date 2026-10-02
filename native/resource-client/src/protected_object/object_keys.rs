//! Retained object keys and uncertain exact emissions. Historical key possession
//! is deliberately independent of receiving authority. A restored archive cannot
//! establish freshness: every emission requires a fresh authenticated source anchor.
use crate::object_messages::{self, Context};
use crate::{hex, Result};
use chacha20poly1305::{
    aead::{Aead, KeyInit, Payload},
    XChaCha20Poly1305, XNonce,
};
use ed25519_dalek::SigningKey;
use ring::rand::{SecureRandom, SystemRandom};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::{
    fs::{self, File, OpenOptions},
    io::Write,
    os::unix::fs::OpenOptionsExt,
    path::{Path, PathBuf},
};
use zeroize::{Zeroize, Zeroizing};

const FRAME: &[u8] = b"MINI/OBJECT-STATE/v1";
const MAX_STATE_BYTES: usize = 32 * 1024 * 1024;
/// This must come from authenticated admitted history, not a local cache or a
/// self-reported epoch. The caller is responsible for source verification.
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct AdmittedAnchor {
    pub object: [u8; 32],
    pub epoch: u64,
    pub transition: [u8; 32],
    pub active: bool,
}
pub(crate) struct Store {
    path: PathBuf,
    _lock: crate::transport::ServiceLock,
    storage_key: Zeroizing<[u8; 32]>,
    state: Value,
    healthy: bool,
}
fn scrub(value: &mut Value) {
    match value {
        Value::String(s) => s.zeroize(),
        Value::Array(a) => a.iter_mut().for_each(scrub),
        Value::Object(o) => o.values_mut().for_each(scrub),
        _ => {}
    }
}
impl Drop for Store {
    fn drop(&mut self) {
        scrub(&mut self.state);
    }
}
fn unhex(s: &str) -> Result<Vec<u8>> {
    crate::workspace::private::decode_hex(s)
}
impl Store {
    /// Initialize durable empty custody explicitly, before publishing its backup manifest.
    pub(crate) fn initialize(path: &Path, storage_key: [u8; 32]) -> Result<Self> {
        let mut store = Self::open(path, storage_key)?;
        if !path.exists() { store.save()?; }
        Ok(store)
    }
    /// Process-held advisory custody. The OS releases it on crash; never unlink
    /// the lock inode, which would permit a second lock on a replacement inode.
    pub(crate) fn open(path: &Path, storage_key: [u8; 32]) -> Result<Self> {
        let lock = path.with_extension("object-lock");
        let lock_file = crate::transport::service_lock(&lock)?;
        let mut s = Self {
            path: path.into(),
            _lock: lock_file,
            storage_key: Zeroizing::new(storage_key),
            state: json!({"keys":{},"pending":{}}),
            healthy: true,
        };
        if path.exists() {
            let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
            if !meta.file_type().is_file() || meta.len() > MAX_STATE_BYTES as u64 {
                return Err("invalid object state file".into());
            }
            let b = fs::read(path).map_err(|e| e.to_string())?;
            let h = FRAME.len() + 24;
            if b.len() < h + 16 || !b.starts_with(FRAME) {
                return Err("invalid object state frame".into());
            }
            let p = Zeroizing::new(
                XChaCha20Poly1305::new((&*s.storage_key).into())
                    .decrypt(
                        XNonce::from_slice(&b[FRAME.len()..h]),
                        Payload {
                            msg: &b[h..],
                            aad: &b[..h],
                        },
                    )
                    .map_err(|_| "object state authentication failed")?,
            );
            s.state = serde_json::from_slice(&p).map_err(|e| e.to_string())?;
            if !s.state["keys"].is_object() || !s.state["pending"].is_object() {
                return Err("invalid object state schema".into());
            }
        }
        Ok(s)
    }
    fn save(&mut self) -> Result<()> {
        self.healthy = false;
        let plain = Zeroizing::new(serde_json::to_vec(&self.state).map_err(|e| e.to_string())?);
        if plain.len() > MAX_STATE_BYTES - FRAME.len() - 24 - 16 {
            return Err("retained object state capacity reached; new emission refused".into());
        }
        let mut nonce = [0; 24];
        SystemRandom::new()
            .fill(&mut nonce)
            .map_err(|_| "randomness unavailable")?;
        let header = [FRAME, &nonce].concat();
        let ct = XChaCha20Poly1305::new((&*self.storage_key).into())
            .encrypt(
                XNonce::from_slice(&nonce),
                Payload {
                    msg: &plain,
                    aad: &header,
                },
            )
            .map_err(|_| "object state encryption failed")?;
        let mut suffix = [0; 16];
        SystemRandom::new()
            .fill(&mut suffix)
            .map_err(|_| "randomness unavailable")?;
        let tmp = self
            .path
            .with_extension(format!("object-tmp-{}", hex(&suffix)));
        let mut f = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&tmp)
            .map_err(|e| e.to_string())?;
        f.write_all(&[header, ct].concat())
            .and_then(|_| f.sync_all())
            .map_err(|e| e.to_string())?;
        fs::rename(&tmp, &self.path).map_err(|e| e.to_string())?;
        File::open(
            self.path
                .parent()
                .filter(|p| !p.as_os_str().is_empty())
                .unwrap_or(Path::new(".")),
        )
        .and_then(|d| d.sync_all())
        .map_err(|e| e.to_string())?;
        self.healthy = true;
        Ok(())
    }
    /// Reconcile a freshly authenticated source observation against the local
    /// accepted epoch high-water mark. This detects isolated application/cache
    /// rewind; it cannot detect restoration of BOTH this journal and the source.
    /// Callers must authenticate current source freshness outside this store.
    pub(crate) fn reconcile_anchor(&mut self, current: &AdmittedAnchor) -> Result<()> {
        if !self.healthy {
            return Err("state persistence failed; reopen and reconcile".into());
        }
        let id = hex(&current.object);
        if self.state.get("anchors").is_none() {
            self.state["anchors"] = json!({});
        }
        if let Some(old) = self.state["anchors"].get(&id) {
            let epoch = old["epoch"]
                .as_u64()
                .ok_or("invalid persisted audience high-water mark")?;
            if current.epoch < epoch {
                return Err("source epoch precedes accepted local high-water mark".into());
            }
            if current.epoch == epoch && old["active"] == json!(false) && current.active {
                return Err(
                    "cannot reactivate a frozen epoch; reconcile canonical successor".into(),
                );
            }
            if current.epoch == epoch
                && current.active
                && old["transition"] != json!(hex(&current.transition))
            {
                return Err("conflicting accepted transition at the same epoch".into());
            }
        }
        self.state["anchors"][&id] = json!({"epoch":current.epoch,"transition":hex(&current.transition),"active":current.active});
        self.save()
    }
    /// Device private material remains in encrypted custody; publication emits
    /// only its authenticated public record and generation commitment.
    pub(crate) fn retain_device(
        &mut self,
        generation: &[u8; 32],
        secret: &crate::object_keys_hybrid::DeviceSecret,
        public: &crate::object_keys_hybrid::DevicePublic,
    ) -> Result<()> {
        if !self.healthy {
            return Err("state persistence failed; reopen and reconcile".into());
        }
        if self.state.get("devices").is_none() {
            self.state["devices"] = json!({});
        }
        let id = hex(generation);
        if self.state["devices"].get(&id).is_some() {
            return Err("device generation already retained".into());
        }
        self.state["devices"][&id] = json!({"kemSecret":hex(&secret.kem),"dhSecret":hex(&*secret.dh),"kemPublic":hex(&public.kem),"dhPublic":hex(&public.dh)});
        self.save()
    }
    pub(crate) fn load_device(
        &self,
        generation: &[u8; 32],
    ) -> Result<(
        crate::object_keys_hybrid::DeviceSecret,
        crate::object_keys_hybrid::DevicePublic,
    )> {
        let row = self.state["devices"]
            .get(hex(generation))
            .ok_or("device generation not retained")?;
        let field = |name: &str| -> Result<Vec<u8>> {
            unhex(row[name].as_str().ok_or("invalid retained device")?)
        };
        let secret = crate::object_keys_hybrid::DeviceSecret {
            kem: Zeroizing::new(field("kemSecret")?),
            dh: Zeroizing::new(
                field("dhSecret")?
                    .try_into()
                    .map_err(|_| "invalid DH secret")?,
            ),
        };
        let public = crate::object_keys_hybrid::DevicePublic {
            kem: field("kemPublic")?,
            dh: field("dhPublic")?
                .try_into()
                .map_err(|_| "invalid DH public")?,
        };
        Ok((secret, public))
    }
    /// Import only delegated epochs. Joining does not automatically import history.
    pub(crate) fn retain(&mut self, anchor: &AdmittedAnchor, key: &[u8; 32]) -> Result<()> {
        if !self.healthy {
            return Err("state persistence failed; reopen and reconcile".into());
        }
        let id = format!(
            "{}:{}:{}",
            hex(&anchor.object),
            anchor.epoch,
            hex(&anchor.transition)
        );
        if let Some(old) = self.state["keys"].get(&id) {
            if old.as_str() != Some(&hex(key)) {
                return Err("conflicting key for admitted epoch".into());
            }
        }
        self.state["keys"][&id] = json!(hex(key));
        self.save()
    }
    pub(crate) fn historical_key(&self, anchor: &AdmittedAnchor) -> Result<Zeroizing<[u8; 32]>> {
        let id = format!(
            "{}:{}:{}",
            hex(&anchor.object),
            anchor.epoch,
            hex(&anchor.transition)
        );
        let bytes = Zeroizing::new(unhex(
            self.state["keys"][id]
                .as_str()
                .ok_or("historical epoch not delegated")?,
        )?);
        Ok(Zeroizing::new(
            bytes
                .as_slice()
                .try_into()
                .map_err(|_| "invalid retained key")?,
        ))
    }
    /// Persist the exact ciphertext before returning bytes eligible for emission.
    /// A stale local epoch is never accepted merely because its key still exists.
    pub(crate) fn prepare(
        &mut self,
        current: &AdmittedAnchor,
        context: &Context,
        writer: &SigningKey,
        plain: &[u8],
    ) -> Result<Vec<u8>> {
        if !self.healthy {
            return Err("state persistence failed; reopen and reconcile before emission".into());
        }
        if !current.active
            || context.object != current.object
            || context.epoch != current.epoch
            || context.transition != current.transition
        {
            return Err("fresh active admitted audience anchor required".into());
        }
        self.reconcile_anchor(current)?;
        let id = hex(&context.operation);
        let plain_hash = hex(&Sha256::digest(plain));
        let writer_id = hex(&writer.verifying_key().to_bytes());
        if let Some(old) = self.state["pending"].get(&id) {
            if old.get("settled").is_some() {
                return Err("operation already settled; reconcile instead of emitting".into());
            }
            if old["plainHash"] != json!(plain_hash)
                || old["writer"] != json!(writer_id)
                || old["context"] != json!(hex(&context.bytes()))
            {
                return Err("operation already bound to another epoch/context".into());
            }
            return unhex(old["wire"].as_str().ok_or("invalid pending wire")?);
        }
        let key = self.historical_key(current)?;
        let wire = object_messages::seal(context, &key, writer, plain)?;
        self.state["pending"][&id] = json!({"context":hex(&context.bytes()),"wire":hex(&wire),"plainHash":plain_hash,"writer":writer_id});
        self.save()?;
        Ok(wire)
    }
    /// Retain an immutable authored fragment and its independent content key.
    /// Exact retries return the original signed ciphertext; audience changes
    /// subsequently wrap this key without resealing or reattributing the body.
    pub(crate) fn prepare_fragment(&mut self, current: &AdmittedAnchor,
        context: &Context, writer: &SigningKey, plain: &[u8]) -> Result<(Zeroizing<[u8;32]>, Vec<u8>)> {
        if !self.healthy || !current.active || context.object != current.object
            || context.epoch != current.epoch || context.transition != current.transition {
            return Err("fresh active fragment audience required".into());
        }
        self.reconcile_anchor(current)?;
        let id=hex(&context.operation);
        let plain_hash=hex(&Sha256::digest(plain));
        let writer_id=hex(&writer.verifying_key().to_bytes());
        if let Some(old)=self.state["fragments"].get(&id) {
            if old["plainHash"]!=json!(plain_hash) || old["writer"]!=json!(writer_id)
                || old["context"]!=json!(hex(&context.bytes())) {
                return Err("authored fragment already bound to another plaintext/context".into());
            }
            let key=Zeroizing::new(unhex(old["key"].as_str().ok_or("invalid fragment key")?)?
                .try_into().map_err(|_|"invalid fragment key length")?);
            return Ok((key,unhex(old["wire"].as_str().ok_or("invalid fragment wire")?)?));
        }
        let mut key=Zeroizing::new([0u8;32]);
        SystemRandom::new().fill(&mut *key).map_err(|_|"fragment randomness unavailable")?;
        let wire=object_messages::seal(context,&key,writer,plain)?;
        if !self.state["fragments"].is_object(){self.state["fragments"]=json!({});}
        self.state["fragments"][&id]=json!({"context":hex(&context.bytes()),"wire":hex(&wire),
            "plainHash":plain_hash,"writer":writer_id,"key":hex(&*key)});
        self.save()?;
        Ok((key,wire))
    }
    /// Retain the complete package and canonical source intent before invoking
    /// the Host author or publishing any phase artifact. Binary authoring can be
    /// resumed from these exact JSON bytes; the key is never generated again.
    pub(crate) fn stage_epoch_intent(
        &mut self, next:&AdmittedAnchor, operation:&[u8;32],
        prepared:&crate::object_epoch_packages::PreparedEpoch, intent:&[u8],
    )->Result<()> {
        self.stage_epoch_material(next,operation,prepared,&[],Some(intent))
    }
    /// Persist fresh epoch key, complete manifest and exact source command before
    /// publishing any rekey phase. An uncertain retry retrieves identical bytes.
    /// `next` is a proposal, never a source freshness/authority certificate.
    pub(crate) fn stage_epoch(
        &mut self, next:&AdmittedAnchor, operation:&[u8;32],
        prepared:&crate::object_epoch_packages::PreparedEpoch, exact_command:&[u8],
    )->Result<()> {
        self.stage_epoch_material(next,operation,prepared,exact_command,None)
    }
    fn stage_epoch_material(
        &mut self, next:&AdmittedAnchor, operation:&[u8;32],
        prepared:&crate::object_epoch_packages::PreparedEpoch, exact_command:&[u8], intent:Option<&[u8]>,
    )->Result<()> {
        if !self.healthy {return Err("state persistence failed; reopen and reconcile".into());}
        let id=hex(operation);
        if self.state["pending"].get(&id).is_some() {
            return Err("rekey operation already staged; reconcile its exact bytes".into());
        }
        let key_id=format!("{}:{}:{}",hex(&next.object),next.epoch,hex(&next.transition));
        if self.state["keys"].get(&key_id).is_some() {
            return Err("epoch key already exists; refusing replacement".into());
        }
        self.state["pending"][&id]=json!({"kind":"epoch","epochKey":hex(&*prepared.key),
            "object":hex(&next.object),"epoch":next.epoch,"transition":hex(&next.transition),
            "manifest":hex(&prepared.manifest),"manifestCommitment":hex(&prepared.commitment),"command":hex(exact_command)});
        if let Some(intent)=intent {self.state["pending"][&id]["intentJson"]=json!(hex(intent));}
        self.save()
    }
    pub(crate) fn stage_control_intent(
        &mut self,next:&AdmittedAnchor,operation:&[u8;32],intent:&[u8],
    )->Result<()> {
        self.stage_control_material(next,operation,&[],Some(intent))
    }
    pub(crate) fn stage_control(
        &mut self,next:&AdmittedAnchor,operation:&[u8;32],exact_command:&[u8],
    )->Result<()> {
        self.stage_control_material(next,operation,exact_command,None)
    }
    fn stage_control_material(
        &mut self,next:&AdmittedAnchor,operation:&[u8;32],exact_command:&[u8],intent:Option<&[u8]>,
    )->Result<()> {
        if !self.healthy {return Err("state persistence failed; reopen and reconcile".into());}
        let id=hex(operation);
        if self.state["pending"].get(&id).is_some() {
            return Err("phase already staged; reconcile its exact command".into());
        }
        self.state["pending"][&id]=json!({"kind":"control","object":hex(&next.object),
            "epoch":next.epoch,"transition":hex(&next.transition),"active":next.active,
            "manifest":"","command":hex(exact_command)});
        if let Some(intent)=intent {self.state["pending"][&id]["intentJson"]=json!(hex(intent));}
        self.save()
    }
    pub(crate) fn operation_known(&self,operation:&[u8;32])->Result<bool> {
        if !self.healthy {return Err("state persistence failed; reopen and reconcile".into());}
        Ok(self.state["pending"].get(hex(operation)).is_some())
    }
    /// Distinguish a retained rejection from a pending or confirmed phase.
    /// Callers must not infer settlement from an unrelated decoding failure.
    pub(crate) fn operation_settlement(&self,operation:&[u8;32])->Result<Option<bool>> {
        if !self.healthy {return Err("state persistence failed; reopen and reconcile".into());}
        let row=self.state["pending"].get(hex(operation)).ok_or("unknown staged operation")?;
        row.get("settled").map(|value|value.as_bool().ok_or("invalid operation settlement".into())).transpose()
    }
    /// Outward artifacts are recoverable even after confirmed settlement. This
    /// returns no key and does not authorize either replacement or resubmission.
    pub(crate) fn phase_artifacts(&self,operation:&[u8;32])->Result<(Vec<u8>,Vec<u8>,Option<Vec<u8>>)> {
        if !self.healthy {return Err("state persistence failed; reopen and reconcile".into());}
        let row=self.state["pending"].get(hex(operation)).ok_or("unknown staged phase")?;
        if row["kind"]!=json!("epoch") && row["kind"]!=json!("control") {
            return Err("operation is not an epoch phase".into());
        }
        Ok((unhex(row["manifest"].as_str().ok_or("invalid staged manifest")?)?,
            unhex(row["command"].as_str().ok_or("invalid staged command")?)?,
            row.get("intentJson").map(|intent|unhex(intent.as_str().ok_or("invalid staged intent JSON")?)).transpose()?))
    }
    /// Bind the Host-authored command once, without changing its staged JSON,
    /// key, manifest or operation identity. Publication follows this fsync.
    pub(crate) fn bind_epoch_command(&mut self,operation:&[u8;32],command:&[u8])->Result<()> {
        if command.is_empty() {return Err("empty epoch command".into());}
        let (_,old)=self.pending_epoch(operation)?;
        if !old.is_empty() {
            if old!=command {return Err("epoch command differs from durable binding".into());}
            return Ok(());
        }
        self.state["pending"][hex(operation)]["command"]=json!(hex(command));
        self.save()
    }
    pub(crate) fn bind_attempt(&mut self, operation: &[u8; 32], directory: &Path) -> Result<()> {
        if !self.healthy {
            return Err("state persistence failed; reconcile before retry".into());
        }
        let directory = if directory.is_absolute() {
            directory.to_path_buf()
        } else {
            std::env::current_dir()
                .map_err(|e| e.to_string())?
                .join(directory)
        };
        let row = self.state["pending"]
            .get_mut(hex(operation))
            .ok_or("unknown staged operation")?;
        if row.get("settled").is_some() {
            return Err("operation already settled".into());
        }
        row["attempt"] = json!(directory.to_str().ok_or("attempt path must be UTF-8")?);
        self.save()
    }
    pub(crate) fn pending_attempt(&self, operation: &[u8; 32]) -> Result<Option<PathBuf>> {
        let row = self.state["pending"]
            .get(hex(operation))
            .ok_or("unknown staged operation")?;
        Ok(row
            .get("attempt")
            .and_then(Value::as_str)
            .map(PathBuf::from))
    }
    pub(crate) fn pending_epoch(&self, operation: &[u8; 32]) -> Result<(Vec<u8>, Vec<u8>)> {
        if !self.healthy {
            return Err("state persistence failed; reopen and reconcile before emission".into());
        }
        let row = self.state["pending"]
            .get(hex(operation))
            .ok_or("unknown staged epoch")?;
        if (row["kind"] != json!("epoch") && row["kind"] != json!("control"))
            || row.get("settled").is_some()
        {
            return Err("epoch is not awaiting source reconciliation".into());
        }
        Ok((
            unhex(row["manifest"].as_str().ok_or("invalid staged manifest")?)?,
            unhex(row["command"].as_str().ok_or("invalid staged command")?)?,
        ))
    }
    /// Only after source settlement establishes this exact operation's outcome.
    /// Retain a tombstone so restoring application state cannot reuse its identity.
    pub(crate) fn settle(&mut self, operation: &[u8; 32], accepted: bool) -> Result<()> {
        if !self.healthy {
            return Err("state persistence failed; reopen and reconcile".into());
        }
        let original = self.state["pending"]
            .get(hex(operation))
            .ok_or("unknown pending operation")?;
        if let Some(settled) = original.get("settled") {
            if settled != &json!(accepted) {
                return Err("contradictory source settlement outcome".into());
            }
        }
        let install = if accepted && original["kind"] == json!("epoch") {
            let key_id = format!(
                "{}:{}:{}",
                original["object"].as_str().ok_or("invalid staged object")?,
                original["epoch"].as_u64().ok_or("invalid staged epoch")?,
                original["transition"]
                    .as_str()
                    .ok_or("invalid staged transition")?
            );
            let key = original["epochKey"]
                .as_str()
                .ok_or("missing staged epoch key")?
                .to_owned();
            if let Some(prior) = self.state["keys"].get(&key_id) {
                if prior != &json!(key) {
                    return Err("accepted epoch conflicts with retained established key".into());
                }
            }
            Some((key_id, key))
        } else {
            None
        };
        let row = self.state["pending"]
            .get_mut(hex(operation))
            .ok_or("unknown pending operation")?;
        row["settled"] = json!(accepted);
        let staged =
            if accepted && (row["kind"] == json!("epoch") || row["kind"] == json!("control")) {
                Some((
                    row["object"]
                        .as_str()
                        .ok_or("invalid staged object")?
                        .to_owned(),
                    row["epoch"].as_u64().ok_or("invalid staged epoch")?,
                    row["transition"].clone(),
                    row["active"].as_bool().unwrap_or(true),
                ))
            } else {
                None
            };
        if let Some((key_id, key)) = install {
            self.state["keys"][&key_id] = json!(key);
        }
        if let Some((object, epoch, transition, active)) = staged {
            if self.state.get("anchors").is_none() {
                self.state["anchors"] = json!({});
            }
            let old = &self.state["anchors"][&object];
            let advance = old.is_null()
                || old["epoch"].as_u64().is_some_and(|prior| {
                    epoch > prior || (epoch == prior && old["active"] != json!(false))
                });
            // Exact historical receipts can arrive after later source progress;
            // they settle their operation without rewinding the high-water mark.
            if advance {
                self.state["anchors"][&object] =
                    json!({"epoch":epoch,"transition":transition,"active":active});
            }
        }
        self.save()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn lock_child() {
        let Some(path) = std::env::var_os("MINI_OBJECT_LOCK_TEST_CHILD") else {
            return;
        };
        let path = PathBuf::from(path);
        let _store = Store::open(&path, [8; 32]).unwrap();
        fs::write(path.with_extension("ready"), b"ready").unwrap();
        loop {
            std::thread::park();
        }
    }
    #[test]
    fn crash_releases_custody_without_unlinking_lock_inode() {
        use std::{process::Command, time::Duration};
        let mut n = [0; 16];
        SystemRandom::new().fill(&mut n).unwrap();
        let dir = std::env::temp_dir().join(format!("mini-object-crash-test-{}", hex(&n)));
        fs::create_dir(&dir).unwrap();
        let path = dir.join("state");
        let marker = path.with_extension("ready");
        let mut child = Command::new(std::env::current_exe().unwrap())
            .arg("--exact")
            .arg("object_keys::tests::lock_child")
            .env("MINI_OBJECT_LOCK_TEST_CHILD", &path)
            .stdout(std::process::Stdio::null())
            .spawn()
            .unwrap();
        for _ in 0..200 {
            if marker.exists() {
                break;
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        if !marker.exists() {
            let _ = child.kill();
            let _ = child.wait();
            panic!("child did not acquire custody");
        }
        assert!(Store::open(&path, [8; 32]).is_err());
        child.kill().unwrap();
        child.wait().unwrap();
        let store = Store::open(&path, [8; 32]).unwrap();
        drop(store);
        assert!(path.with_extension("object-lock").exists());
        fs::remove_file(marker).unwrap();
        fs::remove_file(path.with_extension("object-lock")).unwrap();
        fs::remove_dir(dir).unwrap();
    }
    #[test]
    fn contended_epoch_keeps_proposal_separate_until_exact_acceptance() {
        let mut random = [0; 16];
        SystemRandom::new().fill(&mut random).unwrap();
        let dir = std::env::temp_dir().join(format!("mini-epoch-stage-test-{}", hex(&random)));
        fs::create_dir(&dir).unwrap();
        let path = dir.join("state");
        let a = AdmittedAnchor {
            object: [1; 32],
            epoch: 3,
            transition: [2; 32],
            active: true,
        };
        let first = crate::object_epoch_packages::PreparedEpoch {
            key: Zeroizing::new([9; 32]),
            manifest: b"first exact prepared manifest".to_vec(),
            commitment: [6; 32],
        };
        let second = crate::object_epoch_packages::PreparedEpoch {
            key: Zeroizing::new([10; 32]),
            manifest: b"fresh contender manifest".to_vec(),
            commitment: [7; 32],
        };
        let mut store = Store::open(&path, [8; 32]).unwrap();
        store
            .stage_epoch(&a, &[3; 32], &first, b"first exact command")
            .unwrap();
        assert!(store.historical_key(&a).is_err());
        drop(store);
        let mut store = Store::open(&path, [8; 32]).unwrap();
        assert_eq!(store.pending_epoch(&[3; 32]).unwrap().0, first.manifest);
        store.settle(&[3; 32], false).unwrap();
        assert!(store.historical_key(&a).is_err());
        store
            .stage_epoch(&a, &[4; 32], &second, b"new exact command")
            .unwrap();
        store.settle(&[4; 32], true).unwrap();
        assert_eq!(*store.historical_key(&a).unwrap(), [10; 32]);
        assert!(store
            .stage_epoch(&a, &[5; 32], &first, b"replacement")
            .is_err());
        assert!(store.settle(&[4; 32], false).is_err());
        drop(store);
        fs::remove_file(path).unwrap();
        fs::remove_file(dir.join("state.object-lock")).unwrap();
        fs::remove_dir(dir).unwrap();
    }
    #[test]
    fn phase_restart_keeps_exact_command_and_confirmed_freeze_fence() {
        let mut random = [0; 16];
        SystemRandom::new().fill(&mut random).unwrap();
        let dir = std::env::temp_dir().join(format!("mini-object-phase-test-{}", hex(&random)));
        fs::create_dir(&dir).unwrap();
        let path = dir.join("state");
        let active = AdmittedAnchor {
            object: [1; 32],
            epoch: 2,
            transition: [2; 32],
            active: true,
        };
        let frozen = AdmittedAnchor {
            transition: [3; 32],
            active: false,
            ..active.clone()
        };
        let mut store = Store::open(&path, [8; 32]).unwrap();
        store.reconcile_anchor(&active).unwrap();
        store.stage_control(&frozen, &[3;32], b"rejected earlier generation").unwrap();
        store.settle(&[3;32], false).unwrap();
        store
            .stage_control(&frozen, &[4; 32], b"exact source phase command")
            .unwrap();
        drop(store);
        let mut store = Store::open(&path, [8; 32]).unwrap();
        assert_eq!(
            store.pending_epoch(&[4; 32]).unwrap().1,
            b"exact source phase command"
        );
        store.settle(&[4; 32], true).unwrap();
        drop(store);
        let mut store = Store::open(&path, [8; 32]).unwrap();
        assert!(store.reconcile_anchor(&active).is_err());
        assert!(store.pending_epoch(&[4; 32]).is_err());
        assert_eq!(store.operation_settlement(&[3;32]).unwrap(),Some(false));
        assert_eq!(store.operation_settlement(&[4;32]).unwrap(),Some(true));
        assert!(store.operation_settlement(&[99;32]).is_err());
        drop(store);
        fs::remove_file(path).unwrap();
        fs::remove_file(dir.join("state.object-lock")).unwrap();
        fs::remove_dir(dir).unwrap();
    }
    #[test]
    fn restart_exact_retry_freeze_and_settlement() {
        let mut n = [0; 16];
        SystemRandom::new().fill(&mut n).unwrap();
        let dir = std::env::temp_dir().join(format!("mini-objects-test-{}", hex(&n)));
        fs::create_dir(&dir).unwrap();
        let path = dir.join("state");
        let a = AdmittedAnchor {
            object: [1; 32],
            epoch: 2,
            transition: [2; 32],
            active: true,
        };
        let c = Context {
            object: a.object,
            epoch: a.epoch,
            transition: a.transition,
            operation: [3; 32],
            law: [4; 32],
        };
        let s = SigningKey::from_bytes(&[5; 32]);
        let mut store = Store::open(&path, [8; 32]).unwrap();
        store.retain(&a, &[9; 32]).unwrap();
        let wire = store.prepare(&a, &c, &s, b"draft").unwrap();
        assert!(Store::open(&path, [8; 32]).is_err());
        drop(store);
        let mut store = Store::open(&path, [8; 32]).unwrap();
        assert_eq!(store.prepare(&a, &c, &s, b"draft").unwrap(), wire);
        assert!(store.prepare(&a, &c, &s, b"different").is_err());
        let mut frozen = a.clone();
        frozen.active = false;
        assert!(store.prepare(&frozen, &c, &s, b"draft").is_err());
        assert_eq!(*store.historical_key(&frozen).unwrap(), [9; 32]);
        store.reconcile_anchor(&frozen).unwrap();
        assert!(store.prepare(&a, &c, &s, b"draft").is_err());
        let mut stale = a.clone();
        stale.epoch -= 1;
        assert!(store.reconcile_anchor(&stale).is_err());
        store.settle(&c.operation, true).unwrap();
        drop(store);
        let mut store = Store::open(&path, [8; 32]).unwrap();
        assert!(store.prepare(&a, &c, &s, b"draft").is_err());
        drop(store);
        fs::remove_file(&path).unwrap();
        fs::remove_file(path.with_extension("object-lock")).unwrap();
        fs::remove_dir(dir).unwrap();
    }
    #[cfg(target_os = "linux")]
    #[test]
    fn logical_custody_drop_releases_lock_while_fork_child_retains_fd() {
        let dir = std::env::temp_dir().join(format!("mini-object-fork-lock-{}", crate::workspace::random_nonce().unwrap()));
        crate::workspace::make_private_dir(&dir).unwrap();
        let path = dir.join("state");
        let store = Store::open(&path, [8; 32]).unwrap();
        let mut ready = [-1; 2];
        let mut finish = [-1; 2];
        assert_eq!(unsafe { libc::pipe2(ready.as_mut_ptr(), libc::O_CLOEXEC) }, 0);
        assert_eq!(unsafe { libc::pipe2(finish.as_mut_ptr(), libc::O_CLOEXEC) }, 0);
        let child = unsafe { libc::fork() };
        assert!(child >= 0);
        if child == 0 {
            // Only async-signal-safe syscalls after fork in the threaded test
            // process. Keep the inherited custody descriptor until parent ends.
            unsafe {
                libc::close(ready[0]); libc::close(finish[1]);
                store._lock.release();
                let byte = 1u8;
                libc::write(ready[1], &byte as *const u8 as *const libc::c_void, 1);
                let mut byte = 0u8;
                libc::read(finish[0], &mut byte as *mut u8 as *mut libc::c_void, 1);
                libc::_exit(0);
            }
        }
        unsafe { libc::close(ready[1]); libc::close(finish[0]); }
        let mut byte = 0u8;
        assert_eq!(unsafe { libc::read(ready[0], &mut byte as *mut u8 as *mut libc::c_void, 1) }, 1);
        let parent_still_exclusive = Store::open(&path, [8; 32]).is_err();
        drop(store);
        let reopened = Store::open(&path, [8; 32]);
        // Always release/reap the child, including when testing the regression
        // against the old implementation; it must not leave a waiting process.
        unsafe {
            libc::write(finish[1], &byte as *const u8 as *const libc::c_void, 1);
            libc::close(finish[1]); libc::close(ready[0]);
            libc::waitpid(child, std::ptr::null_mut(), 0);
        }
        assert!(parent_still_exclusive, "child release unlocked its parent's active custody");
        assert!(reopened.is_ok(), "logical custody ended but child retained the lock: {:?}", reopened.err());
        fs::remove_dir_all(dir).unwrap();
    }

}
