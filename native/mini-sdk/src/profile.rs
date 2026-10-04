//! Named identity profiles.
//!
//! Mini shares Bread's profile STORE and derivation FUNCTION, not its key: a profile holds a
//! 64-byte master seed; a key is `blake3::derive_key(path, seed)` read as an Ed25519 secret
//! seed (RFC 8032). Bread's identity is path `dregg/0`. Mini's are the path family
//! `mini/<generation>`: `mini/0` first, and a key rotation's committed next key is the next
//! generation. Distinct paths keep Bread's `dregg-action-sig-v3:` signatures and Mini's raw
//! Lean-canonical header signatures under different keys, and keep the two identities
//! unlinkable. See `docs/design/SDK-DESIGN.md` §9.
use ed25519_dalek::SigningKey;
use zeroize::Zeroizing;

use crate::signer::{Ed25519Signer, HybridSigner, Scheme, Signer};
use crate::{Error, Result};

/// Bread's identity path (pinned here only for the cross-derivation golden vector).
pub const BREAD_PATH: &str = "dregg/0";

/// The Mini key path for a key generation.
pub fn mini_path(generation: u32) -> String {
    format!("mini/{generation}")
}

/// The derivation path of the hybrid scheme's ML-DSA-65 seed for a key generation.
pub fn ml_dsa_path(generation: u32) -> String {
    format!("{}/ml-dsa-65", mini_path(generation))
}

/// `blake3::derive_key(path, seed)` → Ed25519 signing key. The same function as Bread's
/// `mnemonic::derive_keypair`.
pub fn derive(seed: &[u8; 64], path: &str) -> SigningKey {
    let mut derived = blake3::derive_key(path, seed);
    let key = SigningKey::from_bytes(&derived);
    zeroize::Zeroize::zeroize(&mut derived);
    key
}

/// A named identity: a chosen name and its master seed. Key material; never logged.
pub struct Profile {
    pub name: String,
    seed: Zeroizing<[u8; 64]>,
}

impl Profile {
    pub fn from_seed(name: &str, seed: [u8; 64]) -> Result<Self> {
        validate_name(name)?;
        Ok(Profile { name: name.to_owned(), seed: Zeroizing::new(seed) })
    }

    /// The Mini signer of `generation` under `scheme`. The Ed25519 half is always
    /// `derive(seed, "mini/<generation>")`; the hybrid's ML-DSA-65 seed is
    /// `blake3::derive_key("mini/<generation>/ml-dsa-65", seed)` (a distinct path, so the
    /// post-quantum key is unlinkable from the Ed25519 key by derivation alone).
    pub fn mini_signer(&self, generation: u32, scheme: Scheme) -> Box<dyn Signer> {
        let path = mini_path(generation);
        match scheme {
            Scheme::Ed25519 => Box::new(Ed25519Signer(derive(&self.seed, &path))),
            Scheme::HybridEd25519MlDsa65 => {
                let ed = derive(&self.seed, &path).to_bytes();
                let xi = Zeroizing::new(blake3::derive_key(&ml_dsa_path(generation), &*self.seed));
                Box::new(HybridSigner::from_seeds(&ed, &xi))
            }
        }
    }

    /// The seed, for a store writing the profile file. Key material.
    pub fn seed(&self) -> &[u8; 64] {
        &self.seed
    }
}

/// A profile name: 1..=64 of `[A-Za-z0-9_-]`, the same rule Bread's store uses for file names.
pub fn validate_name(name: &str) -> Result<()> {
    if name.is_empty()
        || name.len() > 64
        || !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-')
    {
        return Err(Error(format!("{name:?} is not a profile name")));
    }
    Ok(())
}

/// The shared on-disk store: `$DREGG_HOME/profiles/<name>.json` (default `~/.dregg`), version-1
/// JSON `{version, name, seed_hex, public_key_hex, created_at}` — Bread's format, so `dregg id`
/// and Mini read one store. `public_key_hex` is Bread's display key (`dregg/0`); Mini's key is
/// derived on load and never stored.
#[cfg(feature = "native")]
pub mod store {
    use super::*;
    use serde_json::{json, Value};
    use std::path::PathBuf;

    pub fn dir() -> Result<PathBuf> {
        if let Some(home) = std::env::var_os("DREGG_HOME") {
            return Ok(PathBuf::from(home).join("profiles"));
        }
        let home = std::env::var_os("HOME").ok_or("neither DREGG_HOME nor HOME is set")?;
        Ok(PathBuf::from(home).join(".dregg").join("profiles"))
    }

    pub fn load(name: &str) -> Result<Profile> {
        validate_name(name)?;
        let path = dir()?.join(format!("{name}.json"));
        let bytes = std::fs::read(&path).map_err(|e| format!("profile {name}: {e}"))?;
        let v: Value = serde_json::from_slice(&bytes).map_err(|e| format!("profile {name}: {e}"))?;
        if v["version"] != 1 || v["name"] != name {
            return Err(format!("profile {name}: unsupported or mismatched record").into());
        }
        let seed = crate::hex::decode(v["seed_hex"].as_str().ok_or("profile has no seed_hex")?)?;
        let seed: [u8; 64] = seed.try_into().map_err(|_| "profile seed must be 64 bytes")?;
        let expected = derive(&seed, BREAD_PATH).verifying_key();
        if v["public_key_hex"].as_str() != Some(crate::hex::encode(expected.as_bytes()).as_str()) {
            return Err(format!("profile {name}: seed and recorded public key disagree").into());
        }
        Profile::from_seed(name, seed)
    }

    /// The active profile: `DREGG_PROFILE`, else the `ACTIVE` file, else none.
    pub fn active() -> Result<Option<Profile>> {
        let name = match std::env::var("DREGG_PROFILE") {
            Ok(n) if !n.is_empty() => n,
            _ => match std::fs::read_to_string(dir()?.join("ACTIVE")) {
                Ok(n) => n.trim().to_owned(),
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
                Err(e) => return Err(e.to_string().into()),
            },
        };
        load(&name).map(Some)
    }

    /// Create a profile from 64 bytes of `/dev/urandom`; refuses an existing name.
    pub fn create(name: &str, created_at: i64) -> Result<Profile> {
        use std::io::{Read, Write};
        use std::os::unix::fs::OpenOptionsExt;
        validate_name(name)?;
        let mut seed = [0u8; 64];
        std::fs::File::open("/dev/urandom")
            .and_then(|mut f| f.read_exact(&mut seed))
            .map_err(|e| format!("cannot obtain seed: {e}"))?;
        let profile = Profile::from_seed(name, seed)?;
        zeroize::Zeroize::zeroize(&mut seed);
        let dir = dir()?;
        std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
        let record = json!({"version":1,"name":name,"seed_hex":crate::hex::encode(profile.seed()),
            "public_key_hex":crate::hex::encode(derive(profile.seed(), BREAD_PATH).verifying_key().as_bytes()),
            "created_at":created_at});
        let mut f = std::fs::OpenOptions::new().write(true).create_new(true).mode(0o600)
            .open(dir.join(format!("{name}.json")))
            .map_err(|e| format!("profile {name}: {e}"))?;
        f.write_all(record.to_string().as_bytes()).and_then(|_| f.sync_all()).map_err(|e| e.to_string())?;
        Ok(profile)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn golden_seed() -> [u8; 64] {
        let mut seed = [0u8; 64];
        for (i, b) in seed.iter_mut().enumerate() {
            *b = i as u8;
        }
        seed
    }

    /// Bread's pinned vector (`sdk/src/profiles.rs`, `cli/src/commands/id.rs`, the extension):
    /// this crate's derivation IS Bread's function.
    #[test]
    fn derivation_matches_bread_golden_vector() {
        let key = derive(&golden_seed(), BREAD_PATH);
        assert_eq!(
            crate::hex::encode(key.verifying_key().as_bytes()),
            "335840a9ca2a7a62bcfb83e3df15933c7e091c2dfd9083c26d93a8c468058b9a"
        );
    }

    /// Mini's pinned values live in `golden/vectors.json` (tests/golden.rs and the TS suite).
    #[test]
    fn mini_paths_are_separated_from_bread_and_each_other() {
        let p = Profile::from_seed("golden", golden_seed()).unwrap();
        let k0 = crate::hex::encode(&p.mini_signer(0, Scheme::Ed25519).public_key());
        let k1 = crate::hex::encode(&p.mini_signer(1, Scheme::Ed25519).public_key());
        assert_ne!(k0, "335840a9ca2a7a62bcfb83e3df15933c7e091c2dfd9083c26d93a8c468058b9a");
        assert_ne!(k0, k1);
    }

    #[test]
    fn the_hybrid_signer_is_the_ed25519_key_plus_a_distinctly_derived_ml_dsa_key() {
        let p = Profile::from_seed("golden", golden_seed()).unwrap();
        let (ed, h0, h1) = (p.mini_signer(0, Scheme::Ed25519), p.mini_signer(0, Scheme::HybridEd25519MlDsa65),
            p.mini_signer(1, Scheme::HybridEd25519MlDsa65));
        assert_eq!(h0.public_key()[..32], ed.public_key()[..], "same Ed25519 key as the plain scheme");
        assert_ne!(h0.public_key()[32..], h1.public_key()[32..], "ML-DSA key rotates with the generation");
        assert_eq!(h0.public_key(), p.mini_signer(0, Scheme::HybridEd25519MlDsa65).public_key(), "derivation is deterministic");
        assert_ne!(mini_path(0), ml_dsa_path(0));
    }

    #[test]
    fn names_are_refused_outside_the_store_alphabet() {
        assert!(validate_name("ember").is_ok());
        for bad in ["", "../x", "a b", &"a".repeat(65)] {
            assert!(validate_name(bad).is_err());
        }
    }
}
