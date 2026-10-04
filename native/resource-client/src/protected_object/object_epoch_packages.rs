//! Object audience epoch packages. This module distributes keys, while the Lean
//! audience controller decides authority, freeze and resume. An honest dealer
//! must use the exact authenticated post-revocation audience/device snapshot.
use crate::{
    hex,
    object_keys_hybrid::{self, DevicePublic},
    object_messages::Context,
    Result,
};
use ed25519_dalek::{Signer, SigningKey};
use ring::rand::{SecureRandom, SystemRandom};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use zeroize::Zeroizing;
pub(crate) struct Recipient {
    pub subject: String,
    pub generation: [u8; 32],
    pub capability: String,
    pub device_source: String,
    pub public: DevicePublic,
    pub key_commitment: [u8; 32],
}
pub(crate) struct PreparedEpoch {
    pub key: Zeroizing<[u8; 32]>,
    pub manifest: Vec<u8>,
    pub commitment: [u8; 32],
}
/// Current-and-future delegation only: each package carries only the fresh epoch
/// key. Separate historical delegation explicitly selects retained old epochs.
/// The source binds audience/devices/history and exact manifest commitment on
/// resume; this producer cannot attest hidden audience correctness by itself.
pub(crate) fn prepare(
    context: &Context,
    audience: &[u8; 32],
    devices: &[u8; 32],
    history: &[u8; 32],
    authority_snapshot: &[u8; 32],
    device_snapshot: &[u8; 32],
    recipients: &[Recipient],
    roster_bytes: &[u8],
    dealer_subject: &str,
    dealer_generation: &[u8; 32],
    writer: &SigningKey,
) -> Result<PreparedEpoch> {
    if !recipients
        .iter()
        .any(|r| r.subject == dealer_subject && &r.generation == dealer_generation)
    {
        return Err("retaining epoch dealer must be an explicit recipient keyholder".into());
    }
    if recipients.len() > 4096 || recipients.is_empty() {
        return Err("audience must have 1..4096 recipient devices".into());
    }
    if roster_bytes.is_empty() || roster_bytes.len() > 4 * 1024 * 1024 {
        return Err("missing or oversized canonical roster preimage".into());
    }
    let mut identities = std::collections::HashSet::new();
    for r in recipients {
        if !identities.insert((&r.subject, &r.device_source, r.generation)) {
            return Err("duplicate roster device entry".into());
        }
    }
    for recipient in recipients {
        if object_keys_hybrid::key_commitment(&recipient.public)? != recipient.key_commitment {
            return Err("actual recipient public key differs from roster key commitment".into());
        }
    }
    let mut key = Zeroizing::new([0; 32]);
    SystemRandom::new()
        .fill(&mut *key)
        .map_err(|_| "randomness unavailable")?;
    let mut packages = Vec::<Value>::new();
    for r in recipients {
        if r.subject.is_empty() || r.subject.len() > 4096 {
            return Err("invalid recipient subject".into());
        }
        packages.push(json!({"subject":r.subject,"capability":r.capability,"deviceSource":r.device_source,"generation":hex(&r.generation),"keyCommitment":hex(&r.key_commitment),"wrap":hex(&object_keys_hybrid::wrap(context,&r.generation,&r.public,&key)?)}));
    }
    let unsigned=serde_json::to_vec(&json!({"codec":"MINI/OBJECT-EPOCH/v1","context":hex(&context.bytes()),"audience":hex(audience),"devices":hex(devices),"history":hex(history),"authoritySnapshot":hex(authority_snapshot),"deviceSnapshot":hex(device_snapshot),"dealer":dealer_subject,"dealerGeneration":hex(dealer_generation),"writer":hex(&writer.verifying_key().to_bytes()),"packages":packages,"rosterBytes":hex(roster_bytes)})).map_err(|e|e.to_string())?;
    let signature = writer.sign(&unsigned).to_bytes();
    // Length framing leaves no alternate unsigned/signature interpretation.
    let manifest = [
        (unsigned.len() as u64).to_be_bytes().as_slice(),
        &unsigned,
        &signature,
    ]
    .concat();
    let commitment = Sha256::digest(&manifest).into();
    Ok(PreparedEpoch {
        key,
        manifest,
        commitment,
    })
}

/// Verify a retained/catch-up manifest against the admitted source commitment
/// before extracting a package. The caller separately performs current receiving
/// authorization; this operation can also serve explicitly delegated history.
pub(crate) fn receive(
    context: &Context,
    audience: &[u8; 32],
    devices: &[u8; 32],
    history: &[u8; 32],
    authority_snapshot: &[u8; 32],
    device_snapshot: &[u8; 32],
    commitment: &[u8; 32],
    writer: &[u8; 32],
    subject: &str,
    generation: &[u8; 32],
    secret: &object_keys_hybrid::DeviceSecret,
    public: &DevicePublic,
    manifest: &[u8],
) -> Result<Zeroizing<[u8; 32]>> {
    use ed25519_dalek::{Signature, VerifyingKey};
    if manifest.len() < 8 + 64 || manifest.len() > 32 * 1024 * 1024 {
        return Err("invalid epoch manifest length".into());
    }
    if Sha256::digest(manifest).as_slice() != commitment {
        return Err("manifest differs from admitted commitment".into());
    }
    let n = u64::from_be_bytes(manifest[..8].try_into().unwrap());
    if n != (manifest.len() - 8 - 64) as u64 {
        return Err("invalid manifest framing".into());
    }
    let unsigned = &manifest[8..manifest.len() - 64];
    let signature = Signature::from_slice(&manifest[manifest.len() - 64..])
        .map_err(|_| "invalid manifest signature")?;
    VerifyingKey::from_bytes(writer)
        .map_err(|_| "invalid manifest writer")?
        .verify_strict(unsigned, &signature)
        .map_err(|_| "manifest writer authentication failed")?;
    let value: Value = serde_json::from_slice(unsigned).map_err(|e| e.to_string())?;
    // Reject duplicate keys, extra fields and alternate byte encodings by exact
    // canonical reconstruction, not serde's last-duplicate-wins interpretation.
    if serde_json::to_vec(&value).map_err(|e| e.to_string())? != unsigned {
        return Err("noncanonical manifest JSON".into());
    }
    // The current policy may preserve a manifest across a later law revision.
    // Its admitted digest authenticates the original package law; require all
    // epoch identity fields to match while recovering that signed law binding.
    let encoded =
        crate::decode_hex(value["context"].as_str().ok_or("missing package context")?)?;
    let expected = context.bytes();
    if encoded.len() != expected.len()
        || encoded[..encoded.len() - 32] != expected[..expected.len() - 32]
    {
        return Err("epoch package identity mismatch".into());
    }
    let mut package_context = context.clone();
    package_context
        .law
        .copy_from_slice(&encoded[encoded.len() - 32..]);
    let context = &package_context;
    if value.as_object().map(|o| o.len()) != Some(12)
        || value["codec"] != json!("MINI/OBJECT-EPOCH/v1")
        || value["context"] != json!(hex(&context.bytes()))
        || value["audience"] != json!(hex(audience))
        || value["devices"] != json!(hex(devices))
        || value["history"] != json!(hex(history))
        || value["authoritySnapshot"] != json!(hex(authority_snapshot))
        || value["deviceSnapshot"] != json!(hex(device_snapshot))
        || value["writer"] != json!(hex(writer))
    {
        return Err("epoch manifest context mismatch".into());
    }
    let rows = value["packages"].as_array().ok_or("invalid package list")?;
    if rows.is_empty() || rows.len() > 4096 {
        return Err("invalid audience package count".into());
    }
    let dealer = value["dealer"].as_str().ok_or("missing dealer keyholder")?;
    let dealer_generation = value["dealerGeneration"]
        .as_str()
        .ok_or("missing dealer generation")?;
    let mut dealer_present = false;
    let roster = crate::decode_hex(
        value["rosterBytes"]
            .as_str()
            .ok_or("missing roster preimage")?,
    )?;
    if roster.is_empty() || roster.len() > 4 * 1024 * 1024 {
        return Err("invalid roster preimage size".into());
    }
    let mut identities = std::collections::HashSet::new();
    let mut selected = None;
    for r in rows {
        if r.as_object().map(|o| o.len()) != Some(6) {
            return Err("invalid package fields".into());
        }
        let name = r["subject"].as_str().ok_or("invalid package subject")?;
        let gen = r["generation"]
            .as_str()
            .ok_or("invalid device generation")?;
        let capability = r["capability"]
            .as_str()
            .ok_or("missing package capability")?;
        let source = r["deviceSource"]
            .as_str()
            .ok_or("missing package device source")?;
        if capability.is_empty() || source.is_empty() || !identities.insert((name, source, gen)) {
            return Err("invalid or duplicate roster package entry".into());
        }
        if name == dealer && gen == dealer_generation {
            dealer_present = true;
        }
        if name == subject && gen == hex(generation) {
            if r["keyCommitment"] != json!(hex(&object_keys_hybrid::key_commitment(public)?)) {
                return Err(
                    "received package destination differs from committed actual key".into(),
                );
            }
            if selected.is_some() {
                return Err(
                    "ambiguous subject/device generation; explicit source selection required"
                        .into(),
                );
            }
            selected = Some(r["wrap"].as_str().ok_or("invalid package wrap")?);
        }
    }
    if !dealer_present {
        return Err("manifest excludes retaining dealer keyholder".into());
    }
    object_keys_hybrid::unwrap(
        context,
        generation,
        secret,
        public,
        &crate::decode_hex(selected.ok_or("no delegated package for device")?)?,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn manifest_authenticated_catchup() {
        let (secret, public) = object_keys_hybrid::generate().unwrap();
        let c = Context {
            object: [1; 32],
            epoch: 2,
            transition: [3; 32],
            operation: [4; 32],
            law: [5; 32],
        };
        let writer = SigningKey::from_bytes(&[6; 32]);
        let key_commitment = object_keys_hybrid::key_commitment(&public).unwrap();
        let recipients = [Recipient {
            subject: "alice".into(),
            capability: "1".into(),
            device_source: "2".into(),
            generation: [7; 32],
            public,
            key_commitment,
        }];
        let mut substituted = recipients[0].public.kem.clone();
        substituted[0] ^= 1;
        let wrong_destination = [Recipient {
            subject: "alice".into(),
            capability: "1".into(),
            device_source: "2".into(),
            generation: [7; 32],
            public: DevicePublic {
                kem: substituted,
                dh: recipients[0].public.dh,
            },
            key_commitment,
        }];
        assert!(prepare(
            &c,
            &[8; 32],
            &[9; 32],
            &[10; 32],
            &[11; 32],
            &[12; 32],
            &wrong_destination,
            &[1],
            "alice",
            &[7; 32],
            &writer
        )
        .is_err());
        assert!(prepare(
            &c,
            &[8; 32],
            &[9; 32],
            &[10; 32],
            &[11; 32],
            &[12; 32],
            &recipients,
            &[1],
            "bob",
            &[7; 32],
            &writer
        )
        .is_err());
        let p = prepare(
            &c,
            &[8; 32],
            &[9; 32],
            &[10; 32],
            &[11; 32],
            &[12; 32],
            &recipients,
            &[1],
            "alice",
            &[7; 32],
            &writer,
        )
        .unwrap();
        let key = receive(
            &c,
            &[8; 32],
            &[9; 32],
            &[10; 32],
            &[11; 32],
            &[12; 32],
            &p.commitment,
            &writer.verifying_key().to_bytes(),
            "alice",
            &[7; 32],
            &secret,
            &recipients[0].public,
            &p.manifest,
        )
        .unwrap();
        assert_eq!(*key, *p.key);
        let mut later_law = c.clone();
        later_law.law = [99; 32];
        assert_eq!(
            *receive(
                &later_law,
                &[8; 32],
                &[9; 32],
                &[10; 32],
                &[11; 32],
                &[12; 32],
                &p.commitment,
                &writer.verifying_key().to_bytes(),
                "alice",
                &[7; 32],
                &secret,
                &recipients[0].public,
                &p.manifest
            )
            .unwrap(),
            *p.key
        );
        assert!(receive(
            &c,
            &[8; 32],
            &[9; 32],
            &[10; 32],
            &[13; 32],
            &[12; 32],
            &p.commitment,
            &writer.verifying_key().to_bytes(),
            "alice",
            &[7; 32],
            &secret,
            &recipients[0].public,
            &p.manifest
        )
        .is_err());

        assert!(receive(
            &c,
            &[8; 32],
            &[9; 32],
            &[10; 32],
            &[11; 32],
            &[12; 32],
            &p.commitment,
            &writer.verifying_key().to_bytes(),
            "bob",
            &[7; 32],
            &secret,
            &recipients[0].public,
            &p.manifest
        )
        .is_err());
    }
}
