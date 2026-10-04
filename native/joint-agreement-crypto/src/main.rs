//! Native cryptographic, durable-journal and transport helper for the Lean Simplex driver.
//! Does not parse application candidates, grant authority, or count quorums.
use fips204::{ml_dsa_65 as dsa, traits::SerDes};
use hmac::{Hmac, Mac};
use sha2::Sha256;
use std::os::unix::fs::OpenOptionsExt;
use std::{
    env,
    fs::OpenOptions,
    io::Write,
    path::Path,
};
mod session;
type Error = Box<dyn std::error::Error>;
pub(crate) const CTX: &[u8] = b"MiniJointAgreementV1";
pub(crate) const MAX_FRAME: usize = 16 * 1024 * 1024;
fn fresh(p: &Path, b: &[u8]) -> Result<(), Error> {
    let mut f = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(p)?;
    f.write_all(b)?;
    f.sync_all()?;
    Ok(())
}
pub(crate) fn mac(key: &[u8], body: &[u8]) -> Result<Vec<u8>, Error> {
    if key.len() != 32 {
        return Err("MAC key must be 32 bytes".into());
    }
    let mut h = Hmac::<Sha256>::new_from_slice(key)?;
    h.update(CTX);
    h.update(body);
    Ok(h.finalize().into_bytes().to_vec())
}
pub(crate) fn verify_mac(key: &[u8], body: &[u8], tag: &[u8]) -> Result<bool, Error> {
    if key.len() != 32 {
        return Err("MAC key must be 32 bytes".into());
    }
    let mut h = Hmac::<Sha256>::new_from_slice(key)?;
    h.update(CTX);
    h.update(body);
    Ok(h.verify_slice(tag).is_ok())
}
fn run(a: &[String]) -> Result<(), Error> {
    match a.get(1).map(String::as_str) {
        // Setup only: fresh committee and pairwise key material.
        Some("keygen") if a.len() == 4 => {
            let (pk, sk) = dsa::try_keygen()?;
            fresh(Path::new(&a[2]), &pk.into_bytes())?;
            fresh(Path::new(&a[3]), &sk.into_bytes())?;
        }
        Some("mac-keygen") if a.len() == 3 => {
            let mut b = [0; 32];
            getrandom::getrandom(&mut b).map_err(|_| "rng unavailable")?;
            fresh(Path::new(&a[2]), &b)?;
        }
        // Every signature, MAC, journal append and packet of a running replica
        // goes through one long-lived session: no subprocess per operation.
        Some("session") => session::run(&a[2..])?,
        _ => return Err("usage: keygen PK SK | mac-keygen KEY | session [--sk SK] [--journal LOG] [--listen ADDR] [--peer I=ADDR]... [--pair I=KEY]...".into()),
    }
    Ok(())
}
fn main() {
    if let Err(e) = run(&env::args().collect::<Vec<_>>()) {
        eprintln!("{e}");
        std::process::exit(1)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use fips204::traits::{Signer, Verifier};
    #[test]
    fn mldsa_tamper_rejected() {
        let (pk, sk) = dsa::try_keygen().unwrap();
        let sig = sk.try_sign(b"exact-candidate", CTX).unwrap();
        assert!(pk.verify(b"exact-candidate", &sig, CTX));
        assert!(!pk.verify(b"changed-candidate", &sig, CTX));
    }
    #[test]
    fn mac_sender_recipient_binding() {
        let tag = mac(&[7; 32], b"sender0-recipient1-view4").unwrap();
        assert!(verify_mac(&[7; 32], b"sender0-recipient1-view4", &tag).unwrap());
        assert!(!verify_mac(&[7; 32], b"sender0-recipient2-view4", &tag).unwrap());
    }
}
