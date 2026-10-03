//! Native cryptographic and durable byte transport for the Lean Simplex driver.
//! Does not parse application candidates, grant authority, or count quorums.
use fips204::{
    ml_dsa_65 as dsa,
    traits::{SerDes, Signer, Verifier},
};
use fs2::FileExt;
use hmac::{Hmac, Mac};
use sha2::Sha256;
use std::os::unix::fs::OpenOptionsExt;
use std::{
    env,
    fs::{self, File, OpenOptions},
    io::{Read, Write},
    net::{TcpListener, TcpStream},
    path::Path,
    time::Duration,
};
type Error = Box<dyn std::error::Error>;
const CTX: &[u8] = b"MiniJointAgreementV1";
const MAX_FRAME: usize = 16 * 1024 * 1024;
fn read(p: &str) -> Result<Vec<u8>, Error> {
    let b = fs::read(p)?;
    if b.len() > MAX_FRAME {
        return Err("oversize".into());
    }
    Ok(b)
}
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
fn mac(key: &[u8], body: &[u8]) -> Result<Vec<u8>, Error> {
    if key.len() != 32 {
        return Err("MAC key must be 32 bytes".into());
    }
    let mut h = Hmac::<Sha256>::new_from_slice(key)?;
    h.update(CTX);
    h.update(body);
    Ok(h.finalize().into_bytes().to_vec())
}
fn verify_mac(key: &[u8], body: &[u8], tag: &[u8]) -> Result<bool, Error> {
    if key.len() != 32 {
        return Err("MAC key must be 32 bytes".into());
    }
    let mut h = Hmac::<Sha256>::new_from_slice(key)?;
    h.update(CTX);
    h.update(body);
    Ok(h.verify_slice(tag).is_ok())
}
fn verdict(b: bool) {
    println!("{}", if b { "verified" } else { "invalid" })
}
/// Stable lock inode is never renamed. Rename+directory fsync establishes the
/// persisted frame; a lost reply leaves the exact frame readable on restart.
fn cas(path: &Path, expected: &[u8], next: &[u8]) -> Result<bool, Error> {
    let dir = path.parent().ok_or("no parent")?;
    let lock = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o600)
        .open(path.with_extension("lock"))?;
    lock.lock_exclusive()?;
    let old = fs::read(path)?;
    if old != expected {
        return Ok(false);
    }
    let mut nonce = [0u8; 16];
    getrandom::getrandom(&mut nonce).map_err(|_| "rng unavailable")?;
    let tmp = dir.join(format!(".simplex-{}", hex::encode(nonce)));
    fresh(&tmp, next)?;
    fs::rename(&tmp, path)?;
    File::open(dir)?.sync_all()?;
    Ok(true)
}
fn send_frame(mut stream: &TcpStream, frame: &[u8]) -> Result<(), Error> {
    if frame.len() > MAX_FRAME {
        return Err("oversize".into());
    }
    stream.write_all(&(frame.len() as u64).to_be_bytes())?;
    stream.write_all(frame)?;
    Ok(())
}
fn receive_frame(mut stream: &TcpStream) -> Result<Vec<u8>, Error> {
    let mut length = [0; 8];
    stream.read_exact(&mut length)?;
    let n = usize::try_from(u64::from_be_bytes(length))?;
    if n > MAX_FRAME {
        return Err("oversize".into());
    }
    let mut frame = vec![0; n];
    stream.read_exact(&mut frame)?;
    Ok(frame)
}
fn run(a: &[String]) -> Result<(), Error> {
    match a.get(1).map(String::as_str){
 Some("keygen") if a.len()==4 =>{
   let (pk,sk)=dsa::try_keygen()?;
   fresh(Path::new(&a[2]),&pk.into_bytes())?;fresh(Path::new(&a[3]),&sk.into_bytes())?;
 }
 Some("mac-keygen") if a.len()==3 =>{
   let mut b=[0;32];getrandom::getrandom(&mut b).map_err(|_|"rng unavailable")?;fresh(Path::new(&a[2]),&b)?;
 }
 Some("sign") if a.len()==5 =>{
   let sk=dsa::PrivateKey::try_from_bytes(read(&a[2])?.try_into().map_err(|_|"secret length")?)?;
   let sig=sk.try_sign(&read(&a[3])?,CTX)?;fresh(Path::new(&a[4]),&sig)?;
 }
 Some("verify") if a.len()==5 =>{
   let pk=dsa::PublicKey::try_from_bytes(read(&a[2])?.try_into().map_err(|_|"public length")?)?;
   let sig=read(&a[4])?.try_into().map_err(|_|"signature length")?;
   verdict(pk.verify(&read(&a[3])?,&sig,CTX));
 }
 Some("mac") if a.len()==5 =>fresh(Path::new(&a[4]),&mac(&read(&a[2])?,&read(&a[3])?)?)?,
 Some("verify-mac") if a.len()==5=>verdict(verify_mac(&read(&a[2])?,&read(&a[3])?,&read(&a[4])?)?),
 Some("cas-lose-reply") if a.len()==5=>{
   let _=cas(Path::new(&a[2]),&read(&a[3])?,&read(&a[4])?)?;
   return Err("injected lost reply after durable CAS".into());
 }
 Some("cas") if a.len()==5=>println!("{}",if cas(Path::new(&a[2]),&read(&a[3])?,&read(&a[4])?)? {"durable"}else{"conflict"}),
 // A real TCP hop useful both to a local multi-node driver and the event harness.
 // The receiver returns bytes; authentication is performed by the Lean adapter
 // over recipient/config/epoch/instance/sequence/body before delivery.
 Some("tcp-hop") if a.len()==4=>{
   let body=read(&a[2])?;
   let listener=TcpListener::bind("127.0.0.1:0")?;
   let addr=listener.local_addr()?;
   let sender=std::thread::spawn(move || -> Result<(),String>{
     let stream=TcpStream::connect(addr).map_err(|e|e.to_string())?;
     stream.set_write_timeout(Some(Duration::from_secs(5))).map_err(|e|e.to_string())?;
     send_frame(&stream,&body).map_err(|e|e.to_string())
   });
   let (stream,_)=listener.accept()?;
   stream.set_read_timeout(Some(Duration::from_secs(5)))?;
   let body=receive_frame(&stream)?;
   sender.join().map_err(|_|"sender panic")?.map_err(|e|->Error{e.into()})?;
   fresh(Path::new(&a[3]),&body)?;
 }
 Some("tcp-send") if a.len()==4=>{
   let stream=TcpStream::connect(&a[2])?;
   stream.set_write_timeout(Some(Duration::from_secs(10)))?;
   send_frame(&stream,&read(&a[3])?)?;
 }
 Some("tcp-receive") if a.len()==4=>{
   let listener=TcpListener::bind(&a[2])?;
   let (stream,_)=listener.accept()?;
   stream.set_read_timeout(Some(Duration::from_secs(10)))?;
   fresh(Path::new(&a[3]),&receive_frame(&stream)?)?;
 }
 _=>return Err("usage: keygen PK SK | mac-keygen KEY | sign SK FRAME SIG | verify PK FRAME SIG | mac KEY FRAME TAG | verify-mac KEY FRAME TAG | cas JOURNAL EXPECTED NEXT | tcp-hop INPUT OUTPUT | tcp-send ADDR INPUT | tcp-receive ADDR OUTPUT".into())
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
    #[test]
    fn cas_restart_and_lost_reply() {
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path().join("journal");
        fresh(&p, b"before").unwrap();
        assert!(cas(&p, b"before", b"after").unwrap());
        assert!(!cas(&p, b"before", b"conflicting").unwrap());
        assert_eq!(fs::read(&p).unwrap(), b"after");
    }
    #[test]
    fn tcp_exact_roundtrip() {
        let l = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = l.local_addr().unwrap();
        let t = std::thread::spawn(move || {
            let s = TcpStream::connect(addr).unwrap();
            send_frame(&s, &[0, 255, 17]).unwrap()
        });
        let (s, _) = l.accept().unwrap();
        assert_eq!(receive_frame(&s).unwrap(), vec![0, 255, 17]);
        t.join().unwrap();
    }
}
