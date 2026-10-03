//! SHA-256 in process: no subprocess protocol or repeated frame copies.
use sha2::{Digest,Sha256};
use std::fs::File;
use std::io::{self,Read};
use std::path::Path;
fn hex(bytes:impl AsRef<[u8]>)->String {bytes.as_ref().iter().map(|b|format!("{b:02x}")).collect()}
pub(crate) fn bytes(bytes:&[u8])->String {hex(Sha256::digest(bytes))}
pub(crate) fn file(path:&Path)->io::Result<String>{
    let mut file=File::open(path)?;let mut h=Sha256::new();let mut buffer=[0u8;64*1024];
    loop {let n=match file.read(&mut buffer){Ok(n)=>n,Err(e) if e.kind()==io::ErrorKind::Interrupted=>continue,Err(e)=>return Err(e)};if n==0{break}h.update(&buffer[..n]);}
    Ok(hex(h.finalize()))
}
#[cfg(test)]
mod tests{
    use super::*;
    #[test]
    fn controller_digest_standard_vectors(){
        assert_eq!(bytes(b""),"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
        assert_eq!(bytes(b"abc"),"ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
        assert_eq!(bytes(&vec![b'a';1_000_000]),"cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0");
    }
    #[test]
    fn controller_digest_stream_file_matches_original_bytes(){
        let p=std::env::temp_dir().join(format!("mini-digest-{}-{}",std::process::id(),std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        let payload=(0..200_017).map(|i|(i%251) as u8).collect::<Vec<_>>();
        std::fs::write(&p,&payload).unwrap();assert_eq!(file(&p).unwrap(),bytes(&payload));std::fs::remove_file(p).unwrap();
    }
}
