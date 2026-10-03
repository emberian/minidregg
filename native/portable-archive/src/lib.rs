//! Private byte custody shared by portable continuation and agreement repair.
//! A manifest is a physical inventory, not current source authority. Its exact
//! canonical bytes must be bound by PortableContinuationManifest. No generation,
//! spent-anchor, source-obligation or native admission is decided here.
pub mod durable_file;
use durable_file::private_file;
use fs2::FileExt;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::Path;
pub const CHUNK_BYTES: usize = 65536;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all="camelCase", deny_unknown_fields)]
pub struct Chunk { pub sha256: String, pub bytes: u64 }
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all="camelCase", deny_unknown_fields)]
pub struct FileManifest {
    pub protocol: String,
    /// Source-selected logical coordinate; never used as a physical path.
    pub coordinate: String,
    pub bytes: u64,
    pub sha256: String,
    pub chunks: Vec<Chunk>,
}
fn invalid(s: &str) -> io::Error { io::Error::new(io::ErrorKind::InvalidData,s) }
fn hash(bytes:&[u8])->String { hex::encode(Sha256::digest(bytes)) }
fn canonical_hash(s:&str)->bool { s.len()==64 && s.bytes().all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c)) }
fn owned_directory(root:&Path)->io::Result<()> {
    let m=fs::symlink_metadata(root)?;
    if !m.is_dir() || m.uid()!=unsafe{libc::geteuid()} || m.mode()&0o077!=0 { return Err(invalid("archive directory custody invalid")); }
    Ok(())
}
pub fn initialize(root:&Path)->io::Result<()> {
    use std::os::unix::fs::DirBuilderExt;
    if !root.exists() { fs::DirBuilder::new().mode(0o700).create(root)?; File::open(root.parent().ok_or_else(||invalid("archive parent absent"))?)?.sync_all()?; }
    owned_directory(root)
}
fn exact_chunk(root:&Path,chunk:&Chunk)->io::Result<Vec<u8>> {
    if !canonical_hash(&chunk.sha256) || chunk.bytes==0 || chunk.bytes>CHUNK_BYTES as u64 {return Err(invalid("chunk selector invalid"));}
    owned_directory(root)?;
    let mut f=private_file(&root.join(&chunk.sha256))?;
    if f.metadata()?.len()!=chunk.bytes {return Err(invalid("chunk length differs"));}
    let mut bytes=Vec::with_capacity(CHUNK_BYTES); (&mut f).take(chunk.bytes+1).read_to_end(&mut bytes)?;
    if bytes.len() as u64!=chunk.bytes {return Err(invalid("chunk changed during read"));}
    if hash(&bytes)!=chunk.sha256 {return Err(invalid("chunk bytes differ"));}
    Ok(bytes)
}
/// Incoming bytes from ANY provider must match the exact selected chunk. Local
/// corruption is replaceable only with the same authenticated content address.
pub fn repair_chunk(root:&Path,chunk:&Chunk,incoming:&Path)->io::Result<()> {
    initialize(root)?;
    if !canonical_hash(&chunk.sha256) || chunk.bytes==0 || chunk.bytes>CHUNK_BYTES as u64 {return Err(invalid("chunk selector invalid"));}
    let mut source=private_file(incoming)?;
    if source.metadata()?.len()!=chunk.bytes {return Err(invalid("incoming chunk length differs"));}
    let mut bytes=Vec::with_capacity(CHUNK_BYTES); (&mut source).take(chunk.bytes+1).read_to_end(&mut bytes)?;
    if bytes.len() as u64!=chunk.bytes {return Err(invalid("incoming chunk changed during read"));}
    if hash(&bytes)!=chunk.sha256 {return Err(invalid("incoming chunk digest differs"));}
    retain_chunk(root,&bytes)?; exact_chunk(root,chunk)?; Ok(())
}
fn retain_chunk(root:&Path,bytes:&[u8])->io::Result<Chunk> {
    let chunk=Chunk{sha256:hash(bytes),bytes:bytes.len() as u64};
    let target=root.join(&chunk.sha256);
    let lock=OpenOptions::new().read(true).write(true).create(true).truncate(false)
        .mode(0o600).custom_flags(libc::O_NOFOLLOW).open(root.join(format!("{}.lock",chunk.sha256)))?;
    let m=lock.metadata()?;
    if !m.is_file() || m.nlink()!=1 || m.uid()!=unsafe{libc::geteuid()} || m.mode()&0o077!=0 {return Err(invalid("chunk lock custody invalid"));}
    lock.lock_exclusive()?;
    if exact_chunk(root,&chunk).is_ok() {return Ok(chunk);}
    if let Ok(m)=fs::symlink_metadata(&target) {
        if !m.is_file() || m.nlink()!=1 || m.uid()!=unsafe{libc::geteuid()} || m.mode()&0o077!=0 {return Err(invalid("existing corrupt chunk custody invalid"));}
    }
    let mut nonce=[0u8;16];getrandom::getrandom(&mut nonce).map_err(|e|io::Error::other(e.to_string()))?;
    let staging=root.join(format!(".chunk-{}",hex::encode(nonce)));
    let mut output=OpenOptions::new().write(true).create_new(true).mode(0o600).open(&staging)?;
    output.write_all(bytes)?; output.sync_all()?;
    fs::rename(&staging,&target)?; File::open(root)?.sync_all()?;
    exact_chunk(root,&chunk)?; Ok(chunk)
}
/// Capture under the EXISTING source pause/driver lock. Double-reading catches
/// changing input but cannot replace that source synchronization contract.
pub fn capture(root:&Path,coordinate:String,source:&Path)->io::Result<FileManifest> {
    initialize(root)?;
    if coordinate.is_empty() || coordinate.len()>4096 {return Err(invalid("artifact coordinate invalid"));}
    let mut f=private_file(source)?;let original=f.metadata()?.len();
    let mut remaining=original;let mut chunks=Vec::new();let mut aggregate=Sha256::new();
    let mut buffer=[0u8;CHUNK_BYTES];
    while remaining>0 {
        let count=usize::try_from(remaining.min(CHUNK_BYTES as u64)).unwrap();
        f.read_exact(&mut buffer[..count])?;
        aggregate.update(&buffer[..count]);chunks.push(retain_chunk(root,&buffer[..count])?);remaining-=count as u64;
    }
    let sha256=hex::encode(aggregate.finalize());
    f.seek(SeekFrom::Start(0))?;let mut checked=Sha256::new();let mut seen=0u64;
    loop {let n=f.read(&mut buffer)?;if n==0 {break;}checked.update(&buffer[..n]);seen=seen.checked_add(n as u64).ok_or_else(||invalid("artifact size overflow"))?;}
    if seen!=original || hex::encode(checked.finalize())!=sha256 {return Err(invalid("source changed during capture"));}
    let manifest=FileManifest{protocol:"mini-portable-artifact-chunks-v1".into(),coordinate,bytes:original,sha256,chunks};
    verify(root,&manifest)?;Ok(manifest)
}
fn check_manifest(manifest:&FileManifest)->io::Result<()> {
    if manifest.protocol!="mini-portable-artifact-chunks-v1" || manifest.coordinate.is_empty() || manifest.coordinate.len()>4096 || !canonical_hash(&manifest.sha256) {return Err(invalid("artifact manifest invalid"));}
    let mut total=0u64;
    for (index,chunk) in manifest.chunks.iter().enumerate() {
        if !canonical_hash(&chunk.sha256) || chunk.bytes==0 || chunk.bytes>CHUNK_BYTES as u64 || (index+1<manifest.chunks.len() && chunk.bytes!=CHUNK_BYTES as u64) {return Err(invalid("artifact chunk placement invalid"));}
        total=total.checked_add(chunk.bytes).ok_or_else(||invalid("artifact size overflow"))?;
    }
    if total!=manifest.bytes {return Err(invalid("artifact inventory size differs"));} Ok(())
}
pub fn verify(root:&Path,manifest:&FileManifest)->io::Result<()> {
    check_manifest(manifest)?;let mut aggregate=Sha256::new();
    for chunk in &manifest.chunks {aggregate.update(exact_chunk(root,chunk)?);}
    if hex::encode(aggregate.finalize())!=manifest.sha256 {return Err(invalid("artifact aggregate digest differs"));}Ok(())
}
/// At most ONE physical chunk's worth per request. Position and length come
/// from the source-bound trusted manifest; no replacement digest is accepted.
pub fn read_range(root:&Path,manifest:&FileManifest,offset:u64,count:usize)->io::Result<Vec<u8>> {
    check_manifest(manifest)?;
    if count>CHUNK_BYTES || offset>manifest.bytes || count as u64>manifest.bytes-offset {return Err(invalid("range exceeds bounded artifact"));}
    let mut output=Vec::with_capacity(count);let end=offset+count as u64;let mut start=0u64;
    for chunk in &manifest.chunks {
        let stop=start+chunk.bytes;
        if start<end && stop>offset {
            let bytes=exact_chunk(root,chunk)?;
            let from=offset.saturating_sub(start) as usize;let until=(end.min(stop)-start) as usize;
            output.extend_from_slice(&bytes[from..until]);
        }
        start=stop;if start>=end {break;}
    }
    if output.len()!=count {return Err(invalid("range incomplete"));}Ok(output)
}
/// New output only; no app activation, provider replacement or authority change.
/// Caller may acknowledge custody only after this completes exact readback.
pub fn restore_new(root:&Path,manifest:&FileManifest,target:&Path)->io::Result<()> {
    check_manifest(manifest)?;
    let mut output=OpenOptions::new().write(true).create_new(true).mode(0o600).open(target)?;
    let mut aggregate=Sha256::new();
    for chunk in &manifest.chunks {let bytes=exact_chunk(root,chunk)?;aggregate.update(&bytes);output.write_all(&bytes)?;}
    if hex::encode(aggregate.finalize())!=manifest.sha256 {return Err(invalid("restored artifact aggregate differs"));}
    output.sync_all()?;File::open(target.parent().ok_or_else(||invalid("restore parent absent"))?)?.sync_all()?;
    let mut checked=private_file(target)?;let mut h=Sha256::new();let mut buffer=[0u8;CHUNK_BYTES];
    loop {let n=checked.read(&mut buffer)?;if n==0 {break;}h.update(&buffer[..n]);}
    if checked.metadata()?.len()!=manifest.bytes || hex::encode(h.finalize())!=manifest.sha256 {return Err(invalid("restore readback differs"));}Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn file(path:&Path,bytes:&[u8]) {let mut f=OpenOptions::new().write(true).create_new(true).mode(0o600).open(path).unwrap();f.write_all(bytes).unwrap();f.sync_all().unwrap();}
    #[test]
    fn repair_offline_source_and_bounded_cross_chunk_retrieval() {
        let d=tempfile::tempdir().unwrap();let source=d.path().join("full");
        let content=(0..CHUNK_BYTES*3+11).map(|i|(i%251) as u8).collect::<Vec<_>>();file(&source,&content);
        let root=d.path().join("archive");let m=capture(&root,"native/source+resident/providerHold+outbox".into(),&source).unwrap();
        // Remove ONE local shard to model unavailable custody, entirely inside
        // this isolated test; source admission and semantic history stay intact.
        let victim=&m.chunks[1];let offered=d.path().join("peer-chunk");file(&offered,&content[CHUNK_BYTES..2*CHUNK_BYTES]);
        fs::remove_file(root.join(&victim.sha256)).unwrap();assert!(verify(&root,&m).is_err());
        repair_chunk(&root,victim,&offered).unwrap();verify(&root,&m).unwrap();
        assert_eq!(read_range(&root,&m,(CHUNK_BYTES-7) as u64,19).unwrap(),content[CHUNK_BYTES-7..CHUNK_BYTES+12]);
        let restored=d.path().join("restored");restore_new(&root,&m,&restored).unwrap();assert_eq!(fs::read(restored).unwrap(),content);
    }
    #[test]
    fn forged_wrong_position_missing_and_oversized_ranges_refuse() {
        let d=tempfile::tempdir().unwrap();let source=d.path().join("full");let content=vec![7;CHUNK_BYTES+13];file(&source,&content);
        let root=d.path().join("archive");let m=capture(&root,"consensus/context+roster+replay+old-view-liabilities".into(),&source).unwrap();
        let wrong=d.path().join("wrong");file(&wrong,&vec![8;CHUNK_BYTES]);
        assert!(repair_chunk(&root,&m.chunks[0],&wrong).is_err());
        let mut misplaced=m.clone();misplaced.chunks.swap(0,1);assert!(verify(&root,&misplaced).is_err());
        assert!(read_range(&root,&m,0,CHUNK_BYTES+1).is_err());assert!(read_range(&root,&m,m.bytes,1).is_err());
        assert!(restore_new(&root,&m,&source).is_err());assert_eq!(fs::read(source).unwrap(),content);
    }
}
