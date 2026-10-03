//! Physical packet exporter only: no signing, source admission, execution or receipt.
//! Emits existing v2 socket envelope for an EXACT original SignedCall (ordinaryop2).
use std::{env,fs::{self,File,OpenOptions},io::{Read,Write},os::unix::fs::{MetadataExt,OpenOptionsExt},path::Path};
#[cfg(not(target_os="linux"))]
compile_error!("this custody exporter uses Linux O_NOFOLLOW and /proc/self ownership");
const MAX:usize=12_102_760;
const MAX_CONFIG:usize=65_536;
fn owner()->Result<u32,String>{Ok(fs::metadata("/proc/self").map_err(|e|e.to_string())?.uid())}
fn bounded(path:&Path,limit:usize)->Result<Vec<u8>,String>{
 let mut f=OpenOptions::new().read(true).custom_flags(0o400000 | 0o4000).open(path).map_err(|e|e.to_string())?; // Linux O_NOFOLLOW | O_NONBLOCK: inspect FIFOs without waiting
 let m=f.metadata().map_err(|e|e.to_string())?;
 if m.uid()!=owner()?||!m.is_file()||m.nlink()!=1||m.mode()&0o077!=0||m.len() as usize>limit {return Err("input must be bounded private regular single-link file".into());}
 let mut b=Vec::new();Read::by_ref(&mut f).take((limit+1)as u64).read_to_end(&mut b).map_err(|e|e.to_string())?;
 if b.len()!=m.len()as usize{return Err("input changed during read".into())} Ok(b)
}
fn packet(config:&[u8],pin:&str,call:&[u8])->Result<Vec<u8>,String>{
 if pin.len()!=64||!pin.is_ascii()||call.is_empty()||config.is_empty()||config.len()>MAX_CONFIG||call.len()>=MAX{return Err("invalid config, Host pin or original call".into())}
 let mut sha=[0u8;32];for(i,b)in sha.iter_mut().enumerate(){*b=u8::from_str_radix(&pin[i*2..i*2+2],16).map_err(|_|"Host pin must be hex")?;}
 let mut result=vec![2];result.extend_from_slice(&(config.len()as u32).to_le_bytes());result.extend_from_slice(config);result.extend_from_slice(&sha);result.push(2);result.extend_from_slice(call);
 if result.len()>MAX+4+1024+5+MAX_CONFIG+32{return Err("existing envelope bound exceeded".into())} Ok(result)
}
fn run()->Result<(),String>{
 let a:Vec<_>=env::args_os().collect();if a.len()!=5{return Err("usage: agreement-carrier-packet PRIVATE-CONFIG HOST-SHA256 EXACT-SIGNED-CALL NEW-PRIVATE-OUTPUT".into())}
 let output=Path::new(&a[4]);let parent=output.parent().ok_or("output needs parent")?;let m=fs::metadata(parent).map_err(|e|e.to_string())?;
 if m.uid()!=owner()?||!m.is_dir()||m.mode()&0o077!=0{return Err("output directory must be private".into())}
 let bytes=packet(&bounded(Path::new(&a[1]),MAX_CONFIG)?,a[2].to_str().ok_or("pin not UTF8")?,&bounded(Path::new(&a[3]),MAX-1)?)?;
 let mut out=OpenOptions::new().write(true).create_new(true).mode(0o600).open(output).map_err(|e|e.to_string())?;out.write_all(&bytes).map_err(|e|e.to_string())?;out.sync_all().map_err(|e|e.to_string())?;File::open(parent).and_then(|d|d.sync_all()).map_err(|e|e.to_string())?;Ok(())
}
fn main(){if let Err(e)=run(){eprintln!("agreement-carrier-packet: {e}");std::process::exit(1)}}
#[cfg(test)]mod tests{use super::*;#[test]fn exact_v2(){let b=packet(b"{}",&"ab".repeat(32),b"original").unwrap();assert_eq!(&b[..7],b"\x02\x02\0\0\0{}");assert_eq!(&b[7..39],&[0xab;32]);assert_eq!(&b[39..],b"\x02original");}#[test]fn refuses_bad_pin_and_empty(){assert!(packet(b"{}",&"xy".repeat(32),b"original").is_err());assert!(packet(b"{}",&"00".repeat(32),b"").is_err());}}
