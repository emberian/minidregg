use mini_private_backend::{codec::*, custody::*};
use std::os::unix::fs::OpenOptionsExt;
use std::{
    io::{Read, Write},
    path::Path,
};
fn main() {
    if let Err(e) = run() {
        eprintln!("private-backend: REFUSED {e}");
        std::process::exit(1);
    }
}
fn run() -> std::io::Result<()> {
    let a: Vec<_> = std::env::args().collect();
    match a.get(1).map(String::as_str){
  Some("check-wire-fixtures") if a.len()==3=>{
   let input=std::fs::read_to_string(&a[2])?;
   if input.len()>MAX{return Err(bad("fixture capacity"));}
   let lines:Vec<_>=input.lines().collect();
   if lines.len()!=4{return Err(bad("native fixture count"));}
   let mut frames=vec![];
   for line in lines{
    let s=line.strip_prefix('[').and_then(|x|x.strip_suffix(']')).ok_or_else(||bad("fixture JSON array"))?;
    let values=if s.is_empty(){vec![]}else{s.split(',').map(|x|x.trim().parse::<u8>().map_err(|_|bad("fixture byte"))).collect::<std::io::Result<Vec<_>>>()?};
    frames.push(values);
   }
   let mut inv=[0u8;32];inv[0]=128;inv[31]=42;
   let mut pool=[0u8;32];pool[0]=128;pool[30]=48;pool[31]=57;
   let g=Generation{invocation:Nat::from_be(&inv),command:b"signed.command".to_vec(),attempt:Nat::new(3),generation:Nat::new(255),configuration:Nat::from_be(&[255;32])};
   let id=Correlation{pool:Nat::from_be(&pool),row:Nat::new(254)};
   let journal=Journal::default().reserve(id.clone(),g.clone(),Purpose::HolderPad)?;
   let expected=mini_private_backend::allocation_receipt::AllocationReceipt{
    request:request(&id,&g,Purpose::HolderPad),descriptor_bytes:vec![9,8,7],journal_bytes:journal.encode(),row_commitment:[6;32]};
   if frames[0]!=Journal::default().encode()||frames[1]!=request(&id,&g,Purpose::HolderPad)||frames[2]!=journal.encode()||frames[3]!=expected.encode(){return Err(bad("native/Rust canonical bytes differ"));}
   if parse_request(&frames[1])?!=(id,g,Purpose::HolderPad)||Journal::decode(&frames[2])?!=journal||mini_private_backend::allocation_receipt::AllocationReceipt::decode(&frames[3])?!=expected{return Err(bad("native/Rust decoded values differ"));}
   println!("PRIVATE-BACKEND NATIVE/RUST WIRE PASS (four canonical frames, arbitrary Nat digests)");Ok(())
  }
  Some("anchor") if a.len()==4=>run_anchor(Path::new(&a[2]),Path::new(&a[3])),
  Some("provision-test") if a.len()==4=>{
   let n:usize=a[3].parse().map_err(|_|bad("count"))?;
   if n==0||n>10000{return Err(bad("count bound"));}
   let mut random=std::fs::File::open("/dev/urandom")?;
   let mut rows=vec![vec![0;32];n];for row in &mut rows{random.read_exact(row)?;}
   let p=Pool::provision(Path::new(&a[2]),&rows)?;println!("provisioned {} rows; poolNatDigits={:?}",p.len(),p.id.digits());Ok(())
  }
  Some("reserve") if a.len()==8=>{
   let pool=Pool::open(Path::new(&a[2]))?;
   let row:u64=a[3].parse().map_err(|_|bad("row"))?;
   // Source receiving will supply these exact native bytes, not this test fixture.
   let g=Generation{invocation:Nat::new(7),command:vec![9],attempt:Nat::new(0),generation:Nat::new(1),configuration:Nat::new(2)};
   let crash=match a[7].as_str(){"none"=>Cut::None,"before-anchor"=>Cut::BeforeAnchor,"after-anchor"=>Cut::AfterAnchor,"after-snapshot"=>Cut::AfterSnapshot,"after-secret-read"=>Cut::AfterSecretRead,_=>return Err(bad("crash cut"))};
   let secret=reserve_release(&pool,row,g,Purpose::HolderPad,Path::new(&a[4]),Path::new(&a[5]),crash)?;
   // Explicit test output destination. CLI never prints secret material.
   let mut f=std::fs::OpenOptions::new().write(true).create_new(true).mode(0o600).open(&a[6])?;f.write_all(&secret)?;f.sync_all()?;println!("released once after durable reservation");Ok(())
  }
  Some("recover") if a.len()==4=>{let j=recover_snapshot(Path::new(&a[2]),Path::new(&a[3]))?;println!("recovered {} permanent tombstones",j.spent.len());Ok(())}
  Some("journal-empty")=>{for b in Journal::default().encode(){print!("{b:02x}");}println!();Ok(())}
  _=>Err(bad("usage: anchor ROOT FRESH_SOCKET | provision-test POOL COUNT | reserve POOL ROW SOCKET LOCAL OUTPUT CUT | recover SOCKET LOCAL | journal-empty"))
 }
}
