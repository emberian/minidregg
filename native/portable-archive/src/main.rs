//! Physical-only operator experiment/helper. Inputs do not grant installation,
//! overwrite, private share export or participant authority.
use minidregg_portable_archive::{self as archive, durable_file,FileManifest};
use std::fs::{File,OpenOptions};
use std::io::{self,Read,Write};
use std::os::unix::fs::OpenOptionsExt;
use std::path::Path;
fn write_exact(path:&Path,bytes:&[u8])->io::Result<()> {
    match OpenOptions::new().write(true).create_new(true).mode(0o600).open(path) {
        Ok(mut file)=>{file.write_all(bytes)?;file.sync_all()?;File::open(path.parent().ok_or_else(||io::Error::other("parent absent"))?)?.sync_all()?;}
        Err(error) if error.kind()==io::ErrorKind::AlreadyExists=>{
            let mut file=durable_file::private_file(path)?;
            if file.metadata()?.len()!=bytes.len() as u64 {return Err(io::Error::other("retained output differs"));}
            let mut actual=Vec::new();file.read_to_end(&mut actual)?;
            if actual!=bytes {return Err(io::Error::other("retained output differs"));}
        }
        Err(error)=>return Err(error),
    }
    let mut file=durable_file::private_file(path)?;let mut actual=Vec::new();file.read_to_end(&mut actual)?;
    if actual!=bytes {return Err(io::Error::other("retained output readback differs"));}Ok(())
}
fn manifest(path:&str)->Result<FileManifest,Box<dyn std::error::Error>> {
    Ok(serde_json::from_reader(durable_file::private_file(Path::new(path))?)?)
}
fn run(args:&[String])->Result<(),Box<dyn std::error::Error>> {
    match args.get(1).map(String::as_str) {
        Some("cas") if args.len()==5=>println!("{}",if durable_file::compare_replace(Path::new(&args[2]),Path::new(&args[3]),Path::new(&args[4]))? {"durable"} else {"conflict"}),
        Some("cas-lose-reply") if args.len()==5=>{
            durable_file::compare_replace(Path::new(&args[2]),Path::new(&args[3]),Path::new(&args[4]))?;
            return Err("lost reply after physical CAS".into());
        }
        Some("capture") if args.len()==6=>{
            let value=archive::capture(Path::new(&args[2]),args[3].clone(),Path::new(&args[4]))?;
            write_exact(Path::new(&args[5]),&serde_json::to_vec(&value)?)?;
            println!("retained");
        }
        Some("verify") if args.len()==4=>{archive::verify(Path::new(&args[2]),&manifest(&args[3])?)?;println!("retained");}
        Some("restore-new") if args.len()==5=>{archive::restore_new(Path::new(&args[2]),&manifest(&args[3])?,Path::new(&args[4]))?;println!("retained");}
        Some("read-range") if args.len()==7=>{
            let bytes=archive::read_range(Path::new(&args[2]),&manifest(&args[3])?,args[4].parse()?,args[5].parse()?)?;
            write_exact(Path::new(&args[6]),&bytes)?;println!("retrieved");
        }
        Some("repair-chunk") if args.len()==6=>{
            let m=manifest(&args[3])?;let index:usize=args[4].parse()?;
            archive::repair_chunk(Path::new(&args[2]),m.chunks.get(index).ok_or("chunk position absent")?,Path::new(&args[5]))?;
            println!("retained");
        }
        _=>return Err("usage: minidregg-portable-archive cas|cas-lose-reply JOURNAL EXPECTED NEXT; capture ARCHIVE SOURCE_COORDINATE FILE INVENTORY; verify ARCHIVE INVENTORY; restore-new ARCHIVE INVENTORY NEWFILE; read-range ARCHIVE INVENTORY OFFSET COUNT NEWFILE; repair-chunk ARCHIVE INVENTORY INDEX INCOMING".into()),
    }
    Ok(())
}
fn main() {if let Err(error)=run(&std::env::args().collect::<Vec<_>>()) {eprintln!("portable custody refused: {error}");std::process::exit(1);}}
