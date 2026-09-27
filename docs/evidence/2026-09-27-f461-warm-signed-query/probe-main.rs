mod transport;
use std::path::Path;
fn main() -> Result<(), String> {
    let a: Vec<String> = std::env::args().collect();
    if a.len() != 6 { return Err("usage: probe SOCKET CONFIG HOST_SHA SIGNED OUTPUT".into()); }
    let signed = std::fs::read(&a[4]).map_err(|e| e.to_string())?;
    let reply = transport::invoke_pinned(Path::new(&a[1]), Path::new(&a[2]), &a[3], 5, &signed)?;
    if reply.first() != Some(&5) { return Err(format!("signed query refused, opcode={:?}", reply.first())); }
    std::fs::write(&a[5], &reply[1..]).map_err(|e| e.to_string())?;
    Ok(())
}
