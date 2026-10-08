//! Fixed typed one-shot helper; no socket, daemon or general command verb.
fn main() {
    let args: Vec<_>=std::env::args().collect();
    let result=match args.as_slice() {
        [_,request]=>minidregg_spk_host::volume_helper::execute(request.as_bytes()),
        _=>Err(std::io::Error::new(std::io::ErrorKind::InvalidInput,"volume-helper: one typed JSON request required")),
    };
    match result { Ok(value)=>println!("{value}"),Err(error)=>{eprintln!("{error}");std::process::exit(1);} }
}
