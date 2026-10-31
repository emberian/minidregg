//! Fixed typed one-shot helper; no socket, daemon or general command verb.
// print!/println!/eprint!/eprintln!: a closed standard output ends the command with 141, never a
// panic (`mini_streams`).
#[macro_use]
extern crate mini_streams;
fn run_main() {
    let args: Vec<_>=std::env::args().collect();
    let result=match args.as_slice() {
        [_,request]=>minidregg_spk_host::volume_helper::execute(request.as_bytes()),
        _=>Err(std::io::Error::new(std::io::ErrorKind::InvalidInput,"volume-helper: one typed JSON request required")),
    };
    match result { Ok(value)=>println!("{value}"),Err(error)=>{eprintln!("{error}");std::process::exit(1);} }
}

fn main() -> std::process::ExitCode {
    mini_streams::guard(|| {
        run_main();
        std::process::ExitCode::SUCCESS
    })
}
