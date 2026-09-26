// One-shot Unix socket request/reply for the bounded Linux host probe.
// Compiled in scratch with rustc; no Mini authority or persistent service.
use std::env;
use std::io::{Read, Write};
use std::os::unix::net::{UnixListener, UnixStream};

fn main() -> std::io::Result<()> {
    let args: Vec<_> = env::args().collect();
    match args.as_slice() {
        [_, mode, path] if mode == "server" => {
            let listener = UnixListener::bind(path)?;
            let (mut peer, _) = listener.accept()?;
            let mut request = [0; 4];
            peer.read_exact(&mut request)?;
            assert_eq!(&request, b"ping");
            peer.write_all(b"pong")?;
            println!("broker-received-ping");
        }
        [_, mode, path] if mode == "client" => {
            let mut peer = UnixStream::connect(path)?;
            peer.write_all(b"ping")?;
            let mut reply = [0; 4];
            peer.read_exact(&mut reply)?;
            assert_eq!(&reply, b"pong");
            println!("broker-pong");
        }
        _ => panic!("usage: probe-socket server|client ABS_SOCKET"),
    }
    Ok(())
}
