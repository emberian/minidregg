//! The byte proxy that lets a client on the participant's own machine reach a
//! deployment's public socket over ssh, so that the participant's signing key
//! never leaves that machine.
//!
//! Box side, `mini socket-proxy --socket PUBLIC-SOCKET` is the only command an
//! ssh key in proxy mode may run (`restrict,command=".../mini-socket-proxy
//! ..."`). It reads socket envelopes from stdin, forwards each one that names
//! the deployment's pinned config and a public-socket operation on its own
//! connection to the socket, and writes the socket's reply to stdout. Anything
//! that is not such a frame ends the session: a refusal frame (byte 254) when
//! a whole frame arrived, and in every case the pipe closes and nothing more is
//! read. It never runs a shell and never reads a file named by the client.
//!
//! Client side, a socket address `ssh:DEST` (`mini --remote DEST ...`) makes
//! every request that would have gone to a unix socket go to one `ssh -T DEST`
//! session per process instead. `MINI_SSH` names another ssh program, as
//! `GIT_SSH` does; ports belong in ssh config; --ssh-identity pins a workspace credential.
use crate::transport;
use std::ffi::OsString;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::Mutex;

/// Relays frames until the client closes its side. `check` decides whether a
/// frame may reach the socket; `forward` is one socket exchange. Returns the
/// number of frames relayed; every error means the session is over.
pub(crate) fn relay<R: Read, W: Write>(
    input: &mut R,
    output: &mut W,
    check: impl Fn(&[u8]) -> Result<(), &'static str>,
    mut forward: impl FnMut(&[u8]) -> Result<Vec<u8>, String>,
) -> Result<u64, String> {
    let mut relayed = 0u64;
    loop {
        let frame = match transport::read_frame(input) {
            Ok(Some(frame)) => frame,
            Ok(None) => return Ok(relayed),
            Err(error) => return Err(format!("proxy: not a socket frame ({error}); closing")),
        };
        if let Err(reason) = check(&frame) {
            let mut refusal = b"\xfeproxy: ".to_vec();
            refusal.extend_from_slice(reason.as_bytes());
            let _ = transport::write_frame(output, &refusal);
            return Err(format!("proxy: {reason}; closing"));
        }
        let reply = forward(&frame)?;
        transport::write_frame(output, &reply)
            .map_err(|error| format!("proxy: client lost the reply; status uncertain: {error}"))?;
        relayed += 1;
    }
}

/// `mini socket-proxy --socket PUBLIC-SOCKET`: the box side. The config the
/// envelopes must name is the one `mini serve` pinned beside the socket.
pub(crate) fn serve(socket: &Path) -> Result<(), String> {
    if transport::is_remote(socket) || !socket.is_absolute() {
        return Err("socket-proxy takes the absolute path of the public socket".into());
    }
    let config = transport::read_config(&socket.with_extension("config"))?;
    let catalog = transport::catalog_enabled(&config)?;
    let stdin = io::stdin();
    let stdout = io::stdout();
    relay(
        &mut stdin.lock(),
        &mut stdout.lock(),
        |frame| transport::public_envelope(frame, &config, catalog),
        |frame| transport::exchange_unix(socket, frame),
    )
    .map(|_| ())
}

struct Session {
    destination: String,
    identity: Option<PathBuf>,
    child: Child,
    stdin: ChildStdin,
    stdout: ChildStdout,
}

impl Session {
    fn close(mut self) {
        drop(self.stdin);
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

static SESSIONS: Mutex<Vec<Session>> = Mutex::new(Vec::new());

fn ssh_program() -> OsString {
    std::env::var_os("MINI_SSH")
        .filter(|program| !program.is_empty())
        .unwrap_or_else(|| "ssh".into())
}

fn open(destination: &str) -> Result<Session, String> {
    transport::remote_destination(destination)?;
    let program = ssh_program();
    let mut command = Command::new(&program);
    command.args(["-T", "-o", "BatchMode=yes"]);
    let identity = crate::ssh_identity().map(Path::to_path_buf);
    if let Some(identity) = &identity { command.arg("-i").arg(identity).args(["-o", "IdentitiesOnly=yes"]); }
    let mut child = command.args(["--", destination])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .map_err(|error| format!("cannot start {}: {error}", program.to_string_lossy()))?;
    let stdin = child.stdin.take().ok_or("ssh stdin unavailable")?;
    let stdout = child.stdout.take().ok_or("ssh stdout unavailable")?;
    transport::set_nonblocking(&stdin).map_err(|error| format!("cannot bound ssh input: {error}"))?;
    Ok(Session {
        destination: destination.to_owned(),
        identity,
        child,
        stdin,
        stdout,
    })
}

/// One request over this process's ssh session to `destination`, opened on
/// first use. A failed exchange closes the session; the next request opens a
/// new one. As with the unix socket, a failure after the write leaves the
/// request's status uncertain.
pub(crate) fn exchange(destination: &str, frame: &[u8]) -> Result<Vec<u8>, String> {
    let mut sessions = SESSIONS
        .lock()
        .map_err(|_| "remote session table poisoned")?;
    let index = match sessions.iter().position(|s| s.destination == destination && s.identity.as_deref() == crate::ssh_identity()) {
        Some(index) => index,
        None => {
            sessions.push(open(destination)?);
            sessions.len() - 1
        }
    };
    let session = &mut sessions[index];
    match transport::exchange_stdio(&mut session.stdin, &mut session.stdout, frame) {
        Ok(reply) => Ok(reply),
        Err(error) => {
            sessions.swap_remove(index).close();
            Err(error)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;
    use std::os::unix::net::{UnixListener, UnixStream};
    use std::path::PathBuf;

    const CONFIG: &[u8] = br#"{"domain":"7"}"#;

    fn envelope(config: &[u8], request: &[u8]) -> Vec<u8> {
        let mut frame = vec![2];
        frame.extend_from_slice(&(config.len() as u32).to_le_bytes());
        frame.extend_from_slice(config);
        frame.extend_from_slice(&[0xab; 32]);
        frame.extend_from_slice(request);
        frame
    }

    fn framed(frames: &[&[u8]]) -> Vec<u8> {
        let mut bytes = Vec::new();
        for frame in frames {
            transport::write_frame(&mut bytes, frame).unwrap();
        }
        bytes
    }

    fn check(frame: &[u8]) -> Result<(), &'static str> {
        transport::public_envelope(frame, CONFIG, false)
    }

    fn replies(mut bytes: &[u8]) -> Vec<Vec<u8>> {
        let mut out = Vec::new();
        while let Some(frame) = transport::read_frame(&mut bytes).unwrap() {
            out.push(frame);
        }
        out
    }

    #[test]
    fn bytes_that_are_not_a_frame_close_the_pipe_before_the_socket() {
        for garbage in [
            b"ls -la /var/lib/mini\n".to_vec(),          // text: its "length" exceeds any frame
            vec![0, 0, 0, 0],                             // zero-length frame
            vec![100, 0, 0, 0, 1, 2, 3],                  // truncated frame
            vec![7, 0],                                   // truncated length
        ] {
            let mut forwarded = 0;
            let mut output = Vec::new();
            let result = relay(&mut Cursor::new(garbage.clone()), &mut output, check, |_| {
                forwarded += 1;
                Ok(vec![0])
            });
            assert!(result.unwrap_err().contains("not a socket frame"), "{garbage:?}");
            assert_eq!(forwarded, 0);
            assert!(output.is_empty(), "no reply to a non-frame");
        }
    }

    #[test]
    fn a_frame_the_public_socket_would_refuse_is_refused_and_ends_the_session() {
        let wrong_config = envelope(br#"{"domain":"8"}"#, &[0]);
        let operator_only = envelope(CONFIG, &[22, 1]);
        let bad_version = {
            let mut frame = envelope(CONFIG, &[0]);
            frame[0] = 3;
            frame
        };
        let good = envelope(CONFIG, &[0]);
        for (bad, reason) in [
            (&wrong_config, "config pin mismatch"),
            (&operator_only, "operation unavailable on selected socket"),
            (&bad_version, "invalid socket envelope"),
        ] {
            let mut forwarded = 0;
            let mut output = Vec::new();
            let input = framed(&[bad, &good]);
            let error = relay(&mut Cursor::new(input), &mut output, check, |_| {
                forwarded += 1;
                Ok(vec![0])
            })
            .unwrap_err();
            assert!(error.contains(reason), "{error}");
            assert_eq!(forwarded, 0, "nothing after the refused frame is read");
            let expected = [b"\xfeproxy: ".as_slice(), reason.as_bytes()].concat();
            assert_eq!(replies(&output), vec![expected]);
        }
    }

    #[test]
    fn garbage_after_a_relayed_frame_ends_the_session_after_its_reply() {
        let good = envelope(CONFIG, &[0]);
        let mut input = framed(&[&good]);
        input.extend_from_slice(b"\xff\xff\xff\xffjunk");
        let mut output = Vec::new();
        let error = relay(&mut Cursor::new(input), &mut output, check, |_| Ok(vec![0, 42])).unwrap_err();
        assert!(error.contains("not a socket frame"));
        assert_eq!(replies(&output), vec![vec![0, 42]]);
    }

    fn scratch(label: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "mini-proxy-{label}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        dir
    }

    /// A request round-trips client -> stdio pipe -> proxy -> unix socket ->
    /// fake Host and back, twice over one session, each on its own socket
    /// connection, and the proxy exits cleanly when the client closes.
    #[test]
    fn requests_round_trip_through_a_pipe_pair_and_the_socket() {
        let dir = scratch("roundtrip");
        let socket = dir.join("mini.sock");
        let listener = UnixListener::bind(&socket).unwrap();
        let host = std::thread::spawn(move || {
            let mut seen = Vec::new();
            for _ in 0..2 {
                let (mut connection, _) = listener.accept().unwrap();
                let envelope = transport::read_frame(&mut connection).unwrap().unwrap();
                let request = envelope[5 + CONFIG.len() + 32..].to_vec();
                let mut reply = vec![request[0]];
                reply.extend(request[1..].iter().rev());
                transport::write_frame(&mut connection, &reply).unwrap();
                seen.push(envelope);
            }
            seen
        });
        let (mut client_out, mut proxy_in) = UnixStream::pair().unwrap();
        let (mut proxy_out, mut client_in) = UnixStream::pair().unwrap();
        let proxy_socket = socket.clone();
        let proxy = std::thread::spawn(move || {
            relay(&mut proxy_in, &mut proxy_out, check, |frame| {
                transport::exchange_unix(&proxy_socket, frame)
            })
        });
        transport::set_nonblocking(&client_out).unwrap();
        let first = envelope(CONFIG, &[5, 1, 2, 3]);
        let second = envelope(CONFIG, &[3, 9, 8]);
        assert_eq!(
            transport::exchange_stdio(&mut client_out, &mut client_in, &first).unwrap(),
            vec![5, 3, 2, 1]
        );
        assert_eq!(
            transport::exchange_stdio(&mut client_out, &mut client_in, &second).unwrap(),
            vec![3, 8, 9]
        );
        drop(client_out);
        assert_eq!(proxy.join().unwrap().unwrap(), 2);
        assert_eq!(host.join().unwrap(), vec![first, second], "the socket saw the exact bytes");
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn remote_addresses_parse_and_refuse_option_shaped_destinations() {
        let address = transport::remote_address("mini@dregg-workhorse").unwrap();
        assert_eq!(address, PathBuf::from("ssh:mini@dregg-workhorse"));
        assert!(transport::is_remote(&address));
        assert_eq!(transport::pinned_address(&address).unwrap(), "ssh:mini@dregg-workhorse");
        assert!(!transport::is_remote(Path::new("/var/lib/mini/store/public/mini.sock")));
        for bad in ["", "-oProxyCommand=sh", "mini@host;id", "a b", "mini@host:22"] {
            assert!(transport::remote_address(bad).is_err(), "{bad}");
        }
        assert!(transport::endpoint(Path::new("ssh:-oProxyCommand=x")).is_err());
        assert!(serve(Path::new("ssh:mini@host")).is_err());
        assert!(serve(Path::new("relative.sock")).is_err());
    }
}
