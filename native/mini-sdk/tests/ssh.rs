//! The ssh route against a REAL ssh client and a REAL sshd (not the in-process stand-in the unit
//! tests use). Needs a destination the invoking user can reach with key authentication and a host
//! key already in known_hosts; it changes no configuration anywhere: a throwaway ssh config (`-F`)
//! names a `RemoteCommand` (the frame stand-in, `tests/fixtures/ssh-standin.sh`, in `remote-answer`
//! mode) in place of the box's forced `mini socket-proxy` command.
//!
//! Run (hbox, as the lane user, sshd on localhost):
//!   MINI_SDK_SSH_TEST_HOST=localhost MINI_SDK_SSH_TEST_IDENTITY=~/.ssh/id_boxlocal \
//!     cargo test --features native --test ssh -- --ignored
//! `MINI_SDK_SSH_TEST_HOST` is the real address (HostName); the SDK is given the Host alias.
#![cfg(feature = "native")]
use std::path::PathBuf;
use std::time::Duration;

use mini_sdk::operator::{request, Failure, Operator, Reply, Route, Ssh};

const STANDIN: &str = include_str!("fixtures/ssh-standin.sh");

fn scratch(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("mini-sdk-realssh-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn env(name: &str) -> String {
    std::env::var(name).unwrap_or_else(|_| panic!("{name} must be set to run the real-ssh tests"))
}

fn operator(dir: &PathBuf, alias: &str, host: &str, identity: &str, remote_mode: &str) -> Operator {
    let script = dir.join("standin.sh");
    std::fs::write(&script, STANDIN).unwrap();
    let config = dir.join("ssh_config");
    std::fs::write(&config, format!(
        "Host {alias}\n  HostName {host}\n  HostKeyAlias {host}\n  IdentityFile {identity}\n  RemoteCommand env TMPDIR={} /bin/sh {} {remote_mode}\n  RequestTTY no\n",
        dir.display(), script.display())).unwrap();
    std::fs::write(dir.join("host.config"), b"{}").unwrap();
    let mut ssh = Ssh::new(alias).unwrap();
    ssh.command = vec!["ssh".into()]; // the real client, not $MINI_SSH
    ssh.config = Some(config);
    ssh.connect_timeout = Duration::from_secs(20);
    Operator::new(Route::Ssh(ssh), &dir.join("host.config"), None).unwrap()
}

#[test]
#[ignore = "needs a reachable sshd: set MINI_SDK_SSH_TEST_HOST and MINI_SDK_SSH_TEST_IDENTITY"]
fn real_ssh_carries_the_operator_frames_and_reuses_one_session() {
    let (host, identity) = (env("MINI_SDK_SSH_TEST_HOST"), env("MINI_SDK_SSH_TEST_IDENTITY"));
    let dir = scratch("ok");
    let op = operator(&dir, "mini-sdk-realssh", &host, &identity, "remote-answer");
    let req = dir.join("mini-sdk-ssh-remote-answer.req");
    assert_eq!(op.call(2, b"first"), Ok(Reply::Answer(b"ok".to_vec())));
    assert_eq!(op.call(2, b"second"), Ok(Reply::Answer(b"ok".to_vec())));
    // The remote process saw exactly the two request frames, in order, byte for byte.
    let seen = std::fs::read(&req).expect("the remote stand-in wrote the requests it received");
    assert_eq!(seen, [request(b"{}", None, 2, b"first").unwrap(), request(b"{}", None, 2, b"second").unwrap()].concat());
}

#[test]
#[ignore = "needs a reachable sshd: set MINI_SDK_SSH_TEST_HOST and MINI_SDK_SSH_TEST_IDENTITY"]
fn real_ssh_refuses_an_unknown_host_key_by_name_with_nothing_sent() {
    let (_, identity) = (env("MINI_SDK_SSH_TEST_HOST"), env("MINI_SDK_SSH_TEST_IDENTITY"));
    let dir = scratch("hostkey");
    // The same machine, but under a host-key name nobody has in known_hosts: host key checking is on.
    let host = env("MINI_SDK_SSH_TEST_HOST");
    let script = dir.join("config");
    std::fs::write(&script, format!("Host mini-sdk-unknown\n  HostName {host}\n  HostKeyAlias mini-sdk-never-seen-{}\n  IdentityFile {identity}\n", std::process::id())).unwrap();
    std::fs::write(dir.join("host.config"), b"{}").unwrap();
    let mut ssh = Ssh::new("mini-sdk-unknown").unwrap();
    ssh.command = vec!["ssh".into()];
    ssh.config = Some(script);
    let op = Operator::new(Route::Ssh(ssh), &dir.join("host.config"), None).unwrap();
    match op.call(2, b"call") {
        Err(Failure::Unsent(said)) => assert!(said.contains("host key verification failed"), "{said}"),
        other => panic!("expected a named certainly-unsent refusal, got {other:?}"),
    }
}
