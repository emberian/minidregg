//! The ssh:DEST route against a REAL ssh client, a REAL unprivileged sshd and a REAL scratch Host.
//! Driven by `ssh-e2e.sh`, which starts the Store (the candidate's Host behind its public socket),
//! an sshd on 127.0.0.1 whose only authorised key is forced to `mini socket-proxy`, and the member's
//! ssh configurations; it names them in the `MINI_SDK_E2E_*` variables below. Run with `--ignored`:
//! without the variables each test FAILS, it does not skip.
//!
//! What it shows: the frames the unix socket would carry arrive at the Host over ssh and the reply is
//! byte-identical to the unix socket's; one ssh session serves many requests; a planted wrong host
//! key and an unknown host key are refused by name with nothing sent and sshd never reaches
//! authentication; an unauthorised key is refused by name; the proxy refuses a config it does not pin
//! and an operator-only operation, and the SDK reports both as certainly-unsent.
#![cfg(feature = "native")]
use std::path::{Path, PathBuf};
use std::time::Duration;

use mini_sdk::operator::{Failure, Operator, Reply, Route, Ssh};

fn env(name: &str) -> String {
    std::env::var(name).unwrap_or_else(|_| panic!("{name} must be set (run native/mini-sdk/tests/ssh-e2e.sh)"))
}

fn ssh_route(config_var: &str) -> Route {
    let mut ssh = Ssh::new(&env("MINI_SDK_E2E_ALIAS")).unwrap();
    ssh.command = vec!["ssh".into()]; // the real client, whatever $MINI_SSH says
    ssh.config = Some(env(config_var).into());
    ssh.connect_timeout = Duration::from_secs(30);
    Route::Ssh(ssh)
}

fn operator(route: Route) -> Operator {
    Operator::new(route, Path::new(&env("MINI_SDK_E2E_CONFIG")), None).unwrap()
}

fn accepted_logins() -> usize {
    std::fs::read_to_string(env("MINI_SDK_E2E_SSHD_LOG")).unwrap().matches("Accepted publickey").count()
}

fn unsent(result: Result<Reply, Failure>) -> String {
    match result {
        Err(Failure::Unsent(why)) => why,
        other => panic!("expected certainly-unsent, got {other:?}"),
    }
}

/// DESCRIBE (operation 0) with no payload: the Host answers it on the public socket.
fn describe(op: &Operator) -> Reply {
    op.call(0, b"").unwrap_or_else(|e| panic!("DESCRIBE failed: {e:?}"))
}

#[test]
#[ignore = "driven by tests/ssh-e2e.sh"]
fn ssh_carries_describe_to_the_host_and_equals_the_unix_socket_over_one_session() {
    let before = accepted_logins();
    let over_ssh = operator(ssh_route("MINI_SDK_E2E_SSH_CONFIG_GOOD"));
    let first = describe(&over_ssh);
    let second = describe(&over_ssh);
    let Reply::Answer(body) = &first else { panic!("the Host refused DESCRIBE: {first:?}") };
    assert!(!body.is_empty(), "the Host's DESCRIBE answer is empty");
    assert_eq!(first, second, "the same request answers the same over the reused session");
    assert_eq!(accepted_logins(), before + 1, "two requests, ONE ssh session (one accepted login)");

    let over_unix = operator(Route::Unix(PathBuf::from(env("MINI_SDK_E2E_SOCKET"))));
    assert_eq!(describe(&over_unix), first, "the ssh route's reply is the unix socket's, byte for byte");
    eprintln!("ssh-e2e: DESCRIBE answered {} bytes over ssh, equal to the unix socket's", body.len());
}

#[test]
#[ignore = "driven by tests/ssh-e2e.sh"]
fn a_planted_wrong_host_key_is_refused_before_any_request_leaves() {
    let before = accepted_logins();
    let said = unsent(operator(ssh_route("MINI_SDK_E2E_SSH_CONFIG_WRONG")).call(0, b""));
    assert!(said.contains("host key verification failed"), "{said}");
    assert!(said.contains("known_hosts"), "the refusal says what to do: {said}");
    assert_eq!(accepted_logins(), before, "sshd must never reach authentication with a planted host key");
    eprintln!("ssh-e2e: planted host key refused: {said}");
}

#[test]
#[ignore = "driven by tests/ssh-e2e.sh"]
fn an_unknown_host_key_is_refused_and_not_learned() {
    let before = accepted_logins();
    let said = unsent(operator(ssh_route("MINI_SDK_E2E_SSH_CONFIG_EMPTY")).call(0, b""));
    assert!(said.contains("host key verification failed"), "{said}");
    assert_eq!(accepted_logins(), before);
    assert_eq!(std::fs::metadata(env("MINI_SDK_E2E_KNOWN_HOSTS_EMPTY")).unwrap().len(), 0,
        "an unknown host key is refused, never silently added");
}

#[test]
#[ignore = "driven by tests/ssh-e2e.sh"]
fn an_unauthorised_key_is_refused_by_name_with_nothing_sent() {
    let dir = std::env::temp_dir().join(format!("mini-sdk-e2e-key-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let key = dir.join("not-authorised");
    assert!(std::process::Command::new("ssh-keygen").args(["-q", "-t", "ed25519", "-N", "", "-f"]).arg(&key).status().unwrap().success());
    let Route::Ssh(mut ssh) = ssh_route("MINI_SDK_E2E_SSH_CONFIG_NOKEY") else { unreachable!() };
    ssh.identity = Some(key.clone());
    let before = accepted_logins();
    let said = unsent(operator(Route::Ssh(ssh)).call(0, b""));
    let _ = std::fs::remove_dir_all(&dir);
    assert!(said.contains("authentication refused"), "{said}");
    assert_eq!(accepted_logins(), before);
}

#[test]
#[ignore = "driven by tests/ssh-e2e.sh"]
fn the_proxy_refuses_a_config_it_does_not_pin_and_an_operator_only_operation() {
    // A config the Store did not pin: the proxy answers 254 and ends the session.
    let dir = std::env::temp_dir().join(format!("mini-sdk-e2e-cfg-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("other.config"), br#"{"domain":"1"}"#).unwrap();
    let wrong = Operator::new(ssh_route("MINI_SDK_E2E_SSH_CONFIG_GOOD"), &dir.join("other.config"), None).unwrap();
    let said = unsent(wrong.call(0, b""));
    let _ = std::fs::remove_dir_all(&dir);
    assert!(said.contains("socket rejected request") && said.contains("config pin mismatch"), "{said}");

    // An operator-only operation (22) is not on the public socket, so the member's key cannot reach it.
    let said = unsent(operator(ssh_route("MINI_SDK_E2E_SSH_CONFIG_GOOD")).call(22, &[1]));
    assert!(said.contains("socket rejected request") && said.contains("operation unavailable on selected socket"), "{said}");
}
