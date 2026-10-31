//! The ssh forced command (`bin/mini-line`, installed as `/usr/local/lib/mini/mini-shell-ssh`)
//! against a stand-in `mini` that prints its arguments and its `MINI_*` environment and refuses
//! `line-resident`, so every line reaches the fresh-`mini` path with the exact vector a resident
//! would have been handed plus the call slot.
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

struct World {
    root: PathBuf,
}

impl Drop for World {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

impl World {
    fn new(name: &str) -> World {
        let root = std::env::temp_dir().join(format!("mssh-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("lib")).unwrap();
        fs::create_dir_all(root.join("bin")).unwrap();
        fs::create_dir_all(root.join("home")).unwrap();
        // The program, by the name the box installs it under, beside a motd and a notice.
        fs::copy(env!("CARGO_BIN_EXE_mini-line"), root.join("lib/mini-shell-ssh")).unwrap();
        fs::write(root.join("lib/motd.txt"), "welcome\n\n").unwrap();
        fs::write(root.join("lib/notice.txt"), "re-genesis").unwrap();
        World::script(&root.join("bin/mini"), "[ \"$1\" = line-resident ] && exit 1\nprintf '%s\\n' \"$@\"\necho --env--\nenv | grep '^MINI_' | sort\nexit 0\n");
        World { root }
    }

    fn script(path: &Path, body: &str) {
        fs::write(path, format!("#!/bin/sh\n{body}")).unwrap();
        fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
    }

    fn home(&self) -> PathBuf {
        self.root.join("home")
    }

    fn args(&self) -> Vec<String> {
        let p = |s: &str| self.root.join(s).display().to_string();
        vec![p("bin/mini"), "/host".into(), p("config.json"), "/socket".into(), "/workspace".into(), p("home")]
    }

    fn run(&self, line: Option<&str>, args: &[String], env: &[(&str, &str)]) -> Output {
        let mut command = Command::new(self.root.join("lib/mini-shell-ssh"));
        command.args(args).env("HOME", "/nonexistent-home").env_remove("SSH_ORIGINAL_COMMAND");
        for (key, _) in std::env::vars().filter(|(k, _)| k.starts_with("MINI_")) {
            command.env_remove(key);
        }
        if let Some(line) = line {
            command.env("SSH_ORIGINAL_COMMAND", line);
        }
        command.envs(env.iter().copied());
        command.output().unwrap()
    }

    /// The stand-in's arguments and its `MINI_*` environment.
    fn seen(output: &Output) -> (Vec<String>, Vec<String>) {
        let text = String::from_utf8(output.stdout.clone()).unwrap();
        let mut lines = text.lines().map(str::to_owned);
        let args = lines.by_ref().take_while(|l| l != "--env--").collect();
        (args, lines.collect())
    }

    fn shell(&self) -> Vec<String> {
        let home = self.home().display().to_string();
        let config = self.root.join("config.json").display().to_string();
        ["shell", "--socket", "/socket", "--host", "/host", "--config", &config, "--workspace", "/workspace",
            "--home", &home, "--call-slots", &format!("{home}/.call-slots")]
            .map(str::to_owned).to_vec()
    }
}

fn sha256(bytes: &[u8]) -> String {
    use sha2::Digest;
    sha2::Sha256::digest(bytes).iter().map(|b| format!("{b:02x}")).collect()
}

/// /etc/mini on the machine running the tests shapes what the environment rows can say.
fn box_settings() -> bool {
    ["session-consent", "session-residents", "session-codec"].iter().any(|f| Path::new("/etc/mini").join(f).exists())
}

#[test]
fn a_line_reaches_the_client_with_its_call_slots_and_its_exit_code() {
    let world = World::new("line");
    let out = world.run(Some("read shared 'a b'"), &world.args(), &[]);
    assert_eq!(out.status.code(), Some(0), "{}", String::from_utf8_lossy(&out.stderr));
    let (args, _) = World::seen(&out);
    let mut expected = world.shell();
    expected.extend(["--line".into(), "read shared 'a b'".into()]);
    assert_eq!(args, expected);
    assert!(out.stderr.is_empty(), "a line session prints no motd");
    World::script(&world.root.join("bin/mini"), "[ \"$1\" = line-resident ] && exit 1\nexit 3\n");
    assert_eq!(world.run(Some("x"), &world.args(), &[]).status.code(), Some(3));
}

#[test]
fn an_interactive_login_prints_the_motd_and_the_notice_then_runs_the_shell() {
    let world = World::new("interactive");
    for line in [None, Some("")] {
        let out = world.run(line, &world.args(), &[]);
        assert_eq!(out.status.code(), Some(0));
        assert_eq!(World::seen(&out).0, world.shell());
        assert_eq!(String::from_utf8_lossy(&out.stderr), "welcome\nre-genesis\n");
    }
}

#[test]
fn usage_paths_and_the_client_are_checked_before_anything_runs() {
    let world = World::new("usage");
    let args = world.args();
    assert_eq!(world.run(Some("x"), &args[..5], &[]).status.code(), Some(64));
    let mut relative = args.clone();
    relative[3] = "socket".into();
    assert_eq!(world.run(Some("x"), &relative, &[]).status.code(), Some(64));
    let mut missing = args.clone();
    missing[0] = world.root.join("bin/absent").display().to_string();
    let out = world.run(Some("x"), &missing, &[]);
    assert_eq!(out.status.code(), Some(66));
    assert!(out.stdout.is_empty());
}

#[test]
fn a_third_call_is_refused_by_name() {
    use std::os::fd::AsRawFd;
    let world = World::new("slots");
    let slots = world.home().join(".call-slots");
    fs::create_dir_all(&slots).unwrap();
    let held: Vec<fs::File> = ["1", "2"].iter().map(|n| {
        let file = fs::OpenOptions::new().append(true).create(true).open(slots.join(n)).unwrap();
        assert_eq!(unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) }, 0);
        file
    }).collect();
    let out = world.run(Some("whoami"), &world.args(), &[]);
    assert_eq!(out.status.code(), Some(75));
    assert!(out.stdout.is_empty());
    assert!(String::from_utf8_lossy(&out.stderr).contains("two calls already running"));
    drop(held);
    assert_eq!(world.run(Some("whoami"), &world.args(), &[]).status.code(), Some(0));
}

#[test]
fn consent_anchors_live_in_the_session_home_unless_the_caller_names_them() {
    if box_settings() {
        return;
    }
    let world = World::new("anchors");
    let out = world.run(Some("whoami"), &world.args(), &[]);
    let anchors = format!("MINI_CONSENT_ANCHOR_DIR={}", world.home().join(".mini/consent-anchors").display());
    assert_eq!(World::seen(&out).1, vec![anchors]);
    let out = world.run(Some("whoami"), &world.args(), &[("MINI_CONSENT_ANCHOR_DIR", "/given")]);
    assert_eq!(World::seen(&out).1, vec!["MINI_CONSENT_ANCHOR_DIR=/given".to_owned()]);
}

#[test]
fn delegated_consent_takes_the_pins_beside_the_socket_or_hashes_when_there_are_none() {
    if box_settings() {
        return;
    }
    let world = World::new("pins");
    let consent = world.home().join("consent");
    fs::create_dir_all(&consent).unwrap();
    let _listener = std::os::unix::net::UnixListener::bind(consent.join("peer.sock")).unwrap();
    fs::write(world.root.join("bin/minidregg-client-consent"), "provider").unwrap();
    fs::write(world.root.join("config.json"), "{}").unwrap();
    let env_of = |out: &Output| World::seen(out).1;
    // No pins file: both digests computed here (sha256 of "provider" and of "{}").
    let out = world.run(Some("whoami"), &world.args(), &[]);
    assert_eq!(out.status.code(), Some(0), "{}", String::from_utf8_lossy(&out.stderr));
    let env = env_of(&out);
    let has = |key: &str, value: &str| env.iter().any(|l| l == &format!("{key}={value}"));
    assert!(has("MINI_CONSENT_SOCKET", &consent.join("peer.sock").display().to_string()), "{env:?}");
    assert!(has("MINI_CONSENT_PEER_UID", "0"));
    assert!(has("MINI_LOCAL_HOST", "/host"));
    assert!(has("MINI_CONSENT_HOST", &world.root.join("bin/minidregg-client-consent").display().to_string()));
    assert!(has("MINI_CONSENT_SHA256", &sha256(b"provider")) && has("MINI_CONSENT_CONFIG_SHA256", &sha256(b"{}")), "{env:?}");
    // A pins file is taken as it is, and refused unless it holds two digests.
    let a = "a".repeat(64);
    let b = "b".repeat(64);
    fs::write(consent.join("peer.pins"), format!("{a} {b}\n")).unwrap();
    let env = env_of(&world.run(Some("whoami"), &world.args(), &[]));
    assert!(env.contains(&format!("MINI_CONSENT_SHA256={a}")) && env.contains(&format!("MINI_CONSENT_CONFIG_SHA256={b}")), "{env:?}");
    fs::write(consent.join("peer.pins"), format!("{a}\n")).unwrap();
    let out = world.run(Some("whoami"), &world.args(), &[]);
    assert_eq!(out.status.code(), Some(78));
    assert!(out.stdout.is_empty());
}
