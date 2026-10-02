//! Opt-in installed-runtime qualification. No model prompt, key or live Store.
use crate::mcp::{start_broker, ToolCatalog};
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::Command;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

const PROFILE: &str = "platform_toolsets:\n  acp: []\nmodel:\n  provider: custom\n  default: qwen/qwen3-coder\n  context_length: 262144\n  base_url: http://127.0.0.1:18881/v1\n  api_key: catalogue-probe-not-a-credential\n  api_mode: chat_completions\nmcp_servers: {}\ntimeouts:\n  mcp:\n    tool_call: 840\nmemory:\n  memory_enabled: false\n  user_profile_enabled: false\nauxiliary:\n  title_generation:\n    enabled: false\nagent:\n  max_iterations: 1\n  context_history: current_turn\ntools:\n  tool_search:\n    enabled: false\n";

#[test]
#[ignore = "requires installed Hermes runtime and Linux bwrap; set MINI_HERMES_CATALOGUE_RUNTIME"]
fn real_acp_room_catalogue_is_exact_before_any_prompt() {
    let runtime = fs::canonicalize(std::env::var_os("MINI_HERMES_CATALOGUE_RUNTIME")
        .expect("set MINI_HERMES_CATALOGUE_RUNTIME to the installed keyless runtime")).unwrap();
    let root = PathBuf::from("/tmp").join(format!("mini-hermes-catalogue-{}-{}", std::process::id(),
        SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()));
    fs::create_dir(&root).unwrap();
    fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
    let socket = root.join("broker.sock");
    let broker = start_broker(&socket, Duration::from_secs(90), ToolCatalog {
        room_tools: true, ..ToolCatalog::default()
    }).unwrap(); // Never activate_prompt: even an unexpected tool call cannot execute.
    let script = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../deploy/hermes/runtime-inputs/probe-catalogue.py");
    assert!(script.is_file(), "probe script missing");
    for (label, python, expected_exit) in [
        ("installed", "/agent/venv/bin/python", 0),
        ("historical-missing-sdk", "/agent/venv-before-mcp2/bin/python", 2),
        ("empty-catalogue", "/agent/venv/bin/python", 3),
    ] {
        let workspace = root.join(label);
        fs::create_dir_all(workspace.join(".hermes")).unwrap();
        fs::write(workspace.join(".hermes/config.yaml"), PROFILE).unwrap();
        fs::copy(&script, workspace.join("probe-catalogue.py")).unwrap();
        let mut command = Command::new("/usr/bin/timeout");
        command.args(["--signal=KILL", "100s", "/usr/bin/bwrap",
            "--die-with-parent", "--unshare-user", "--unshare-pid", "--unshare-ipc", "--unshare-uts",
            "--unshare-cgroup", "--unshare-net", "--clearenv", "--ro-bind", "/usr", "/usr",
            "--symlink", "usr/bin", "/bin", "--symlink", "usr/lib", "/lib",
            "--symlink", "usr/lib64", "/lib64", "--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp",
            "--ro-bind"]).arg(&runtime).arg("/agent").arg("--bind").arg(&workspace).arg("/workspace")
            .args(["--dir", "/run", "--ro-bind"]).arg(&socket).arg("/run/mini-grain.sock")
            .args(["--chdir", "/workspace", "--setenv", "HOME", "/workspace", "--setenv", "PATH", "/usr/bin:/bin",
                "--setenv", "PYTHONPATH", "/agent/source", "--setenv", "HERMES_HOME", "/workspace/.hermes",
                "--setenv", "XDG_CACHE_HOME", "/workspace/.cache", "--setenv", "XDG_CONFIG_HOME", "/workspace/.config",
                "--setenv", "XDG_DATA_HOME", "/workspace/.local/share", "--setenv", "PYTHONDONTWRITEBYTECODE", "1",
                "--setenv", "HERMES_ACP_SKIP_CONFIGURED_MCP", "1", "--setenv", "HERMES_DISABLE_LAZY_INSTALLS", "1"]);
        if let Some(source) = std::env::var_os("MINI_HERMES_CATALOGUE_SOURCE") {
            command.arg("--ro-bind").arg(fs::canonicalize(source).unwrap()).arg("/agent/source");
        }
        command.args(["--", python, "/workspace/probe-catalogue.py"]);
        if label == "empty-catalogue" { command.arg("--without-mcp"); }
        let result = command.output().unwrap();
        fs::write(root.join(format!("{label}.stdout")), &result.stdout).unwrap();
        fs::write(root.join(format!("{label}.stderr")), &result.stderr).unwrap();
        eprintln!("{label}: {}", String::from_utf8_lossy(&result.stdout));
        assert_eq!(result.status.code(), Some(expected_exit), "{label}; evidence={}\n{}",
            root.display(), String::from_utf8_lossy(&result.stderr));
        let reports: Vec<serde_json::Value> = String::from_utf8_lossy(&result.stdout).lines()
            .filter_map(|line| serde_json::from_str(line).ok()).collect();
        let report = reports.iter().find(|v| v["type"] == "mini-hermes-catalogue-preflight-v1").unwrap();
        if expected_exit != 2 {
            assert_eq!(report["wireMatchesTools"], true);
            assert_eq!(report["wireCatalogue"]["type"], "mini-hermes-tool-catalogue-v1");
            assert_eq!(report["wireCatalogue"]["valid"], true);
            assert_eq!(report["wireCatalogue"]["names"], report["tools"]);
        }
        if expected_exit == 0 {
            assert_eq!(report["ok"], true);
            assert_eq!(report["tools"].as_array().unwrap().len(), 8);
            assert_eq!(report["contextHistory"], "current_turn");
            assert_eq!(report["promptSubmitted"], false);
            assert_eq!(report["providerRequestsSent"], 0);
            assert!(report["providerConnectAttempts"].as_array().unwrap().iter()
                .all(|attempt| attempt["deniedBeforeSend"] == true && attempt["knownMetadataGet"] == true));
        } else if expected_exit == 2 {
            assert_eq!(report["reason"], "mcp-sdk-unavailable");
        } else {
            assert_eq!(report["ok"], false);
            assert_eq!(report["tools"], serde_json::json!([]));
            assert_eq!(report["providerRequestsSent"], 0);
        }
    }
    assert!(broker.requests.try_recv().is_err(), "catalogue discovery submitted a tool operation");
    eprintln!("catalogue qualification evidence: {}", root.display());
}
