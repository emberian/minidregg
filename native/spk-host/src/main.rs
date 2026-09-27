#[cfg(target_os = "linux")]
fn main() {
    use minidregg_spk_host::materialize::{
        materialize_spk, qualify_bridge_spk, signed_schema_source,
    };
    use serde_json::json;
    use std::path::Path;

    fn hex(bytes: [u8; 32]) -> String {
        let mut out = String::with_capacity(64);
        for byte in bytes {
            out.push_str(&format!("{byte:02x}"));
        }
        out
    }

    let args: Vec<_> = std::env::args().collect();
    if args.len() == 3 && args[1] == "qualify" {
        match qualify_bridge_spk(Path::new(&args[2])) {
            Ok((package, bridge)) => {
                let bridge_sha = package
                    .signed_bridge_config_sha256
                    .expect("qualified bridge has signed member");
                let member = package
                    .signed_bridge_config
                    .expect("qualified bridge has signed member");
                let json = json!({
                    "protocol":"mini-spk-bridge-qualification-v1",
                    "rawSha256":package.raw_sha256,
                    "rawLength":package.raw_length.to_string(),
                    "signedAppId":package.manifest.app_id.0,
                    "signedAppVersion":package.manifest.app_version.to_string(),
                    "manifestSha256":hex(package.signed_manifest_sha256),
                    "bridgeConfigSha256":hex(bridge_sha),
                    "signedBridgeConfigHex":member.iter().map(|byte| format!("{byte:02x}"))
                        .collect::<String>(),
                    "bridgeApiPath":bridge.api_path.clone().unwrap_or_default(),
                    "signedSchema":signed_schema_source(&bridge, package.manifest.app_version),
                });
                println!("{json}");
            }
            Err(error) => {
                eprintln!("spk-host: {error}");
                std::process::exit(1);
            }
        }
        return;
    }
    if args.len() == 5 && args[1] == "materialize" {
        let uid: u32 = match args[4].parse() {
            Ok(uid) => uid,
            Err(_) => {
                eprintln!("spk-host: APP_UID must be a decimal Unix UID");
                std::process::exit(2);
            }
        };
        match materialize_spk(Path::new(&args[2]), Path::new(&args[3]), uid) {
            Ok(installed) => {
                println!(
                    "installed={} spkSha256={} spkLength={} appId={} version={} signedManifestSha256={} signedBridgeConfigSha256={}",
                    installed.directory.display(),
                    installed.raw_sha256,
                    installed.raw_length,
                    installed.manifest.app_id.0,
                    installed.manifest.app_version,
                    hex(installed.signed_manifest_sha256),
                    installed.signed_bridge_config_sha256.map(hex).unwrap_or_else(|| "absent".into()),
                );
            }
            Err(error) => {
                eprintln!("spk-host: {error}");
                std::process::exit(1);
            }
        }
        return;
    }
    eprintln!(
        "usage: spk-host qualify VERIFIED_SPK | materialize VERIFIED_SPK OPERATOR_STORE APP_UID"
    );
    eprintln!("spk-host: application launch is unavailable until Mini admission is installed");
    std::process::exit(2);
}

#[cfg(not(target_os = "linux"))]
fn main() {
    eprintln!("spk-host is Linux-only");
    std::process::exit(2);
}
