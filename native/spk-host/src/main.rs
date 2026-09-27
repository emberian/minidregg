#[cfg(target_os = "linux")]
fn main() {
    use minidregg_spk_host::materialize::materialize_spk;
    use std::path::Path;

    fn hex(bytes: [u8; 32]) -> String {
        let mut out = String::with_capacity(64);
        for byte in bytes {
            out.push_str(&format!("{byte:02x}"));
        }
        out
    }

    let args: Vec<_> = std::env::args().collect();
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
    eprintln!("usage: spk-host materialize VERIFIED_SPK OPERATOR_STORE APP_UID");
    eprintln!("spk-host: application launch is unavailable until Mini admission is installed");
    std::process::exit(2);
}

#[cfg(not(target_os = "linux"))]
fn main() {
    eprintln!("spk-host is Linux-only");
    std::process::exit(2);
}
