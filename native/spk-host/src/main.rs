#[cfg(target_os = "linux")]
fn main() {
    use minidregg_spk_host::launch_descriptor_native::qualify_launch;
    use minidregg_spk_host::materialize::{
        materialize_spk_with_profile, qualify_bridge_spk_with_profile, signed_schema_source,
        verify_installed_spk, ImportProfile,
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

    // Every artifact spk-host or its pinned Mini Host helper writes is owner
    // private; later custody reads refuse anything else, whatever the caller's
    // or service manager's umask.
    unsafe {
        libc::umask(0o077);
    }
    let mut args: Vec<_> = std::env::args().collect();
    // This process is operator tooling. An application or package never chooses
    // the importer profile through the broker's request protocol.
    let mut import_profile = ImportProfile::Standard;
    if matches!(args.get(1).map(String::as_str), Some("qualify" | "materialize"))
        && args.get(2).map(String::as_str) == Some("--import-profile")
    {
        import_profile = match args.get(3).and_then(|name| name.parse().ok()) {
            Some(profile) => profile,
            None => {
                eprintln!("spk-host: import profile must be standard-v1, market-large-v1 or operator-appliance-v1");
                std::process::exit(2);
            }
        };
        args.drain(2..4);
    }
    // The modeled unit manager of a fixture build (src/fixture_os.rs).
    #[cfg(feature = "fixture-os")]
    match args.get(1).map(String::as_str) {
        Some("fixture-systemctl") => {
            std::process::exit(minidregg_spk_host::fixture_os::systemctl_main(&args[2..]))
        }
        Some("fixture-unit-run") => {
            std::process::exit(minidregg_spk_host::fixture_os::unit_run_main(&args[2..]))
        }
        _ => {}
    }
    // The intake bounds of an import profile for a raw package size, for the operator scripts
    // (spk-ingest, spk-qualify, spk-install-phase), so the table lives once, here:
    // `import-limits PROFILE RAW_BYTES` prints `RAW_LIMIT DECODED_LIMIT WALL_SECONDS`.
    if args.len() == 4 && args[1] == "import-limits" {
        let (Ok(profile), Ok(raw)) = (args[2].parse::<ImportProfile>(), args[3].parse::<u64>()) else {
            eprintln!("spk-host: import-limits PROFILE RAW_BYTES (standard-v1, market-large-v1 or operator-appliance-v1)");
            std::process::exit(2);
        };
        let limits = profile.limits();
        println!("{} {} {}", limits.raw_bytes, limits.decoded_bytes, limits.wall_seconds(raw));
        return;
    }
    if args.len() == 3 && args[1] == "qualify-launch" {
        match qualify_launch(Path::new(&args[2])) {
            Ok(result) => {
                println!("{result}");
                return;
            }
            Err(error) => {
                eprintln!("spk-host: launch qualification refused: {error}");
                std::process::exit(1);
            }
        }
    }
    if args.len() == 3 && matches!(args[1].as_str(), "install-prepare" | "install-complete") {
        let result = if args[1] == "install-prepare" {
            minidregg_spk_host::install_service::prepare(Path::new(&args[2]))
        } else {
            minidregg_spk_host::install_service::complete(Path::new(&args[2]))
        };
        match result {
            Ok(()) => return,
            Err(error) => {
                eprintln!("spk-host: INSTALL refused: {error}");
                std::process::exit(1);
            }
        }
    }
    let checkpoint_result = match args.as_slice() {
        [_, verb, config, input] if verb == "checkpoint-pause-check" => Some(
            minidregg_spk_host::broker::checkpoint_pause_check(Path::new(config), Path::new(input)),
        ),
        [_, verb, config, out, input] if verb == "checkpoint-backup" => {
            Some(minidregg_spk_host::broker::checkpoint_backup(
                Path::new(config),
                Path::new(out),
                Path::new(input),
            ))
        }
        _ => None,
    };
    if let Some(result) = checkpoint_result {
        match result {
            Ok(value) => println!("{value}"),
            Err(error) => {
                eprintln!("spk-host checkpoint: {error}");
                std::process::exit(1);
            }
        }
        return;
    }
    if args.len() == 7 && args[1] == "volume-custodian" {
        // volume-custodian ROOT SOCKET UID_BASE UID_LIMIT SOCKET_GID (deploy/spk-host/VOLUMES.md)
        let n = |i: usize| args[i].parse::<u32>().unwrap_or_else(|_| { eprintln!("spk-host volume-custodian: {} is not a number", args[i]); std::process::exit(2) });
        let served = minidregg_spk_host::broker::volume_custodian::Custodian::open(std::path::Path::new(&args[2]), n(4), n(5))
            .and_then(|c| c.serve(std::path::Path::new(&args[3]), n(6)));
        if let Err(error) = served { eprintln!("spk-host volume-custodian: {error}"); std::process::exit(1); }
        return;
    }
    if args.len() >= 4 && args[1] == "grain" {
        match minidregg_spk_host::grain::run(&args[2..]) {
            Ok(result) => {
                println!("{result}");
                return;
            }
            Err(error) => {
                eprintln!("spk-host: grain refused: {error}");
                // An uncertain record is never retried: the supervisor template
                // sets RestartPreventExitStatus=3.
                std::process::exit(if error.to_string().starts_with("UNRESOLVED:") {
                    3
                } else {
                    1
                });
            }
        }
    }
    if args.len() == 3 && args[1] == "resident-bootstrap" {
        match minidregg_spk_host::resident_privilege::run(Path::new(&args[2])) {
            Ok(()) => return,
            Err(error) => { eprintln!("spk-host: resident bootstrap refused: {error}"); std::process::exit(1); }
        }
    }
    if args.len()==3 && args[1]=="resident-validate" {
        match minidregg_spk_host::resident_service::validate_config(Path::new(&args[2])) {
            Ok(())=>return,
            Err(error)=>{eprintln!("resident config refused: {error}");std::process::exit(1);}
        }
    }
    if args.len() == 3 && args[1] == "resident-run" {
        match minidregg_spk_host::resident_service::run(Path::new(&args[2])) {
            Ok(()) => return,
            Err(error) => {
                eprintln!("spk-host: resident refused: {error}");
                std::process::exit(1);
            }
        }
    }
    if args.len() == 3 && args[1] == "resident-stop" {
        match minidregg_spk_host::lifecycle_v3_stop_service::run(Path::new(&args[2])) {
            Ok(()) => return,
            Err(error) => {
                eprintln!("spk-host: resident STOP refused: {error}");
                std::process::exit(1);
            }
        }
    }
    if args.len() == 9 && args[1] == "human-custodian-init" {
        match minidregg_spk_host::http_entrance::initialize_custodian(
            Path::new(&args[2]),
            &args[3],
            &args[4],
            &args[5],
            &args[6],
            &args[7],
            &args[8],
        ) {
            Ok(()) => {
                println!("human custodian initialized at {}", args[2]);
                return;
            }
            Err(error) => {
                eprintln!("spk-host: human custodian initialization refused: {error}");
                std::process::exit(1);
            }
        }
    }
    if args.len() == 3 && args[1] == "qualify" {
        match qualify_bridge_spk_with_profile(Path::new(&args[2]), import_profile) {
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
                    "bridgeFacilities":{
                        "saveIdentityCaps":bridge.save_identity_caps,
                        "expectAppHooks":bridge.expect_app_hooks,
                        "served":"identity capabilities are saved, restored and dropped through the app's identity custody (revocable, listed in receipts); app hooks answer the bridge's getViewInfo; app-object restore answers unknownToken"
                    },
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
    if args.len() == 4 && args[1] == "inspect-installed" {
        let uid: u32 = match args[3].parse() {
            Ok(uid) if uid != 0 => uid,
            _ => {
                eprintln!("spk-host: APP_UID must be a nonzero decimal Unix UID");
                std::process::exit(2);
            }
        };
        let image = Path::new(&args[2]);
        if !image.is_absolute() {
            eprintln!("spk-host: installed image path must be absolute");
            std::process::exit(2);
        }
        match verify_installed_spk(image, uid) {
            Ok(installed) => {
                let bridge = match installed.signed_bridge_config_sha256 {
                    Some(digest) => digest,
                    None => {
                        eprintln!("spk-host: installed signed bridge absent");
                        std::process::exit(1);
                    }
                };
                println!(
                    "{}",
                    json!({
                        "protocol":"mini-spk-installed-inspection-v1",
                        "imageDir":installed.directory,
                        "appUid":uid,
                        "rawSha256":installed.raw_sha256,
                        "rawLength":installed.raw_length.to_string(),
                        "signedAppId":installed.manifest.app_id.0,
                        "signedAppVersion":installed.manifest.app_version.to_string(),
                        "signedManifestSha256":hex(installed.signed_manifest_sha256),
                        "signedBridgeConfigSha256":hex(bridge),
                    })
                );
            }
            Err(error) => {
                eprintln!("spk-host: installed image inspection refused: {error}");
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
        match materialize_spk_with_profile(Path::new(&args[2]), Path::new(&args[3]), uid, import_profile) {
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
        "usage: spk-host qualify VERIFIED_SPK | qualify-launch PRIVATE_CONFIG | inspect-installed IMAGE_DIR APP_UID | materialize VERIFIED_SPK OPERATOR_STORE APP_UID | install-prepare PRIVATE_CONFIG | install-complete PRIVATE_CONFIG | resident-run PRIVATE_CONFIG | resident-stop PRIVATE_CONFIG | human-custodian-init PRIVATE_DIR HOST APP SUBJECT SESSION TICKET web|api | grain VERB ..."
    );
    eprintln!("spk-host: resident-run requires current Mini lifecycle admission and physical unit custody");
    eprintln!("qualify and materialize accept --import-profile standard-v1|market-large-v1|operator-appliance-v1 immediately after the verb");
    std::process::exit(2);
}

#[cfg(not(target_os = "linux"))]
fn main() {
    eprintln!("spk-host is Linux-only");
    std::process::exit(2);
}
