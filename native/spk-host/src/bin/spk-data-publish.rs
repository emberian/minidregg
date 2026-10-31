//! Operator-only local publication/audit utility. Never accepts network URLs.
// print!/println!/eprint!/eprintln!: a closed standard output ends the command with 141, never a
// panic (`mini_streams`).
#[macro_use]
extern crate mini_streams;
#[cfg(target_os = "linux")]
fn run() -> std::io::Result<()> {
    use minidregg_spk_host::shared_data;
    use std::io::Read;
    use std::os::unix::fs::OpenOptionsExt;
    use std::path::Path;
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.as_slice() {
        [verb, store_flag, store, source_flag, source, inventory_flag, inventory]
            if verb == "publish" && store_flag == "--store" && source_flag == "--source" && inventory_flag == "--inventory" => {
                let mut file = std::fs::OpenOptions::new().read(true)
                    .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK).open(inventory)?;
                let meta = file.metadata()?;
                if !meta.is_file() || meta.len() > shared_data::MAX_INVENTORY_BYTES as u64 {
                    return Err(std::io::Error::other("inventory must be a bounded regular file"));
                }
                let mut bytes=Vec::new();
                file.by_ref().take(shared_data::MAX_INVENTORY_BYTES as u64+1).read_to_end(&mut bytes)?;
                let published = shared_data::publish(Path::new(store),Path::new(source),&bytes)?;
                println!("{}",serde_json::to_string(&published)?);
                Ok(())
            }
        [verb, store_flag, store, digest_flag, digest]
            if verb == "audit" && store_flag == "--store" && digest_flag == "--inventory-sha256" => {
                let attachment=serde_json::to_vec(&serde_json::json!({"schema":"minidregg-public-data-v1","inventory_sha256":digest}))?;
                let requirement=shared_data::parse_signed_attachment(&attachment)?;
                // Audit has no application actor. Select a distinct sentinel only
                // for the shared reader's "never app-owned" custody check.
                let sentinel=unsafe {libc::geteuid()}.checked_add(1).ok_or_else(|| std::io::Error::other("invalid operator UID"))?;
                shared_data::audit(Path::new(store),&requirement,sentinel)?;
                println!("{}",serde_json::json!({"schema":"mini-spk-public-data-audit-v1","inventory_sha256":digest,"verified":true}));
                Ok(())
            }
        _ => Err(std::io::Error::other("usage: spk-data-publish publish --store PUBLIC_DATA_STORE --source SOURCE_DIR --inventory INVENTORY_JSON | audit --store PUBLIC_DATA_STORE --inventory-sha256 HEX")),
    }
}

#[cfg(target_os = "linux")]
fn run_main() {
    if let Err(error) = run() {
        eprintln!("spk-data-publish: {error}");
        std::process::exit(1);
    }
}
#[cfg(not(target_os = "linux"))]
fn run_main() {
    eprintln!("spk-data-publish requires Linux");
    std::process::exit(1);
}

fn main() -> std::process::ExitCode {
    mini_streams::guard(|| {
        run_main();
        std::process::ExitCode::SUCCESS
    })
}
