//! Operator-private status endpoint. BEGIN and dispatch stay unavailable until
//! Mini's native checked receivers can issue sealed authority values.

#[cfg(target_os = "linux")]
fn main() {
    use minidregg_spk_host::endpoint::PrivateEndpoint;
    use minidregg_spk_host::hostd::Journal;
    use std::path::Path;

    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 || args[1] != "serve-status" {
        eprintln!("usage: spk-hostd serve-status ABS_OPERATOR_PRIVATE_DIR");
        std::process::exit(2);
    }
    let directory = Path::new(&args[2]);
    let outcome = (|| {
        let journal = Journal::open(directory)?;
        let endpoint = PrivateEndpoint::bind(directory, &journal)?;
        endpoint.serve(&journal)
    })();
    if let Err(error) = outcome {
        eprintln!("spk-hostd: {error}");
        std::process::exit(1);
    }
}

#[cfg(not(target_os = "linux"))]
fn main() {
    eprintln!("spk-hostd requires Linux");
    std::process::exit(2);
}
