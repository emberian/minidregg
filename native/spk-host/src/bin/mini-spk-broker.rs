//! `mini-spk-broker serve CONFIG` — the operator unix-socket broker for grain hosts.
//! `mini-spk-broker backup CONFIG OUT_DIR` — consistent copies of every grain volume.

// print!/println!/eprint!/eprintln!: a closed standard output ends the command with 141, never a
// panic (`mini_streams`).
#[macro_use]
extern crate mini_streams;
#[cfg(target_os = "linux")]
fn run_main() {
    let args: Vec<String> = std::env::args().collect();
    let result = match args.as_slice() {
        [_, verb, config] if verb == "serve" => {
            minidregg_spk_host::broker::serve(std::path::Path::new(config)).map(|()| None)
        }
        [_, verb, config, out] if verb == "backup" => minidregg_spk_host::broker::backup(
            std::path::Path::new(config),
            std::path::Path::new(out),
        )
        .map(Some),
        _ => {
            eprintln!("usage: mini-spk-broker serve CONFIG | backup CONFIG OUT_DIR");
            std::process::exit(2);
        }
    };
    match result {
        Ok(Some(value)) => println!("{value}"),
        Ok(None) => {}
        Err(error) => {
            eprintln!("mini-spk-broker: {error}");
            std::process::exit(1);
        }
    }
}

#[cfg(not(target_os = "linux"))]
fn run_main() {
    eprintln!("mini-spk-broker: Linux only");
    std::process::exit(2);
}

fn main() -> std::process::ExitCode {
    mini_streams::guard(|| {
        run_main();
        std::process::ExitCode::SUCCESS
    })
}
