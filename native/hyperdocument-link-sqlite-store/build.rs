use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn compiler_library(name: &str) -> Option<PathBuf> {
    let compiler = env::var_os("CC").unwrap_or_else(|| "cc".into());
    let output = Command::new(compiler)
        .arg(format!("-print-file-name={name}"))
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let path = PathBuf::from(String::from_utf8(output.stdout).ok()?.trim());
    path.is_absolute()
        .then_some(path)
        .filter(|path| path.is_file())
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=CC");

    if env::var("CARGO_CFG_TARGET_OS").as_deref() != Ok("linux") {
        return;
    }

    // A normal development installation already exposes `libsqlite3.so`.
    // Minimal worker images sometimes retain only the ABI-versioned runtime
    // object. Give the linker a private unversioned alias while preserving the
    // object's `libsqlite3.so.0` SONAME for runtime loading.
    if compiler_library("libsqlite3.so").is_some() {
        return;
    }

    let runtime = compiler_library("libsqlite3.so.0").or_else(|| {
        [
            "/lib/x86_64-linux-gnu/libsqlite3.so.0",
            "/usr/lib/x86_64-linux-gnu/libsqlite3.so.0",
            "/lib/aarch64-linux-gnu/libsqlite3.so.0",
            "/usr/lib/aarch64-linux-gnu/libsqlite3.so.0",
        ]
        .into_iter()
        .map(PathBuf::from)
        .find(|path| path.is_file())
    });
    let runtime = runtime.unwrap_or_else(|| {
        panic!(
            "SQLite runtime library not found; install libsqlite3 or expose libsqlite3.so.0 through CC"
        )
    });

    let link_dir =
        PathBuf::from(env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR")).join("sqlite-link");
    fs::create_dir_all(&link_dir).expect("create private SQLite link directory");
    let alias = link_dir.join("libsqlite3.so");
    if !Path::new(&alias).is_file() {
        fs::copy(&runtime, &alias).expect("copy versioned SQLite runtime for linker alias");
    }
    println!("cargo:rustc-link-search=native={}", link_dir.display());
}
