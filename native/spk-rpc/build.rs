use sha2::{Digest, Sha256};
use std::path::PathBuf;

fn main() {
    let schemas = [
        "util.capnp",
        "identity.capnp",
        "powerbox.capnp",
        "activity.capnp",
        "grain.capnp",
        "supervisor.capnp",
        "ip.capnp",
        "web-session.capnp",
        "api-session.capnp",
    ];
    let mut command = capnpc::CompilerCommand::new();
    command.src_prefix("schema").import_path("schema");
    command.file("schema/capnp/persistent.capnp");
    println!("cargo:rerun-if-changed=schema/capnp/persistent.capnp");
    for schema in schemas {
        println!("cargo:rerun-if-changed=schema/{schema}");
        command.file(format!("schema/{schema}"));
    }
    command.run().expect("compile pinned Sandstorm schemas");

    // `package.capnp` itself is pinned and unmodified. capnpc 0.27 emits two
    // Rust modules called `category_info` for its CategoryInfo struct and
    // categoryInfo annotation. Rename only the annotation symbol in a private
    // build input; its explicit wire ID and all field ordinals/types remain
    // unchanged. This keeps the complete upstream BridgeConfig definition.
    let source = std::fs::read("schema/package.capnp").expect("read pinned package schema");
    assert_eq!(
        format!("{:x}", Sha256::digest(&source)),
        "e5535bc6cae621c7205befa5d8aea655206ecfc859d27b4bd43b2e4c065fadfb",
        "package.capnp differs from pinned Sandstorm a97cf3e"
    );
    let source = String::from_utf8(source).expect("package schema UTF-8");
    assert_eq!(source.matches("categoryInfo").count(), 12);
    let derived = source.replace("categoryInfo", "categoryAnnotation");
    let out = PathBuf::from(std::env::var_os("OUT_DIR").expect("OUT_DIR"));
    for entry in std::fs::read_dir("schema").expect("read pinned schema directory") {
        let entry = entry.expect("schema entry");
        if entry
            .path()
            .extension()
            .is_some_and(|extension| extension == "capnp")
        {
            std::fs::copy(entry.path(), out.join(entry.file_name()))
                .expect("copy private imported schema");
        }
    }
    std::fs::create_dir_all(out.join("capnp")).expect("private Cap'n Proto schema directory");
    std::fs::copy(
        "schema/capnp/persistent.capnp",
        out.join("capnp/persistent.capnp"),
    )
    .expect("copy private persistent schema");
    let derived_path = out.join("package-rust.capnp");
    std::fs::write(&derived_path, derived).expect("write private package schema");
    println!("cargo:rerun-if-changed=schema/package.capnp");
    capnpc::CompilerCommand::new()
        .src_prefix(&out)
        .import_path(
            std::env::current_dir()
                .expect("crate directory")
                .join("schema"),
        )
        .file(&derived_path)
        .run()
        .expect("compile complete pinned package schema with annotation name repair");
}
