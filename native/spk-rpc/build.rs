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
}
