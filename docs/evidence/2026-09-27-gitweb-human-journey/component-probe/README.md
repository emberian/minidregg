# GitWeb human helper: native-entrance component probe

The test is an explicitly ignored, manually invoked Rust test in the real
`http_entrance` module. It creates a fresh owner-private native custodian and
`PrivateHttpEntrance`, authenticates the helper's API bearer through that
Unix socket, and forwards fixed Git smart-HTTP requests to `/usr/bin/git
http-backend` serving a new private bare repository. Its callback discards
the response **after** Git accepts the one `git-receive-pack` POST. The helper
then performs `lookup-api` through the same entrance. The test asserts one
receive-pack total, retained one-send marker, the real bare-repo master ref,
and matching read-only lookup result. It is a transport component test; its
test callback does not issue a Mini dispatch permit or claim resident START.

The test additions were `native/spk-host/src/http_entrance.rs` SHA-256
`5b76139edd2fc114734654009ff2505ca59a78d8ab69d98a990ea05fc9f43366`
and new `native/spk-host/src/http_entrance_gitweb_probe.rs` SHA-256
`27401a4b61396a388fe2fa24acd890b15e233645448faaf538e66f382e21c3ce`.
The isolated test target was compiled from committed `9d84b6e` plus only
those two test files with `cargo test --locked --offline --lib --no-run`.
`compile.log` records the pass.

The initial ignored run (`probe-r1.log`) refused test scratch under
`/home/ember/build`, whose ancestor was mode 0775. The next run used the
protected `/run/user/1000` and exposed a real helper bug (`probe-r2.log`):
Git inherited umask 0002 and cloned `repo/`/`public/` as mode 0775, so the
read-only lookup correctly refused their private-path ancestry after the
accepted Git write. Both red runs remain classified as such.

The standalone helper now sets umask 0077 before spawning Git. Corrected
helper source SHA-256 is
`11ee47d2e07333a6c65c7adcfe69b7394fcddcf99daade5d655371bbcdbd8a92`.
Its isolated committed-`9d84b6e` overlay passed focused Cargo check,
strict target Clippy, and release build (`helper-*.log`). The exact release
binary run in the final probe had SHA-256
`cea0692f412d3d24f84bb2a5d4eed32e90b89425e9f64b19cd1f2416b964be2a`.
The bounded final command was the single ignored test under
`timeout -k 5s 130s`, `XDG_RUNTIME_DIR=/run/user/1000`, and the pinned helper
path; `probe-r3.log` records 1 passed, 0 failed in 0.16 seconds. The test
used no production r3 Store, controller, resident app, ticket, or user token.

Before a live write, the actual installed resident Mini dispatch path and
human tickets still require their own admission/receipt evidence. A matching
Git ref is app readback, not a Mini historical receipt.
