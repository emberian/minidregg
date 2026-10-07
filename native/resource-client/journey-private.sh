# journey-private.sh -- sourced by journey hooks.
# install_private MODE SRC DST: copy SRC to DST with MODE, creating DST's missing
# parent folders owner-private (0700). `install -D` creates its parents 0755
# whatever the umask, and the client refuses a session folder (keys/, provision/,
# requests/ ...) that anyone else can read: "session folder keys must be an
# owner-private directory" (shell/session_fs.rs private_folder).
install_private() {
  mkdir -p -m 700 "$(dirname "$3")" && install -m "$1" "$2" "$3"
}
