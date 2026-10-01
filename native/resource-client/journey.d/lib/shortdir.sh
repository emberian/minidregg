# journey.d/lib/shortdir.sh: where the journey's Unix-domain sockets live.
# Sourced (POSIX sh) by journey.sh, by every hook that binds a socket, and by
# newparticipant-acceptance.sh. Not a hook: the journey runs journey.d/<id>.sh only.
#
# A socket path must fit sockaddr_un.sun_path: 108 bytes with the NUL, so 107
# usable. A Store's socket used to sit under the directory its Store was made
# in, i.e. under the run root (world/public/mini.sock, 23 bytes past it) or a
# step directory (steps/M8/m8/fixture/public/mini.sock, 37 past it). Under a
# long clone path `mini serve` or a grain controller could not bind, and every
# row after it read red for an unrelated-looking reason.
#
# So nothing binds under the run root. A caller that binds a socket takes a
# SHORT private directory, $JOURNEY_RUNTIME_BASE/jm.XXXXXX (XDG_RUNTIME_DIR,
# else /run/user/UID, else /tmp with a warning), linked from its own directory
# as rt/. Its sockets are declared in the table below, so their length is
# known, and checked, before anything is created. When the caller exits, the
# directory is copied back over the rt/ link (sockets dropped), the sockets it
# bound are measured into rt-sockets.tsv (and a socket longer than its declared
# one fails the caller: the table would be lying), and the directory is removed.

JOURNEY_SUN_PATH_MAX=107

# journey_check_sun_len PATH [WHAT]: exit 64, by name, when PATH cannot be bound.
journey_check_sun_len() {
  if [ "${#1}" -gt "$JOURNEY_SUN_PATH_MAX" ]; then
    echo "journey: socket path too long: ${2:-a socket} would be ${#1} bytes, sun_path holds $JOURNEY_SUN_PATH_MAX: $1" >&2
    exit 64
  fi
}

# Every socket a journey caller binds, as STEP NAME PATH-UNDER-THE-SHORT-DIR
# (the longest one per caller; NAME/ is the caller's own directory in it).
# A hook that starts binding a new or longer socket adds or edits its row.
journey_socket_table() {
  cat <<'TABLE'
J0	world	world.sock
M3	m3	m3/public/mini.sock
M4	m4	m4/store/public/mini.sock
M5	m5	m5/hermes/state/mcp-0000000000000011.sock
M7	m7	m7/public/mini.sock
M8	m8	m8/fixture/public/mini.sock
J13	j13	j13/store/public/mini.sock
JN2	jnock2	jnock2/world/public/mini.sock
JN3	jnock3	jnock3/world/public/mini.sock
JN5	jnock5	jnock5/world/public/mini.sock
JPAY4	jpay4	jpay4/acceptance/public/mini.sock
JPAY6	jpay6	jpay6/runtime-state/mcp-0000000000000011.sock
TABLE
}

# Sets JOURNEY_RUNTIME_BASE once (exported, so hooks inherit the choice).
journey_runtime_base_init() {
  [ -n "${JOURNEY_RUNTIME_BASE:-}" ] && return 0
  for _jrb in "${XDG_RUNTIME_DIR:-}" "/run/user/$(id -u)"; do
    if [ -n "$_jrb" ] && [ -d "$_jrb" ] && [ -w "$_jrb" ]; then
      JOURNEY_RUNTIME_BASE=$_jrb; export JOURNEY_RUNTIME_BASE; return 0
    fi
  done
  echo "journey: warning: no writable XDG_RUNTIME_DIR or /run/user/$(id -u); short socket directories go under /tmp" >&2
  JOURNEY_RUNTIME_BASE=/tmp; export JOURNEY_RUNTIME_BASE
}

# journey_socket_path NAME: the declared socket's path as it will be (the
# mktemp suffix has a fixed width); exit 64 when NAME declares none.
journey_socket_path() {
  journey_runtime_base_init
  _jsp=$(journey_socket_table | awk -F '\t' -v n="$1" '$2 == n { print $3 }')
  [ -n "$_jsp" ] || { echo "journey: $1 binds a socket but declares none in journey.d/lib/shortdir.sh" >&2; exit 64; }
  printf '%s\n' "$JOURNEY_RUNTIME_BASE/jm.XXXXXX/$_jsp"
}

# journey_check_all_sockets: every declared socket fits, or exit 64 by name.
journey_check_all_sockets() {
  journey_runtime_base_init
  for _jca in $(journey_socket_table | cut -f2); do
    _jcp=$(journey_socket_path "$_jca") || exit 64
    journey_check_sun_len "$_jcp" "$_jca"
  done
}

# journey_margin_table: STEP NAME BYTES MARGIN PATH for every declared socket.
journey_margin_table() {
  journey_runtime_base_init
  printf 'step\thook\tbytes\tmargin\tsocket (sun_path holds %s)\n' "$JOURNEY_SUN_PATH_MAX"
  journey_socket_table | while IFS='	' read -r _jmi _jmn _jms; do
    _jmp="$JOURNEY_RUNTIME_BASE/jm.XXXXXX/$_jms"
    printf '%s\t%s\t%s\t%s\t%s\n' "$_jmi" "$_jmn" "${#_jmp}" "$((JOURNEY_SUN_PATH_MAX - ${#_jmp}))" "$_jmp"
  done
}

# journey_shortdir NAME [LINKDIR]: allocate the short directory for NAME's
# sockets (refusing first if its declared socket cannot fit), link it as
# LINKDIR/rt (LINKDIR defaults to JOURNEY_STEP_DIR), and set
#   JOURNEY_RT  the short directory      JOURNEY_D  JOURNEY_RT/NAME, not created
# (the lane scripts a hook runs create their own run directory). On exit
# (JOURNEY_SHORTDIR_NOTRAP=1: when the caller calls journey_shortdir_return
# itself) the directory comes back to LINKDIR/rt. The journey rewrites a hook's
# artifact and detail from JOURNEY_RT to LINKDIR/rt (rt.origin records it).
journey_shortdir() {
  _jsd_name=$1
  journey_runtime_base_init
  JOURNEY_RT_LINKDIR=${2:-${JOURNEY_STEP_DIR:?journey_shortdir: no JOURNEY_STEP_DIR}}
  _jsd_sock=$(journey_socket_path "$_jsd_name") || exit 64
  journey_check_sun_len "$_jsd_sock" "$_jsd_name"
  JOURNEY_RT_DECLARED=${#_jsd_sock}
  mkdir -p "$JOURNEY_RT_LINKDIR"
  if [ -e "$JOURNEY_RT_LINKDIR/rt" ] || [ -L "$JOURNEY_RT_LINKDIR/rt" ]; then
    echo "journey: refusing to reuse $JOURNEY_RT_LINKDIR/rt" >&2; exit 2
  fi
  JOURNEY_RT=$(mktemp -d "$JOURNEY_RUNTIME_BASE/jm.XXXXXX") \
    || { echo "journey: cannot make a short directory under $JOURNEY_RUNTIME_BASE" >&2; exit 70; }
  ln -s "$JOURNEY_RT" "$JOURNEY_RT_LINKDIR/rt"
  printf '%s\n' "$JOURNEY_RT" >"$JOURNEY_RT_LINKDIR/rt.origin"
  JOURNEY_D=$JOURNEY_RT/$_jsd_name
  export JOURNEY_RT
  if [ "${JOURNEY_SHORTDIR_NOTRAP:-0}" != 1 ]; then
    trap 'journey_shortdir_return' EXIT
    trap 'exit 143' TERM
    trap 'exit 130' INT
  fi
}

# journey_shortdir_return: measure, copy back, remove. Idempotent. Run from an
# EXIT trap it leaves the caller's exit status alone, unless a measured socket
# outgrew its declared row: then the caller exits 66.
journey_shortdir_return() {
  [ -n "${JOURNEY_RT:-}" ] && [ -d "$JOURNEY_RT" ] || return 0
  _jsr_tsv=$JOURNEY_RT_LINKDIR/rt-sockets.tsv
  printf 'bytes\tmargin\tsocket\n' >"$_jsr_tsv"
  _jsr_long=$(find "$JOURNEY_RT" -type s | while IFS= read -r _jsr_s; do
    printf '%s\t%s\t%s\n' "${#_jsr_s}" "$((JOURNEY_SUN_PATH_MAX - ${#_jsr_s}))" "$_jsr_s" >>"$_jsr_tsv"
    [ "${#_jsr_s}" -le "$JOURNEY_RT_DECLARED" ] || printf '%s\n' "$_jsr_s"
  done)
  rm -f "$JOURNEY_RT_LINKDIR/rt"
  cp -a "$JOURNEY_RT" "$JOURNEY_RT_LINKDIR/rt" && find "$JOURNEY_RT_LINKDIR/rt" -type s -exec rm -f {} + \
    || echo "journey: copying $JOURNEY_RT back to $JOURNEY_RT_LINKDIR/rt failed; left in place" >&2
  [ -d "$JOURNEY_RT_LINKDIR/rt" ] && rm -rf "$JOURNEY_RT"
  JOURNEY_RT=
  if [ -n "$_jsr_long" ]; then
    echo "journey: a socket outgrew its declared row in journey.d/lib/shortdir.sh ($JOURNEY_RT_DECLARED bytes): $_jsr_long" >&2
    exit 66
  fi
  return 0
}
