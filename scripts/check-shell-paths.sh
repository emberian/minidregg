#!/usr/bin/env bash
# check-shell-paths.sh — a path a friend types is confined by descriptor, never
# by its spelling.
#
# Every path a shell line names (say --operation-record, tail --discover, @FILE)
# is confined by native/resource-client/src/shell/session_fs.rs: reached from the
# session root through descriptors that never follow a symlink, into an
# owner-private folder. `is_absolute()` in a line parser is the defect R2-1 #4a
# named: it accepted any absolute path — another friend's requests/, a Store
# directory — as if it were this session's. This gate is red when a shell-line
# parser calls it. The one allowed call is the operator's own invocation,
# `mini shell --workspace/--home` (shell.rs `run`), pinned by its exact text.
#
# The instrument tests itself every run: the same check over a scratch copy with
# one injected call must go red, so a check that stopped matching cannot read
# green.
set -uo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$root/native/resource-client/src" || exit 2
parsers=(chat.rs story.rs hermes.rs shell.rs shell/*.rs)
allowed='shell.rs:        if !path.is_absolute() {'

check() { # DIR -> prints offending lines; exit 1 when any
  local dir=$1 hits
  hits=$(cd "$dir" && grep -n 'is_absolute()' "${parsers[@]}" 2>/dev/null \
    | sed 's/^\([^:]*\):[0-9]*:/\1:/' | grep -vxF "$allowed")
  if [ -n "$hits" ]; then printf '%s\n' "$hits"; return 1; fi
  # The allowed call stays exactly one: the shell's own --workspace/--home.
  [ "$(cd "$dir" && grep -c 'is_absolute()' shell.rs)" = 1 ] || { echo "shell.rs: allowed call count changed"; return 1; }
  return 0
}

scratch=$(mktemp -d); trap 'rm -rf "$scratch"' EXIT
mkdir -p "$scratch/shell"
for f in "${parsers[@]}"; do cp "$f" "$scratch/$f"; done
printf '\nfn injected(p: &std::path::Path) -> bool { p.is_absolute() }\n' >>"$scratch/chat.rs"
if check "$scratch" >/dev/null; then
  echo "shell-paths: RED: the instrument did not see an injected is_absolute() in chat.rs"
  exit 1
fi
if out=$(check .); then
  echo "shell-paths: ok: no shell-line parser confines a path by is_absolute() (${#parsers[@]} files; self-test red as expected)"
else
  echo "shell-paths: RED: a shell-line parser confines a path by its spelling; route it through shell::session_fs:"
  printf '%s\n' "$out"
  exit 1
fi
