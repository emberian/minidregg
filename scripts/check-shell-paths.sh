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
# every file below shell/ (nested directories too), not just shell/*.rs
mapfile -t shell_dir < <(find shell -type f -name '*.rs' | sort)
parsers=(chat.rs story.rs hermes.rs shell.rs "${shell_dir[@]}")
# The spelling tests that confine a path by what it looks like: `p.is_absolute()`, the
# `Path::is_absolute(p)` and `.map(Path::is_absolute)` forms, `p.has_root()`, a `starts_with('/')`
spelling='\b(is_absolute|has_root)\b|starts_with\(.\/.\)'

allowed='shell.rs:        if !path.is_absolute() {'

check() { # DIR -> prints offending lines; exit 1 when any
  local dir=$1 hits
  hits=$(cd "$dir" && grep -nE "$spelling" "${parsers[@]}" 2>/dev/null \
    | sed 's/^\([^:]*\):[0-9]*:/\1:/' | grep -vxF "$allowed")
  if [ -n "$hits" ]; then printf '%s\n' "$hits"; return 1; fi
  # The allowed call stays exactly one: the shell's own --workspace/--home.
  [ "$(cd "$dir" && grep -cE "$spelling" shell.rs)" = 1 ] || { echo "shell.rs: allowed call count changed"; return 1; }
  return 0
}

scratch=$(mktemp -d); trap 'rm -rf "$scratch"' EXIT
for f in "${parsers[@]}"; do mkdir -p "$scratch/$(dirname "$f")"; cp "$f" "$scratch/$f"; done
# one injected spelling per form the check claims to see, each in a different file
inject() { # FILE BODY: the check over a scratch copy with BODY appended to FILE must go red
  cp -a "$scratch/$1" "$scratch/$1.orig"
  printf '\nfn injected(p: &std::path::Path) -> bool { %s }\n' "$2" >>"$scratch/$1"
  if check "$scratch" >/dev/null; then
    echo "shell-paths: RED: the instrument did not see an injected '$2' in $1"; exit 1
  fi
  mv "$scratch/$1.orig" "$scratch/$1"
}
inject chat.rs 'p.is_absolute()'
inject story.rs 'std::path::Path::is_absolute(p)'
inject hermes.rs 'p.has_root()'
inject shell.rs "p.to_str().map_or(false, |s| s.starts_with('/'))"
inject "${shell_dir[0]}" 'p.is_absolute ()'

if out=$(check .); then
  echo "shell-paths: ok: no shell-line parser confines a path by is_absolute() (${#parsers[@]} files; self-test red as expected)"
else
  echo "shell-paths: RED: a shell-line parser confines a path by its spelling; route it through shell::session_fs:"
  printf '%s\n' "$out"
  exit 1
fi
