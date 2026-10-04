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
# The files that confine a friend-typed path are DERIVED, not listed: every file below shell/ (nested
# directories too) and every file that names the confinement API (`session_fs`), plus the four parsers
# that always counted. A file that starts confining paths by descriptor enters by saying so; the check
# that the four seeds are still derived keeps the derivation from quietly shrinking.
mapfile -t shell_dir < <(find shell -type f -name '*.rs' | sort)
mapfile -t parsers < <({ printf '%s\n' chat.rs story.rs hermes.rs shell.rs "${shell_dir[@]}"; grep -rl 'session_fs' --include='*.rs' . | sed 's|^\./||'; } | sort -u)
for seed in chat.rs story.rs hermes.rs shell.rs; do
  printf '%s\n' "${parsers[@]}" | grep -qx "$seed" || { echo "shell-paths: RED: seed parser $seed is no longer derived (renamed or deleted?)"; exit 1; }
done
# a legitimate spelling hit in a derived file is pinned with its reason, by file and exact text
allow=$root/scripts/gates/shell-paths-allow.tsv
# The spelling tests that confine a path by what it looks like: `p.is_absolute()`, the
# `Path::is_absolute(p)` and `.map(Path::is_absolute)` forms, `p.has_root()`, a `starts_with('/')`
spelling='\b(is_absolute|has_root)\b|starts_with\(.\/.\)'

check() { # DIR -> prints offending lines; exit 1 when any
  local dir=$1 hits
  hits=$(cd "$dir" && grep -nE "$spelling" "${parsers[@]}" 2>/dev/null \
    | sed 's/^\([^:]*\):[0-9]*:/\1\t/' | awk -F'\t' -v allow="$allow" 'BEGIN { while ((getline l < allow) > 0) if (l !~ /^#/ && l != "") { split(l, a, "\t"); ok[a[1] "\t" a[2]] = 1 } } !(($1 "\t" $2) in ok)' | tr '\t' ':')
  if [ -n "$hits" ]; then printf '%s\n' "$hits"; return 1; fi
  # The allowed call stays exactly one: the shell's own --workspace/--home.
  # and every pinned row still matches a line (a stale row is red)
  while IFS=$'\t' read -r f text _; do
    [ -n "$f" ] && [[ $f != \#* ]] || continue
    (cd "$dir" && grep -qxF -- "$text" "$f" 2>/dev/null) || { echo "$f: pinned allow row no longer matches a line: $text"; return 1; }
  done <"$allow"
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
