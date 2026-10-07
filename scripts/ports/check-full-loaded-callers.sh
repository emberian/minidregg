#!/usr/bin/env bash
# KN2 ratchet (DEPUTY-KERNEL condition 3): every caller of the FULL verified materialization of the
# durable image (the whole decoded log in DurableReceiverIO.Loaded) is listed in
# scripts/ports/full-loaded-callers.txt. Fails on a caller not in the list (a new full-path use)
# and on a listed file that no longer calls it (the list must shrink when a port lands).
# The constructors of the full shape: DurableReceiverIO.load / loadChained / loadImage / loadSeed /
# loadBytes / extendFrom, NativeHost.openExisting, NativeHistorySelection.loadPrefix.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
pattern='(DurableReceiverIO\.)?(loadChained|loadImage|loadSeed|loadBytes|extendFrom|openExisting|loadPrefix)\b|DurableReceiverIO\.load\b|\bload transport\b|\bload config\.transport\b'
home='^(Compiler/DurableReceiverIO\.lean)$'
actual=$(git grep -lP "$pattern" -- '*.lean' | grep -vE "$home" | sort -u)
listed=$(grep -v '^#' scripts/ports/full-loaded-callers.txt | sed '/^$/d' | sort -u)
new=$(comm -23 <(echo "$actual") <(echo "$listed"))
stale=$(comm -13 <(echo "$actual") <(echo "$listed"))
fail=0
if [ -n "$new" ]; then echo "full-loaded ratchet: NEW callers of the full materialization (port them or justify):"; echo "$new"; fail=1; fi
if [ -n "$stale" ]; then echo "full-loaded ratchet: listed files that no longer call it (remove them from the list):"; echo "$stale"; fail=1; fi
[ $fail = 0 ] && echo "full-loaded ratchet: PASS ($(echo "$actual" | wc -l | tr -d ' ') callers, list matches)"
exit $fail
