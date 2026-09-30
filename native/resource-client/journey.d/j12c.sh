#!/usr/bin/env bash
# J12c (PLACE §2.4): B quotes a range of commons/wall into lab/paper; C (in
# commons only) reading the quote inside lab/paper is refused no-grant; A (in
# lab only) reads the quoted bytes; A's `doc follow` is refused no-grant.
#
# This hook is a FAILING STUB by construction, not a skipped step: it types the
# first verb of J12c into a real shell session and reports the shell's own
# answer. It turns green when that verb exists, which needs
#   K-CONTENT-ACTIONS  a `transclude` action in Kernel/ContentResource.lean
#                      `Action` and a TransclusionRecord entry (with its
#                      disclosurePolicy) in the content page's entry grammar;
#   K-ROOM (3a-3c)     rooms, so "in lab only" and "in commons only" are grants;
#   K-HISTORY-READ     for `doc follow` at the current height.
set -u
umask 077
: "${JOURNEY_STEP_DIR:?}" "${SHELL_BIN:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}" "${SPONSOR_WS:?}"
SD=$JOURNEY_STEP_DIR
mkdir -p -m 700 "$SD/home"
line="doc quote paper wall 1"
printf '%s\n' "$line" >"$SD/quote.line"
"$SHELL_BIN" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
  --workspace "$SPONSOR_WS" --home "$SD/home" --line "$line" >"$SD/quote.out" 2>"$SD/quote.err"
rc=$?
echo "$SD/quote.err"
if [ "$rc" = 0 ]; then
  echo "J12c: \`$line\` now succeeds; replace this stub with the four-grant J12c rows" >&2
  exit 1
fi
echo "J12c stub: \`$line\` -> rc $rc: $(head -1 "$SD/quote.err")" >&2
exit 1
