#!/bin/sh
# scripts/burst/hbox-pull.sh BURST_ID GATE_USER@HOST -- installed on hbox by burst-up as
# ~/.local/bin/pull-<BURST_ID>-remote (+ a 10-min user timer): mirror the burst's shared git remote
# (main/next/green + every lane/<name>) into /tank/dregg-build/claude-lanes/bundles/<BURST_ID>-minidregg.git,
# over hbox's read-only puller key (authorized on the gate box as box-peer-gate: git fetch + rsync -ro only).
# Deliberately NOT --prune: a branch deleted on the box stays here. The boxes are disposable; this is not.
set -u
id=${1:?BURST_ID}; gate=${2:?GATE user@host}
key=$HOME/.ssh/${id}_pull
mirror=/tank/dregg-build/claude-lanes/bundles/${id}-minidregg.git
[ -d "$mirror" ] || git init -q --bare "$mirror"
exec env GIT_SSH_COMMAND="ssh -i $key -o IdentitiesOnly=yes -o BatchMode=yes -o StrictHostKeyChecking=accept-new -o ConnectTimeout=30" \
  git --git-dir="$mirror" fetch -q "$gate:/srv/git/minidregg.git" "+refs/heads/*:refs/heads/*" "+refs/tags/*:refs/tags/*"
