#!/usr/bin/env bash
# JPROTECTED-DOCS candidate: source-owned protected documents on the existing
# J-DOCUVERSE Store. This file has only had bash syntax checking; it does not
# claim a completed journey. Run after the common Host all-holder gate lands.
# No fixture enrollment, replacement Store, room-key shortcut, or service kill.
# "Reopen" below means fresh client processes reopening durable key custody;
# it does not claim a cold Host/Store restart or process-crash fault injection.
set -euo pipefail
umask 077
: "${JOURNEY_STEP_DIR:?}" "${JOURNEY_WORLD:?}" "${JOURNEY_RUN:?}"
: "${MINI:?}" "${HOST:?}" "${CONFIG:?}" "${SOCKET:?}"
SD=$JOURNEY_STEP_DIR
STORE=${PD_STORE_DIR:-$JOURNEY_WORLD/store}
FIXTURE=${PD_FIXTURE_DIR:-$JOURNEY_RUN/steps/JDV}
OWNER_WS=${PD_OWNER_WS:-$FIXTURE/w/amy}
MEMBER_WS=${PD_MEMBER_WS:-$FIXTURE/w/ben}
OWNER_HOME=${PD_OWNER_HOME:-$FIXTURE/h/amy}
MEMBER_HOME=${PD_MEMBER_HOME:-$FIXTURE/h/ben}
DOC=${PD_DOCUMENT:-pd-paper}
CAT=${PD_CATALOG:-pd-paper-catalog}
# Must name the actual source gate; unrelated law/stale/transport failures do
# not satisfy this row. Override only for the common Host's precise spelling.
ALL_HOLDER_REASON=${PD_ALL_HOLDER_REASON:-audience.*transition|transition.*audience}
AUTH_REASON='revoked|no-grant|noGrant|undisclosed|not.standing|unauthorized|authorization'
for file in "$OWNER_WS/workspace.json" "$MEMBER_WS/workspace.json"; do
  [ -f "$file" ] || { echo "JPROTECTED-DOCS missing fixture: $file" >&2; exit 1; }
done
case "$DOC:$CAT" in *[!a-zA-Z0-9_.:-]*) echo 'use simple local document/catalog names' >&2; exit 1;; esac
[ ! -e "$OWNER_WS/refs/$DOC.json" ] || { echo 'choose PD_DOCUMENT for a fresh journey document' >&2; exit 1; }
mkdir -p "$SD/log" "$OWNER_HOME/requests" "$MEMBER_HOME/requests"
TABLE=$SD/jprotected-docs.tsv
printf 'row\tcheck\tresult\tevidence\n' >"$TABLE"
printf '%s\n' '{"state":"running","coldHostRestart":false}' >"$SD/status.json"
N=0
fail() {
  printf '%s\t%s\tFAIL\t%s\n' "$N" "$1" "${ERR:-}" >>"$TABLE"
  printf '%s\n' '{"state":"failed","coldHostRestart":false}' >"$SD/status.json"
  echo "$TABLE"
  echo "JPROTECTED-DOCS: $1; see $TABLE" >&2
  exit 1
}
row() { printf '%s\t%s\tok\t%s\n' "$N" "$1" "${2:-}" >>"$TABLE"; }
check() {
  local label=$1; shift
  N=$((N + 1)); OUT=$SD/log/$N.out; ERR=$SD/log/$N.err
  "$@" >"$OUT" 2>"$ERR" || fail "$label"
  row "$label" "$OUT"
}
run_as() {
  shift
  "$@"

}
line() {
  local who=$1 text=$2 ws home
  if [ "$who" = owner ]; then ws=$OWNER_WS; home=$OWNER_HOME
  else ws=$MEMBER_WS; home=$MEMBER_HOME; fi
  N=$((N + 1)); OUT=$SD/log/$N.out; ERR=$SD/log/$N.err
  printf '%s\n' "$text" >"$SD/log/$N.line"
  if run_as "$who" "$MINI" shell --socket "$SOCKET" --host "$HOST" --config "$CONFIG" \
    --workspace "$ws" --home "$home" --line "$text" >"$OUT" 2>"$ERR"; then RC=0; else RC=$?; fi
}
ok() {
  line "$1" "$2"
  [ "$RC" = 0 ] || fail "$1: $2"
  row "$1: $2" "$OUT"
}
refused() {
  local who=$1 command=$2 reason=$3
  line "$who" "$command"
  [ "$RC" != 0 ] && grep -Eiq -- "$reason" "$ERR" || fail "$who: $command did not refuse for $reason (rc $RC)"
  row "$who: $command refused for $reason" "$ERR"
}
pull() { ok "$1" "doc pull $DOC"; cp "$OUT" "$2"; }
seen() {
  if [ "$1" = owner ]; then cp "$OWNER_WS/seen/$DOC.json" "$2"
  else cp "$MEMBER_WS/seen/$DOC.json" "$2"; fi
}

# Artifact assertions use signed raw entries and their separate local opening.
# They never decrypt or print storage.key or the encrypted custody journal.
cat >"$SD/assert.py" <<'PY'
import json, pathlib, sys
def load(p): return json.loads(pathlib.Path(p).read_text())
def raw(v): return {x['id']: x for x in v['view']['cell']['entries'] if x['type']=='atom'}
def opened(v): return {x['id']: x for x in v['openedEntries'] if x['type']=='atom'}
def epoch(a):
    assert a['kind']['type']=='sealedObject' and a['payload']=='', 'atom is not an authored protected fragment'
    b=bytes.fromhex(a['kind']['fragment']['wrapping']); f=b'MINI/PROTECTED-AUTHORED-WRAP/v1'
    assert b.startswith(f), 'atom is not protected ciphertext'
    start=len(f)+32; msg=b'MINI/OBJECT-MESSAGE/v1'
    assert b[start:].startswith(msg), 'wrong protected message frame'
    start+=len(msg)+32
    return int.from_bytes(b[start:start+8], 'big')
mode, *args=sys.argv[1:]
if mode=='fixtures':
    a,b=map(load,args[:2]); config=pathlib.Path(args[2]).resolve()
    assert a['subject']!=b['subject'], 'fixtures must be distinct participants'
    assert a['socket']==b['socket']==args[3], 'fixtures must pin this journey socket'
    assert pathlib.Path(a['config']).resolve()==pathlib.Path(b['config']).resolve()==config, 'fixtures must use this journey configuration'
elif mode=='detached':
    before,after=map(load,args[:2]); wanted=args[2]; unlocked=args[3]=='owner'
    matches=[a['id'] for a in before['openedEntries'] if isinstance(a.get('private'),dict) and a['private'].get('text')==wanted]
    assert len(matches)==1, 'expected exactly one detached historical atom'
    key=matches[0]; assert raw(before)[key]==raw(after)[key], 'detached atom was rewritten'
    private=opened(after)[key].get('private')
    if unlocked: assert isinstance(private,dict) and private.get('text')==wanted, 'owner lost historical key'
    else: assert isinstance(private,str) and 'locked' in private, 'new member can open detached history'
elif mode=='shared':
    before,after,bundle=map(load,args)
    old=raw(before); new=raw(after); target=int(bundle['epoch']['epoch'])
    assert target>min(epoch(a) for a in old.values()), 'sharing failed to rotate epoch'
    # The two placed seed lines rotate; the removed third line does not.
    for a in opened(before).values():
        private=a.get('private'); value=private.get('text') if isinstance(private,dict) else None
        if value in ('PROTECTED-DOCS-first','PROTECTED-DOCS-second'):
            assert epoch(new[a['id']])==target, 'current text was not rekeyed'
            prior=old[a['id']];current=new[a['id']]
            for key in ('document','payload','createdBy','createdAt','revision','tombstonedAt'):
                assert prior[key]==current[key], f'atom semantic field changed: {key}'
            for key in ('ciphertext','author','operation'):
                assert prior['kind']['fragment'][key]==current['kind']['fragment'][key], f'authored atom changed: {key}'
            assert prior['kind']['fragment']['wrapping']!=current['kind']['fragment']['wrapping'], 'key wrapping did not rotate'
elif mode=='annotations':
    before,after=map(load,args[:2]);wanted=args[2]
    def annotations(v, projection=False):
        return {x['id']:x for x in (v['openedEntries'] if projection else v['view']['cell']['entries']) if x['type']=='annotation'}
    old,new=annotations(before),annotations(after)
    matches=[x['id'] for x in annotations(before,True).values() if isinstance(x.get('private'),dict) and x['private'].get('text')==wanted]
    assert len(matches)==1, 'expected exactly one authored comment'
    aid=matches[0];a,b=old[aid],new[aid]
    for key in ('author','operation','anchor','tombstonedAt'):
        assert a[key]==b[key], f'annotation origin changed: {key}'
    assert a['body']['fragment']['ciphertext']==b['body']['fragment']['ciphertext'], 'authored ciphertext was resealed'
    assert a['body']['fragment']['wrapping']!=b['body']['fragment']['wrapping'], 'annotation key wrapping did not rotate'
    assert annotations(after,True)[aid]['private']['text']==wanted, 'legitimate member cannot open old comment'
elif mode=='annotation-fresh' or mode=='annotation-stale':
    view=load(args[0]);wanted=args[1]
    matches=[a for a in view['openedEntries'] if a['type']=='annotation' and isinstance(a.get('private'),dict) and a['private'].get('text')==wanted]
    assert len(matches)==1 and matches[0]['fresh'] is (mode=='annotation-fresh'), 'semantic comment freshness differs'
elif mode=='custody':
    before,after=map(load,args);old,new=raw(before),raw(after)
    changed=0
    assert old.keys()==new.keys(), 'custody changed atom identities'
    for aid,prior in old.items():
        current=new[aid]
        for key in ('document','payload','createdBy','createdAt','revision','tombstonedAt'):
            assert prior[key]==current[key], f'custody changed semantic atom field: {key}'
        if prior['kind']['type']=='sealedObject':
            for key in ('ciphertext','author','operation'):
                assert prior['kind']['fragment'][key]==current['kind']['fragment'][key], f'authored atom changed: {key}'
            changed+=prior['kind']['fragment']['wrapping']!=current['kind']['fragment']['wrapping']
    assert changed>0, 'no current atom wrapping rotated'
elif mode=='same-atoms':
    assert raw(load(args[0]))==raw(load(args[1])), 'refused write changed source atoms'
elif mode=='rotation':
    before,after=map(load,args)
    assert int(after['epoch'])>int(before['epoch']), 'revocation did not advance epoch'
elif mode=='scan':
    needle=b'PROTECTED-DOCS-'
    count=0
    for base in map(pathlib.Path,args):
        assert base.exists(), f'missing ciphertext scan root: {base}'
        for p in base.rglob('*'):
            if not p.is_file(): continue
            if base.name=='proposals' and p.name!='intent.json': continue
            data=p.read_bytes(); count+=1
            assert needle not in data and needle.hex().encode() not in data, f'plaintext in {p}'
    assert count>0
    print(f'checked {count} persisted source/intent files')
else: raise SystemExit('unknown assertion')
PY
check 'distinct existing participants on this same Store/socket' python3 "$SD/assert.py" fixtures \
  "$OWNER_WS/workspace.json" "$MEMBER_WS/workspace.json" "$CONFIG" "$SOCKET"
MEMBER=$(jq -er .subject "$MEMBER_WS/workspace.json")
printf '%s\n' '{"type":"all","predicates":[]}' >"$SD/document-law.json"
check 'create empty content document with all[] law' run_as owner "$MINI" workspace --socket "$SOCKET" \
  --action doc-new --dir "$OWNER_WS" --name "$DOC" --predicate "$SD/document-law.json"
ok owner "doc protect $DOC"
ok owner "doc protect-recover $DOC"
ok owner 'doc device'; cp "$OUT" "$SD/owner-device.json"
ok member 'doc device'; cp "$OUT" "$SD/member-device.json"
cp "$SD/member-device.json" "$OWNER_HOME/requests/pd-device.json"
pull owner "$SD/empty.txt"
printf 'PROTECTED-DOCS-first\nPROTECTED-DOCS-second\nPROTECTED-DOCS-detached-history\n' >"$OWNER_HOME/requests/pd-edit.md"
ok owner "doc push pd-seed $DOC @pd-edit.md"
pull owner "$SD/seed.txt"; seen owner "$SD/seed-seen.json"
ok owner "doc remove $DOC 3"
pull owner "$SD/annotation-anchor.txt"
ok owner "doc annotate pd-comment $DOC 1 PROTECTED-DOCS-owner-comment"
ok owner 'submit pd-comment'
pull owner "$SD/before-share.txt"; seen owner "$SD/before-share-seen.json"
check 'line removal preserves the encrypted historical atom' python3 "$SD/assert.py" detached \
  "$SD/seed-seen.json" "$SD/before-share-seen.json" PROTECTED-DOCS-detached-history owner

ok owner "doc share pd-share $DOC $MEMBER @pd-device.json @pd-invitation.json"
cp "$OWNER_HOME/requests/pd-invitation.json" "$SD/invitation.json"
ok owner "doc membership-recover pd-share $DOC @pd-invitation-recovered.json"
check 'completed share recovery exports identical invitation' cmp \
  "$SD/invitation.json" "$OWNER_HOME/requests/pd-invitation-recovered.json"
cp "$SD/invitation.json" "$MEMBER_HOME/requests/pd-invitation.json"
ok member "doc accept $DOC $CAT @pd-invitation.json"
pull member "$SD/member-shared.txt"; seen member "$SD/member-shared-seen.json"
check 'member opens exactly the placed text' cmp "$SD/before-share.txt" "$SD/member-shared.txt"
check 'shared current atoms use new epoch' python3 "$SD/assert.py" shared \
  "$SD/before-share-seen.json" "$SD/member-shared-seen.json" "$SD/invitation.json"
check 'new member opens old authored comment without resealing it' python3 "$SD/assert.py" annotations \
  "$SD/before-share-seen.json" "$SD/member-shared-seen.json" PROTECTED-DOCS-owner-comment
ok member "doc show $DOC"; check 'comment appears in member rendered view' grep -F PROTECTED-DOCS-owner-comment "$OUT"
check 'key maintenance retains original comment anchor and freshness' python3 "$SD/assert.py" annotation-fresh \
  "$SD/member-shared-seen.json" PROTECTED-DOCS-owner-comment
check 'new member cannot open untouched detached history' python3 "$SD/assert.py" detached \
  "$SD/seed-seen.json" "$SD/member-shared-seen.json" PROTECTED-DOCS-detached-history member

pull member "$MEMBER_HOME/requests/pd-edit.md"
printf 'PROTECTED-DOCS-member-first\nPROTECTED-DOCS-second\n' >"$MEMBER_HOME/requests/pd-edit.md"
ok member "doc push pd-member-edit $DOC @pd-edit.md"
pull owner "$SD/owner-after-member.txt"; seen owner "$SD/owner-after-member-seen.json"
check 'genuine text editing preserves original comment anchor with honest stale marker' python3 "$SD/assert.py" annotation-stale \
  "$SD/owner-after-member-seen.json" PROTECTED-DOCS-owner-comment
pull member "$SD/member-comment-anchor.txt"
ok member "doc annotate pd-member-comment $DOC 2 PROTECTED-DOCS-member-comment"
ok member 'submit pd-member-comment'
pull member "$SD/member-comments.txt"; seen member "$SD/member-comments-seen.json"
check 'owner receives member edit' cmp "$MEMBER_HOME/requests/pd-edit.md" "$SD/owner-after-member.txt"
pull member "$MEMBER_HOME/requests/pd-stale.md"
ok owner "doc edit pd-owner-edit $DOC 1 PROTECTED-DOCS-owner-newer"
ok owner 'submit pd-owner-edit'
printf 'PROTECTED-DOCS-member-stale\nPROTECTED-DOCS-second\n' >"$MEMBER_HOME/requests/pd-stale.md"
refused member "doc push pd-stale $DOC @pd-stale.md" 'stale-line|staleAtom'

# Each shell call is a new process. Freeze copies here and compare after reads:
# opening custody must preserve the exact journal and device generation.
cp "$MEMBER_WS/protected-documents/keys.json" "$SD/member-before-reopen.keys"
cp "$MEMBER_WS/protected-documents/storage.key" "$SD/member-storage.key"
pull owner "$SD/before-reopen.txt"
pull member "$SD/after-reopen.txt"
check 'fresh process reopens current document' cmp "$SD/before-reopen.txt" "$SD/after-reopen.txt"
ok member 'doc device'
check 'fresh process preserves device generation' cmp "$SD/member-device.json" "$OUT"
check 'read-only reopen preserves encrypted key journal' cmp "$SD/member-before-reopen.keys" "$MEMBER_WS/protected-documents/keys.json"
check 'read-only reopen preserves storage key' cmp "$SD/member-storage.key" "$MEMBER_WS/protected-documents/storage.key"

# Revoking the grant alone leaves its holder in the current epoch roster.
# Fresh owner ciphertext must be refused by the real all-holder source gate.
ok owner "doc epoch-export $DOC @pd-shared-epoch.json"
ok owner "revoke pd-ordinary-revoke $DOC $MEMBER"
ok owner 'submit pd-ordinary-revoke'
pull owner "$SD/before-blocked.txt"; seen owner "$SD/before-blocked-seen.json"
line owner "doc append pd-blocked $DOC PROTECTED-DOCS-must-not-enter"
if [ "$RC" = 0 ]; then
  row 'owner prepares fresh protected bytes against revoked holder' "$OUT"
  refused owner 'submit pd-blocked' "$ALL_HOLDER_REASON"
else
  grep -Eiq -- "$ALL_HOLDER_REASON" "$ERR" || fail 'fresh owner bytes did not reach the all-holder refusal'
  row 'Host authoring refuses fresh bytes for revoked roster holder' "$ERR"
fi
pull owner "$SD/after-blocked.txt"; seen owner "$SD/after-blocked-seen.json"
check 'all-holder refusal admits no new atoms or edits' python3 "$SD/assert.py" same-atoms \
  "$SD/before-blocked-seen.json" "$SD/after-blocked-seen.json"
ok owner "doc epoch-export $DOC @pd-after-block-epoch.json"
check 'fresh source observation still commits the same epoch and manifest' cmp \
  "$OWNER_HOME/requests/pd-shared-epoch.json" "$OWNER_HOME/requests/pd-after-block-epoch.json"
refused member "doc pull $DOC" "$AUTH_REASON"

# Coordinated revoke must tolerate the already nonstanding document grant.
ok owner "doc revoke pd-cut $DOC $MEMBER"
ok owner "doc membership-recover pd-cut $DOC"
ok owner "doc epoch-export $DOC @pd-current-epoch.json"
check 'coordinated revocation advances epoch' python3 "$SD/assert.py" rotation \
  "$OWNER_HOME/requests/pd-shared-epoch.json" "$OWNER_HOME/requests/pd-current-epoch.json"
pull owner "$SD/rotated.txt"; seen owner "$SD/rotated-seen.json"
check 'revoke custody preserves semantic revisions and authored atom payloads' python3 "$SD/assert.py" custody \
  "$SD/before-blocked-seen.json" "$SD/rotated-seen.json"
ok owner "doc edit pd-post-cut $DOC 2 PROTECTED-DOCS-owner-after-cut"
ok owner 'submit pd-post-cut'
pull owner "$SD/owner-final.txt"; seen owner "$SD/owner-final-seen.json"
check 'revocation rotates owner comment wrapping while retaining its authorship' python3 "$SD/assert.py" annotations \
  "$SD/member-comments-seen.json" "$SD/owner-final-seen.json" PROTECTED-DOCS-owner-comment
check 'revocation rotates departed author comment wrapping while retaining its authorship' python3 "$SD/assert.py" annotations \
  "$SD/member-comments-seen.json" "$SD/owner-final-seen.json" PROTECTED-DOCS-member-comment
check 'owner editing resumes after revocation rotation' grep -Fx PROTECTED-DOCS-owner-after-cut "$SD/owner-final.txt"
check 'owner still opens historical epoch; detached atom never rekeyed' python3 "$SD/assert.py" detached \
  "$SD/seed-seen.json" "$SD/owner-final-seen.json" PROTECTED-DOCS-detached-history owner
cp "$MEMBER_WS/protected-documents/keys.json" "$SD/member-before-refusals.keys"
cp "$OWNER_HOME/requests/pd-current-epoch.json" "$MEMBER_HOME/requests/pd-current-epoch.json"
jq .epoch "$SD/invitation.json" >"$MEMBER_HOME/requests/pd-old-epoch.json"
refused member "doc pull $DOC" "$AUTH_REASON"
refused member "doc insert $DOC 1 PROTECTED-DOCS-excluded-write" "$AUTH_REASON"
refused member "doc epoch-import $DOC $CAT @pd-old-epoch.json" "$AUTH_REASON"
refused member "doc epoch-import $DOC $CAT @pd-current-epoch.json" "$AUTH_REASON"
check 'refusals retain member historical key journal exactly' cmp "$SD/member-before-refusals.keys" "$MEMBER_WS/protected-documents/keys.json"
check 'refusals retain original member storage key' cmp "$SD/member-storage.key" "$MEMBER_WS/protected-documents/storage.key"
pull owner "$SD/after-excluded-writes.txt"
check 'excluded member changed no current text' cmp "$SD/owner-final.txt" "$SD/after-excluded-writes.txt"
check 'source and submitted intents contain no document plaintext' python3 "$SD/assert.py" scan \
  "$STORE" "$OWNER_WS/proposals" "$MEMBER_WS/proposals"
printf '%s\n' '{"state":"passed","coldHostRestart":false,"crashInjection":false}' >"$SD/status.json"
echo "$TABLE"
echo "JPROTECTED-DOCS: $N rows passed on existing Store; client custody reopen only" >&2
