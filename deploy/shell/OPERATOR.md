# Operator: one friend, from their public key to "you're in"

This is ember's checklist for the Mini node on `dregg-workhorse` (2.28.141.27). Box
layout, units and scripts are in `dregg-infra/edge/mini/README.md`; this file only puts
them in order for one friend. Friends get `FRIENDS.md`.

Names used below:

```
BOX=dregg-workhorse            # root ssh
C=/var/lib/mini/candidate/current
NODE=/var/lib/mini/store/node   # Store, sponsor workspace (NODE/sponsor), socket
S=/var/lib/mini/sessions        # S/NAME = a friend's session home; S/ember = the sponsor's
ASMINI='systemd-run -q --wait --pipe --collect --slice=mini.slice --uid=mini --gid=mini -p UMask=0077 -E TMPDIR=/var/lib/mini/store/node/tmp --'
```

The sponsor session is `ssh -t -i ~/.ssh/id_portable mini@2.28.141.27` (`friends/ember.pub`;
its workspace is `NODE/sponsor` and its home is `S/ember`).

**Precondition.** The shipped candidate's client has `mini shell` and `provision`
(product-20260930 or later; `deploy-1.md` §"Phase 2"). Check it with
`ssh $BOX "sed -n 2p /etc/mini/authorized_keys"`, which must say `mode=open`. While it
says `mode=closed`, every friend gets `mini-closed` and exit 69.

## Per friend

1. **Receive the key.** You need exactly one line, `ssh-ed25519 AAAA… comment`, and a
   NAME matching `^[a-z][a-z0-9-]{0,31}$`. NAME names the session forever: a renamed
   file is a new, empty session.
2. **Roster.** From `~/dev/dregg-infra`:
   ```
   cp their.pub edge/mini/friends/NAME.pub
   git add edge/mini/friends/NAME.pub && git commit -m "mini: add friend NAME"
   edge/mini/render-authorized-keys.sh     # rsyncs friends/ and renders on the box; prints "N key(s), mode=open"
   ```
   There is no ship step. `ship.sh` re-renders too, but the roster needs only this.
   Rendering also creates `S/NAME` (mini, 0700).
3. **Their first login.** Tell them: `ssh -t -i ~/.ssh/mini mini@2.28.141.27`, then
   `keygen mini.key`. Check that the key exists:
   `ssh $BOX test -s $S/NAME/keys/mini.key.pub && echo ok`
   If they type `init` before step 6 is done, the shell answers one line
   (`error: init needs your provisioning at …/provision/birth-context.json …`) and
   makes nothing, so there is nothing to clean up.
4. **Custody copy (today's contract, `m4-shell.md` §Deviations 1).** `enroll plan` and
   `seal` sign with the sponsor's key and the newcomer's key in one process:
   ```
   ssh $BOX "install -d -o mini -g mini -m 0700 $S/ember/keys && \
             install -o mini -g mini -m 0600 $S/NAME/keys/mini.key $S/ember/keys/NAME.key && \
             install -o mini -g mini -m 0644 $S/NAME/keys/mini.key.next.pub $S/ember/keys/NAME.key.next.pub"
   ```
   The second file is the friend's NEXT public key (K-PREROTATE): enrollment commits to its
   digest, and `enroll plan` refuses without it. Only the public half travels; the next
   secret (`mini.key.next`) stays with the friend, who should move it off the box. A key
   made before pre-rotation has no `mini.key.next.pub`: the friend runs `keygen` again
   under a new name (keygen never overwrites), and you enroll that one.
5. **Enroll, from the sponsor session.**
   ```
   mini> enroll plan NAME NAME.key
   mini> enroll seal NAME
   mini> enroll submit NAME        # "authority": "admitted-key-only", "subject": "<SUBJECT>"; note SUBJECT
   ```
   `enroll lookup NAME` asks again and returns the same receipt. Afterwards remove the copy:
   `ssh $BOX rm $S/ember/keys/NAME.key` (keep `NAME.key.pub`).
6. **Provision (M3): factory observation plus a funded account the friend owns.**
   ```
   ssh $BOX "install -d -o mini -g mini -m 0700 $S/ember/requests && \
     printf '%s\n' '{\"type\":\"all\",\"predicates\":[]}' > $S/ember/requests/permit-all.json && \
     chown mini:mini $S/ember/requests/permit-all.json"          # once, not per friend
   ssh $BOX "$ASMINI $C/bin/mini workspace --action provision --dir $NODE/sponsor \
     --name NAME --holder SUBJECT --funding 1000 \
     --account-predicate $S/ember/requests/permit-all.json --factory-ref factory"
   ```
   This writes `NODE/sponsor/provisions/NAME/{provision.json,birth-context.json}`.
   `--action provision-lookup --dir $NODE/sponsor --name NAME --factory-ref factory` asks again.
   Deliver the birth context into their session home, where their `init` looks for it:
   ```
   ssh $BOX "install -d -o mini -g mini -m 0700 $S/NAME/provision && \
     install -o mini -g mini -m 0600 $NODE/sponsor/provisions/NAME/birth-context.json \
       $S/NAME/provision/birth-context.json"
   ```
7. **Tell them** their SUBJECT and "you're in: `init mini.key SUBJECT`, `whoami`, then the
   first 10 minutes." Their `init` binds `provision/birth-context.json` and a namespace at
   `$S/NAME/namespace` itself. `whoami` must show `"initialized": true` and their subject.

## Re-genesis, as friends experience it

Before: post in the friends' channel, e.g. "reset at HH:MM UTC. keys stay, everything you
made goes. i'll re-enroll you; then redo your first 10 minutes with new IDs."

1. Ship: `edge/mini/ship.sh L --regenesis` (`deploy-1.md` §"Phase 2" steps 1–3). The old
   Store moves to `store/retired-<ts>` and the sponsor workspace goes with it. Ship
   re-renders the roster and runs `mini-health`.
2. For every friend, move the old-Store state aside and keep the keys:
   ```
   ssh $BOX 'ts=$(date -u +%Y%m%dT%H%M%SZ); for d in /var/lib/mini/sessions/*/; do n=$(basename $d); \
     install -d -o mini -g mini -m 0700 $d/retired-$ts; \
     for x in workspace namespace provision requests inbox refusals enroll; do [ -e $d/$x ] && mv $d/$x $d/retired-$ts/; done; done'
   ```
   `requests/` must go too: request files are write-once, so an old ID with new content
   is refused. Then restore the permit-all file (step 6).
3. Redo steps 4–7 per friend (their `keys/mini.key` is still there; they do **not** keygen
   again). Their subject may change, so tell them the new one.

What friends redo: nothing until you say so, then their own resources, grants and
references. Hand-offs between friends (`export`/`import`) must be done again.

## Health, restart, backups

- **Health:** `ssh $BOX "$ASMINI /usr/local/lib/mini/mini-health"`. Healthy means a signed
  sponsor read of `factory` was answered, not that a pid exists.
- **Restart:** `ssh $BOX systemctl restart mini-store`, then health. A friend's `retry ID`
  afterwards returns `replayed`.
- **Backups:** `mini-backup.timer` runs nightly at 03:17 UTC. Archives are in `/var/lib/mini-backups/`
  (14 kept, and they contain the **sponsor secret key**), and the anchor pulls them off-box.
  List them: `ssh $BOX ls -l /var/lib/mini-backups`. Check one restores without touching
  anything live: `ssh $BOX /usr/local/lib/mini/mini-restore-check [ARCHIVE]`. For a real
  restore, follow the README §"Restore for real".
- **Not backed up: friends' session homes** (their secret keys, workspaces, requests). If
  the box is lost, friends keygen again and you redo steps 2–7.

## Removing a friend

1. `git rm edge/mini/friends/NAME.pub && git commit -m "mini: remove friend NAME"`, then
   `edge/mini/render-authorized-keys.sh`. Their ssh stops working at once.
2. Their signing key stays enrolled and their grants stay live in the Store, but the
   secret exists only in `S/NAME/keys` (and in `S/ember/keys/NAME.key` if step 5's `rm` was
   skipped: remove it). No verb prints a secret key.
3. Revoke what they were granted, from the session that delegated it (the owner's or
   yours): `revoke ID REF SUBJECT`, then `submit ID`. It revokes the capability that
   session delegated on REF to SUBJECT; their next read of REF is `refused: revoked`.
4. `S/NAME` is their data. Archive it or delete it by hand; the script doesn't decide that.
