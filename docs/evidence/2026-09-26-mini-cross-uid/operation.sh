#!/bin/sh
set -eu
umask 077
mode=$1 who=$2 subject=$3 cap=$4 nonce=$5 label=$6
home=/tmp/mini-cross-task-$who-20260926
public=/tmp/mini-cross-front-$who-signed-20260926
mini=/tmp/mini-cross-account-bin-20260926/mini-v2-current
host=/tmp/mini-cross-account-bin-20260926/host
cd "$home"
case "$mode" in
  query|deny)
    target=$7
    jq -n --arg subject "$subject" --arg cap "$cap" --arg nonce "$nonce" --arg target "$target" \
      '{subject:$subject,nonce:$nonce,purpose:{type:"query",kind:"object",target:$target,view:"resource"},grants:[{kind:"object",target:$target,capability:$cap}]}' > "$label-intent.json"
    if [ "$mode" = query ]; then
      "$mini" query --host "$host" --config "$public/host.json" --socket "$public/host.sock" \
        --intent "$label-intent.json" --key key --view resource --dir "$label" > "$label.stdout" 2> "$label.stderr"
      jq -r .page.root "$label/view.json"
    else
      if "$mini" query --host "$host" --config "$public/host.json" --socket "$public/host.sock" \
        --intent "$label-intent.json" --key key --view resource --dir "$label" > "$label.stdout" 2> "$label.stderr"; then
        echo 'unexpectedly authorized' >&2; exit 1
      fi
      test -s "$label/signed-observation.bin"
      test ! -e "$label/view.json"
      grep -Fq 'host refused query' "$label.stderr"
      grep -Fq "$(printf 'observation refused' | od -An -tx1 -v | tr -d ' \n')" "$label.stderr"
      echo "$label native signed observation refused"
    fi
    ;;
  create|edit)
    observed=$7
    payload=$(printf '%s' "$8" | od -An -tx1 -v | tr -d ' \n')
    if [ "$mode" = create ]; then
      jq -n --slurpfile view "$observed/view.json" --slurpfile challenge "$observed/challenge.json" \
        --arg subject "$subject" --arg cap "$cap" --arg nonce "$nonce" --arg payload "$payload" \
        '{subject:$subject,nonce:$nonce,purpose:{type:"prepare",draft:{type:"invoke",
          command:{subject:$subject,expectedAuthorityRoot:$challenge[0].signing[0].authorityRoot,
            nonce:($nonce + "1"),targets:[{kind:"object",target:"8001",capability:$cap,
              observeCapability:null,schemaVersion:"1",expectedTargetRoot:$view[0].page.root,
              payload:{type:"content",actions:[{type:"createAtom",atom:"7401",
                kind:{type:"text"},payload:$payload}]}}]}}},
          grants:[{kind:"object",target:"8001",capability:$cap}]}' > "$label-intent.json"
    else
      jq -n --slurpfile view "$observed/view.json" --slurpfile challenge "$observed/challenge.json" \
        --arg subject "$subject" --arg cap "$cap" --arg nonce "$nonce" --arg payload "$payload" \
        '{subject:$subject,nonce:$nonce,purpose:{type:"prepare",draft:{type:"invoke",
          command:{subject:$subject,expectedAuthorityRoot:$challenge[0].signing[0].authorityRoot,
            nonce:($nonce + "1"),targets:[{kind:"object",target:"8001",capability:$cap,
              observeCapability:"98",schemaVersion:"1",expectedTargetRoot:$view[0].page.root,
              payload:{type:"content",actions:[{type:"editAtom",atom:"7401",
                before:($view[0].page.entries[0] | {document,kind,payload,createdBy,createdAt,tombstonedAt}),
                kind:{type:"text"},payload:$payload,tombstone:false}]}}]}}},
          grants:[{kind:"object",target:"8001",capability:"98"}]}' > "$label-intent.json"
    fi
    "$mini" submit --host "$host" --config "$public/host.json" --socket "$public/host.sock" \
      --intent "$label-intent.json" --key key --dir "$label-attempt" > "$label.stdout" 2> "$label.stderr"
    jq -e '.type == "confirmed" and .confirmation == "installed"' "$label-attempt/outcome.json" >/dev/null
    jq -r .acceptedCount "$label-attempt/outcome.json"
    ;;
  *) exit 2;;
esac
