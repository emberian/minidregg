#!/bin/sh
set -eu
F=/home/hbox/mini-ticket-tool-fixture-r8
command=$1
shift
case "$command" in
  query)
    while [ "$#" -gt 0 ]; do case "$1" in --dir) D=$2; shift 2;; *) shift;; esac; done
    mkdir -m 700 "$D"
    if [ -f "$F/fail-after-once" ] && [ -f "$F/sends.log" ]; then
      rm "$F/fail-after-once"
      exit 1
    fi
    status=1 remaining=25 reserved=0
    if [ -f "$F/sends.log" ]; then status=3 remaining=22 reserved=3; fi
    [ ! -e "$F/bad-status" ] || status=0
    printf '{"page":{"root":"123","grain":{"task":"7902","generation":"1","status":"%s","remaining":"%s","reserved":"%s"}}}\n' "$status" "$remaining" "$reserved" > "$D/view.json"
    printf '{"signing":[{"authorityRoot":"456"}]}\n' > "$D/challenge.json"
    chmod 600 "$D/view.json" "$D/challenge.json"
    ;;
  submit)
    while [ "$#" -gt 0 ]; do case "$1" in --dir) D=$2; shift 2;; *) shift;; esac; done
    mkdir -m 700 "$D"
    printf 'exact-mock-call' > "$D/call.bin"
    chmod 600 "$D/call.bin"
    ;;
  retry)
    while [ "$#" -gt 0 ]; do case "$1" in --attempt) D=$2; shift 2;; --mode) M=$2; shift 2;; *) shift;; esac; done
    case "$M" in
      submit)
        printf 'submit\n' >> "$F/sends.log"
        printf '{"type":"confirmed","confirmation":"installed","transactionId":"101","eventId":"102","acceptedCount":"30","imageBoundary":"103"}\n' > "$D/retry-0001.json"
        chmod 600 "$D/retry-0001.json"
        exit 1;;
      lookup)
        printf 'lookup\n' >> "$F/lookups.log"
        printf '{"type":"confirmed","confirmation":"replayed","transactionId":"101","eventId":"102","acceptedCount":"30","imageBoundary":"103"}\n' > "$D/retry-0002.json"
        chmod 600 "$D/retry-0002.json";;
      *) exit 2;;
    esac;;
  grain-share-issue-lookup)
    printf 'ticket-lookup\n' >> "$F/ticket-lookups.log"
    printf '{"type":"confirmed","confirmation":"replayed","transactionId":"201","eventId":"202","acceptedCount":"31","imageBoundary":"203"}\n';;
  *) exit 2;;
esac
