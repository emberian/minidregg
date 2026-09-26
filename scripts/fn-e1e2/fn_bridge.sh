#!/bin/sh
set -eu
[ "$1" = "--fn" ] || exit 64
verb=$2
image=${FN_B3_IMAGE:?FN_B3_IMAGE must name the frozen fn image}
case "$image" in /tank/fn/gates/*) ;; *) exit 64;; esac
case "$image" in *[!A-Za-z0-9_./-]*) exit 64;; esac
remote_dir=$(ssh hbox 'mktemp -d /tmp/fn-mini-e2.XXXXXX')
case "$remote_dir" in /tmp/fn-mini-e2.*) ;; *) exit 70;; esac
cleanup() {
  status=$?
  trap - EXIT
  ssh hbox "rm -rf $remote_dir" >/dev/null 2>&1 || true
  exit "$status"
}
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
case "$verb" in
  hybrid-author)
    [ "$#" -eq 8 ] || exit 64
    case "$3" in *[!A-Za-z0-9_./-]*|'') exit 64;; esac
    case "$4" in *[!0-9]*|'') exit 64;; esac
    scp -q "$5" "hbox:$remote_dir/source"
    scp -q "$6" "hbox:$remote_dir/ed.sig"
    scp -q "$7" "hbox:$remote_dir/ml.sig"
    scp -q "$8" "hbox:$remote_dir/ml-public.pem"
    if [ "${FN_E1E2_DROP_POST_REPLY:-0}" = 1 ]; then
      ssh hbox "FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 $image --fn hybrid-author $3 $4 $remote_dir/source $remote_dir/ed.sig $remote_dir/ml.sig $remote_dir/ml-public.pem" >/dev/null
      exit 75
    fi
    ssh hbox "FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 $image --fn hybrid-author $3 $4 $remote_dir/source $remote_dir/ed.sig $remote_dir/ml.sig $remote_dir/ml-public.pem"
    ;;
  hybrid-sign-carrier)
    [ "$#" -eq 9 ] || exit 64
    case "$5" in *[!A-Za-z0-9_./-]*|'') exit 64;; esac
    case "$7" in *[!A-Za-z0-9_./-]*|'') exit 64;; esac
    scp -q "$3" "hbox:$remote_dir/principal"
    scp -q "$4" "hbox:$remote_dir/ed-public"
    scp -q "$6" "hbox:$remote_dir/ml-public.pem"
    scp -q "$8" "hbox:$remote_dir/source"
    ssh hbox "FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 $image --fn hybrid-sign-carrier $remote_dir/principal $remote_dir/ed-public $5 $remote_dir/ml-public.pem $7 $remote_dir/source $remote_dir/carrier"
    scp -q "hbox:$remote_dir/carrier" "$9"
    ;;
  hybrid-sign)
    [ "$#" -eq 8 ] || exit 64
    case "$5" in *[!A-Za-z0-9_./-]*|'') exit 64;; esac
    case "$7" in *[!A-Za-z0-9_./-]*|'') exit 64;; esac
    scp -q "$3" "hbox:$remote_dir/principal"
    scp -q "$4" "hbox:$remote_dir/ed-public"
    scp -q "$6" "hbox:$remote_dir/ml-public.pem"
    scp -q "$8" "hbox:$remote_dir/source"
    ssh hbox "FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 $image --fn hybrid-sign $remote_dir/principal $remote_dir/ed-public $5 $remote_dir/ml-public.pem $7 $remote_dir/source"
    ;;
  consumer-project)
    [ "$#" -eq 4 ] || exit 64
    scp -q "$3" "hbox:$remote_dir/cursor"
    scp -q "$4" "hbox:$remote_dir/event"
    ssh hbox "FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 $image --fn consumer-project $remote_dir/cursor $remote_dir/event"
    ;;
  consumer-inspect)
    [ "$#" -eq 3 ] || exit 64
    scp -q "$3" "hbox:$remote_dir/cursor"
    ssh hbox "FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 $image --fn consumer-inspect $remote_dir/cursor"
    ;;
  hybrid-verify-source)
    [ "$#" -eq 4 ] || exit 64
    scp -q "$3" "hbox:$remote_dir/carrier"
    scp -q "$4" "hbox:$remote_dir/ml.pem"
    ssh hbox "FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 $image --fn hybrid-verify-source $remote_dir/carrier $remote_dir/ml.pem"
    ;;
  consumer)
    case "$3" in
      status)
        [ "$#" -eq 5 ] || exit 64
        case "$4" in *[!A-Za-z0-9_./-]*|'') exit 64;; esac
        case "$5" in *[!A-Za-z0-9_-]*|'') exit 64;; esac
        ssh hbox "FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 $image --fn consumer status $4 $5"
        ;;
      poll)
        [ "$#" -eq 7 ] || exit 64
        case "$4" in *[!A-Za-z0-9_./-]*|'') exit 64;; esac
        case "$5" in *[!A-Za-z0-9_-]*|'') exit 64;; esac
        ssh hbox "FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 $image --fn consumer poll $4 $5 $remote_dir/cursor $remote_dir/event"
        scp -q "hbox:$remote_dir/event" "$7"
        scp -q "hbox:$remote_dir/cursor" "$6"
        ;;
      ack)
        [ "$#" -eq 5 ] || exit 64
        case "$4" in *[!A-Za-z0-9_./-]*|'') exit 64;; esac
        scp -q "$5" "hbox:$remote_dir/cursor"
        if [ "${FN_E1E2_DROP_ACK_REPLY:-0}" = 1 ]; then
          ssh hbox "FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 $image --fn consumer ack $4 $remote_dir/cursor" >/dev/null
          exit 75
        fi
        ssh hbox "FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 $image --fn consumer ack $4 $remote_dir/cursor"
        ;;
      position)
        [ "$#" -eq 6 ] || exit 64
        case "$4" in *[!A-Za-z0-9_./-]*|'') exit 64;; esac
        case "$5" in *[!A-Za-z0-9_-]*|'') exit 64;; esac
        ssh hbox "FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8 $image --fn consumer position $4 $5 $remote_dir/position"
        scp -q "hbox:$remote_dir/position" "$6"
        ;;
      *) exit 64;;
    esac
    ;;
  *) exit 64;;
esac
