for last; do :; done
mode=$last
req="${TMPDIR:-/tmp}/mini-sdk-ssh-$last.req"
case "$mode" in
  hostkey) echo "No ED25519 host key is known for box and you have requested strict checking." >&2; echo "Host key verification failed." >&2; exit 255;;
  denied) echo "member@box: Permission denied (publickey)." >&2; exit 255;;
  refused) echo "ssh: connect to host box port 22: Connection refused" >&2; exit 255;;
  garbled) echo "something ssh never prints" >&2; exit 255;;
  silent) sleep 20; exit 0;;
  remote-*) ;;
  *) echo "debug1: Authenticated to box ([203.0.113.1]:22) using \"publickey\"." >&2
     echo "debug1: Entering interactive session." >&2;;
esac
while :; do
  n=$(dd bs=1 count=4 2>/dev/null | od -An -tu4 -v | tr -d ' ')
  [ -z "$n" ] && exit 0
  dd bs=1 count="$n" 2>/dev/null >> "$req"
  case "$mode" in
    *hangup) exit 255;;
    *mute) sleep 20; exit 0;;
    *garbage) printf '\000\000\000\000';;
    *refuse) printf '\003\000\000\000\377no';;
    *reject) printf '\002\000\000\000\376x';;
    *) printf '\003\000\000\000\002ok';;
  esac
done
