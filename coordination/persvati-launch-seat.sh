#!/usr/bin/env bash
set -euo pipefail
seat=$1; lane=$2; body=$3; unit=$4
case "$lane" in /home/ember/workbox/persvati-*) ;; *) exit 64;; esac
case "$unit" in persvati-*) ;; *) exit 64;; esac
case "$seat" in
 lean-main) mem=16G;cpu=400%;seconds=300;min_kib=18874368 ;;
 lean-leaf[1-6]) mem=4G;cpu=200%;seconds=300;min_kib=6291456 ;;
 rust[12]) mem=8G;cpu=400%;seconds=1800;min_kib=10485760 ;;
 *) exit 64;;
esac
available=$(awk '/MemAvailable/{print $2}' /proc/meminfo)
[ "$available" -ge "$min_kib" ] || { echo 'persvati-job: VERDICT outcome=REFUSED reason=headroom';exit 75; }
test -f "$body";mkdir -p "$lane"
exec systemd-run --user --quiet --unit="$unit" --property=MemoryMax="$mem" --property=MemorySwapMax=0 --property=CPUQuota="$cpu" --property=TasksMax=256 --property=RuntimeMaxSec="$seconds" --property=KillMode=control-group --property=OOMPolicy=stop /bin/bash /home/ember/workbox/persvati-lean-20261003/guardian.sh "$seat" "$lane" "$body"
