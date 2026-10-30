#!/bin/bash
set -euo pipefail
export HOME=/var
mkdir -p /var/store/last /var/store/rec /var/tmp
cd /opt/app
# safe to run every time
./ot-recorder --initialize
exec ./ot-recorder --http-port=8000 --norevgeo
