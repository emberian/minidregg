# Sourced by the run-*.sh scripts. Absolute paths; every binary is pinned by sha256 in the run logs.
# Defaults describe the W15 burst lane on burst-gate (host A); override with W15_* for another lane.
L=${W15_LANE:-/srv/lanes/W15-TRAFFIC-V13}
RC=$L/src/native/resource-client
ART=${W15_ART:-$L/art/bin}
HOST=$ART/minidregg-host
STORE=$ART/minidregg-link-sqlite-store
VERIFIER=$ART/minidregg-credential-signature-verifier
MINI_BASELINE=$L/artifacts/mini-baseline     # c8fdd000 (pre-shared-key link adapter)
MINI_NEW=$L/artifacts/mini-mce3-r2  # this tree: roster enrollment + hybrid KEM + read_layer_keys fix
WORLD=$L/world
LOOKUP=$L/fixtures/lookup
EFFECT=$L/fixtures/new-effect
SOCKET=$WORLD/public/mini.sock
# Host B: an ssh alias that resolves to its own key (the run key under $L/runkey, deleted after the run).
REMOTE=${W15_REMOTE:-w15b}
REMOTE_IP=${W15_REMOTE_IP:-162.43.189.7}
LAN_IP=${W15_LAN_IP:-67.213.124.13}
REMOTE_BASE=${W15_REMOTE_BASE:-/srv/lanes/W15-TRAFFIC-V13/remote}
