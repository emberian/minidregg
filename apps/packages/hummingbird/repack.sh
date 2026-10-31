#!/usr/bin/env bash
# repack.sh: Hummingbird 0.4.1 from the market package, repackaged under our key with bridgeConfig.apiPath = "/".
#
# The market package (package 9365130605f1998f3d4aea205d8768ae, app 4mfserfc04wtcevvgn0jw27hvwfntmt8j468y3ma55kj8d5tj9kh)
# sets apiPath "/tracking_pixel/", so an `api` route reaches only the tracking pixel; the declaration's socket.io
# conversation needs "/". Upstream (mnutt/hummingbird) carries no Sandstorm packaging, so the recipe rebuilds the
# package definition from the published package: unpack, decode its manifest and bridge config, drop the author's PGP
# signature and keyring (they sign the old app id), set apiPath "/", and `spk pack` the unpacked tree under a new key.
#
# Needs: the Sandstorm 308 `spk` tool (dregg-forge: /var/lib/spk-fresh/tools/spk), capnp (decode), the sandstorm
# schemas (sandstorm-308/usr/include/sandstorm), python3. KEYRING is the new app's key (never in the repository).
# Result on dregg-forge /srv/spk-build/hummingbird/out/hummingbird-0.4.1-api.spk: app
# 434g078hse54h0tt189hsyp2stf7n7rap8uxwjf3dyq2zvymrx0h, package c7287dfbae2796cd283a32452d2395c7.
set -euo pipefail
SPK=${SPK:-/var/lib/spk-fresh/tools/spk}
INCLUDE=${INCLUDE:-/var/lib/spk-fresh/tools/sandstorm-308/usr/include}
W=${W:?W=/work/dir}; KEYRING=${KEYRING:?KEYRING=path to the new app key}
APPID=${APPID:?APPID=the new app id (spk keygen)}
MARKET=https://app-index.sandstorm.io/packages/9365130605f1998f3d4aea205d8768ae
mkdir -p "$W/downloads" "$W/out"
[ -f "$W/downloads/hb.spk" ] || curl -fsSL -o "$W/downloads/hb.spk" "$MARKET"
[ "$(sha256sum "$W/downloads/hb.spk" | cut -c1-32)" = 9365130605f1998f3d4aea205d8768ae ]
rm -rf "$W/unpacked"; "$SPK" unpack "$W/downloads/hb.spk" "$W/unpacked" >/dev/null
# the generated files come from the package definition, not from the tree
mkdir -p "$W/orig-meta"; mv "$W/unpacked/sandstorm-manifest" "$W/unpacked/sandstorm-http-bridge-config" "$W/orig-meta/"
capnp decode -I "$INCLUDE" "$INCLUDE/sandstorm/package.capnp" Manifest < "$W/orig-meta/sandstorm-manifest" > "$W/manifest.txt"
capnp decode -I "$INCLUDE" "$INCLUDE/sandstorm/package.capnp" BridgeConfig < "$W/orig-meta/sandstorm-http-bridge-config" > "$W/bridge.txt"
python3 - "$W" "$APPID" <<'PY'
import re, sys
w, appid = sys.argv[1], sys.argv[2]
man = open(w + '/manifest.txt').read().rstrip()
cfg = open(w + '/bridge.txt').read().rstrip()
# drop the author's signature (it signs the old app id) and the keyring that verifies it
man, n = re.subn(r'\n\s*pgpSignature = "(?:[^"\\]|\\.)*"\s*\),?\n', '\n      upstreamAuthor = "Michael Nutt" ),\n', man, count=1); assert n == 1
man, n = re.subn(r'\n\s*pgpKeyring = "(?:[^"\\]|\\.)*",', '', man, count=1); assert n == 1
cfg, n = re.subn(r'apiPath = "[^"]*"', 'apiPath = "/"', cfg); assert n == 1
open(w + '/sandstorm-pkgdef.capnp', 'w').write('''@0xb8e1c6a47f1d3e55;

using Spk = import "/sandstorm/package.capnp";

const pkgdef :Spk.PackageDefinition = (
  id = "%s",
  manifest = %s,
  sourceMap = (searchPath = [ ( sourcePath = "unpacked" ) ]),
  alwaysInclude = [ "bin", "dev", "etc", "lib", "lib64", "opt", "proc", "tmp", "usr", "var",
    "sandstorm-http-bridge", "sandstorm-manifest", "sandstorm-http-bridge-config" ],
  bridgeConfig = %s,
);
''' % (appid, man, cfg))
PY
cd "$W" && "$SPK" pack -k"$KEYRING" out/hummingbird-0.4.1-api.spk
"$SPK" verify --details out/hummingbird-0.4.1-api.spk | tee out/verify.txt
sha256sum out/hummingbird-0.4.1-api.spk | tee out/sha256.txt
