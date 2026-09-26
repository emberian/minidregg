#!/bin/sh
set -euC
umask 077

root=${1:?private fixture root required}
name=${2:?base or positive required}
# The fixture emits these paths into a shell hook; reject shell syntax rather
# than letting a path become executable source.
case "$root" in /*) ;; *) echo 'fixture root must be absolute' >&2; exit 2 ;; esac
case "$root" in *[!a-zA-Z0-9_./-]*) echo 'fixture root contains unsupported characters' >&2; exit 2 ;; esac
case "$name" in
  base) upstream=18863; gateway=18864 ;;
  positive) upstream=18873; gateway=18874 ;;
  *) exit 2 ;;
esac
e=$root/$name
test -d "$e"
mkdir -m 700 "$e/runtime-state" "$e/worker-work"
printf 'local-fixture-key\n' > "$e/runtime-state/upstream-local-fixture.key"

host=/home/ember/build/minidregg-overnight-20260926/evidence/minidregg-host-final-combined
mini=/home/ember/build/minidregg-overnight-20260926/client-f089a71/native/resource-client/target/debug/mini
jq -n \
  --arg root "$root" --arg e "$e" --arg host "$host" \
  --arg upstream "http://127.0.0.1:$upstream/v1/chat/completions" \
  --arg gateway "127.0.0.1:$gateway" \
  '{mini:($e+"/mini-hook"),host:$host,
    hostConfig:($e+"/deployment/continuity-config.json"),
    hostSocket:($e+"/integrated-session/host.sock"),
    controlSocket:($e+"/runtime-state/control.sock"),
    custodyKey:($e+"/controller.key"),stateDir:($e+"/runtime-state"),cwd:$e,
    task:"7901",subject:"7",capability:"71",queryCapability:"71",policyControlCapability:"72",
    toolTask:{task:"7902",subject:"8",capability:"81",queryCapability:"81",
      custodyKey:($e+"/tool.key"),parentCapability:"73",parentObserveCapability:"73",
      reserve:"2",charge:"1",
      allowedPublications:[{kind:"object",target:"7903",capability:"93",observeCapability:"93"}],
      allowedReads:[{name:"publication",kind:"object",target:"7903",observeCapability:"94",maxResultBytes:65536}]},
    providerTask:{task:"7904",subject:"9",capability:"101",queryCapability:"101",
      custodyKey:($e+"/provider.key"),parentCapability:"75",parentObserveCapability:"75",
      reserve:"3",charge:"1",model:"mini-hermes-protocol-fixture",upstreamUrl:$upstream,
      providerKeyFile:($e+"/runtime-state/upstream-local-fixture.key"),gatewayBind:$gateway,
      maxRequestBytes:1048576,maxResponseBytes:8388608,timeoutSeconds:600},
    commands:[{name:"hermes-acp",program:($root+"/deploy/grain-host/bwrap"),
      args:["--workspace",($e+"/worker-work"),"--runtime-root",($root+"/runtime-root"),
        "--network","host","--","/agent/hermes-acp"],
      systemdScope:true,wallTimeSeconds:1500,reserve:"3",charge:"1"}]}' \
  > "$e/runtime-config.json"

cat > "$e/mini-hook" <<EOF
#!/bin/sh
set -eu
if [ "\${1-}" = continuity ]; then
  : > "$e/hook.entered"
  i=0
  while [ ! -e "$e/hook.release" ]; do
    i=\$((i + 1))
    [ "\$i" -lt 900 ] || { echo "private continuity hook timed out" >&2; exit 73; }
    sleep 1
  done
fi
exec "$mini" "\$@"
EOF
chmod 500 "$e/mini-hook"
jq '.continuityProviderResourceId = 7904' \
  "$e/deployment/pinned-config.json" > "$e/deployment/continuity-config.json"
printf '%s\n' "$e/runtime-config.json"
