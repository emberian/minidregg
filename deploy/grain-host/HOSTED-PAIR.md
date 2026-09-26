# Deploy two hosted Mini grains on one content page

This recipe starts **after** a signed, source-qualified native provision such as `scripts/workroom/hosted-provision.sh`. That provision must create two separate parent/tool pairs, current parent witness grants, narrow named read and publication grants on one content page, and a pinned Mini host config. Keep its signed birth/delegation/readback artifacts. This deployment recipe neither creates Mini authority nor repairs a rejected or held grain.

Use an already-installed Linux `mini` client and Mini Host qualified against that provision, one fixed `grain-runtime` binary, and a reviewed `bwrap` launcher with its compiled sibling `launch-gate`. Stage two **separate** nonsecret Hermes runtime roots and writable workspaces. Each runtime root needs `/agent/hermes-acp` (the unmodified upstream ACP entry) and a byte-identical `/agent/grain-runtime` keyless MCP client. Put each worker's `.hermes/config.yaml` under its own workspace; for a local deterministic provider, set a different loopback `base_url` per peer and a bounded `timeouts.mcp.tool_call` below the command's `wallTimeSeconds`. No Mini custody key, controller JSON, state directory, or host config belongs under either worker mount. Production friend isolation additionally requires different Unix task accounts; separate paths under one account are only a test fixture.

Create a fresh owned mode-0700 output directory and an owned mode-0600 manifest. All paths are absolute, canonical and without spaces, `%`, quotes or backslashes. This example uses the currently exercised `hermes-acp` command with a 1500-second physical worker ceiling, a three-unit parent reserve, and one-unit charge; the native policy and allowance must admit those amounts:

```json
{
  "baseA":"/srv/mini/provision/runtime-config-a.base.json",
  "baseB":"/srv/mini/provision/runtime-config-b.base.json",
  "runtime":"/opt/mini/bin/grain-runtime",
  "launcher":"/opt/mini/bin/bwrap",
  "unitDir":"/home/task/.config/systemd/user",
  "outputDir":"/srv/mini/hosted-pair-render",
  "peerA":{"cwd":"/srv/mini/a/controller-cwd","workspace":"/srv/mini/a/workspace","runtimeRoot":"/opt/mini/a/agent"},
  "peerB":{"cwd":"/srv/mini/b/controller-cwd","workspace":"/srv/mini/b/workspace","runtimeRoot":"/opt/mini/b/agent"},
  "wallTimeSeconds":1500,"reserve":"3","charge":"1"
}
```

As the controller account, run `render-hosted-pair ABS_MANIFEST_JSON`. It copies the original base configs without changing them, writes private command-bearing overlays and executable SHA-256 pin manifests into `outputDir/peer-a` and `peer-b`, runs `check-hosted-pair`, then renders both direct systemd units through `install-controller --render-only`. It refuses an existing output and an active/conflicting controller unit. Review the emitted hashes against the native provision and build manifests, and run `systemd-analyze --user verify` on both rendered units. The pin manifest records operator-selected executable bytes **at render time**; it is not source or immutability proof.

Install the two reviewed units separately with `install-controller --config OUTPUT/peer-a/runtime-config.json --runtime RUNTIME --pins OUTPUT/peer-a/pins.json --unit-dir UNIT_DIR`, then the corresponding peer-b command. The installer checks owned mode-0600 final configs and custody keys, mode-0700 state, pinned executable bytes, the bwrap/gate protocol, and live systemd ownership. It neither starts nor enables a unit. `check-hosted-pair` adds cross-worker path checks; it cannot prove different key bytes or native content grants.

Start **one** private Mini host service using the provision's common `hostConfig` and `hostSocket`. The socket's parent must be owned mode 0700. For a bounded owner test, a transient user service is sufficient:

```sh
systemd-run --user --collect --unit=mini-hosted-shared-host \
  --property=KillMode=control-group --property=RuntimeMaxSec=21600s \
  --property=MemoryMax=8G --property=TasksMax=128 \
  MINI serve --host HOST --config HOST_CONFIG --socket HOST_SOCKET
```

Replace the uppercase operands with the exact pinned paths from the provision. Confirm the host socket is listening, then explicitly `systemctl --user start mini-grain-controller@PARENT_A.service` and `mini-grain-controller@PARENT_B.service`. Confirm each `FragmentPath`, active `MainPID`, private `control.sock`, and detached journal before attaching. Worker launches should produce distinct `mini-grain-t<PARENT>-o<OP>.service` cgroups, each `BindsTo=` its own controller; record the gate state and prove the cgroup empty after completion. No public SSH listener or friend key is created by this recipe. Owner access can use the existing account's SSH login and `grain-ssh` against one fixed socket; friend forced-key installation remains the separate [friend-grain procedure](FRIEND-GRAINS.md).

For the **deterministic peer fixture only**, run one source-matched `mini-hermes-test-provider` process per peer on distinct loopback ports, each with its own private log and `--content-peer-a` or `--content-peer-b` mode. The current fixture specifically expects content 8001 and tool grains 7802/7804; changing task IDs requires a new reviewed fixture. It makes no model call. A BYO or paid provider needs separate signed provider custody, credential and egress policy, plus a fresh acceptance; do not substitute a real key into this fixture profile. After the peer test, stop the two controllers, host and fixture services deliberately and preserve signed Mini views, ACP/MCP receipts, exact unit/cgroup evidence and source/binary hashes.
