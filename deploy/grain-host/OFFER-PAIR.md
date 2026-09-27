# Offer a fresh hosted Hermes pair

This is the operator sequence for **one new Mini Store** with the fixed workroom profile: parent/tool grains 7801/7802 and 7803/7804, shared content 8001, four signing subjects, and two separate Unix task accounts. It composes the existing signed [hosted provisioner](../../scripts/workroom/hosted-provision.sh), the per-UID Mini host frontend, [controller installer](install-controller), gated `bwrap`/Hermes runtime, and a separate operator fn bridge. The existing [single-account hosted pair](HOSTED-PAIR.md) proved two controllers and physical workers; it is not an account-isolation installation recipe. Never point this procedure at that live Store or reuse its task accounts.

The four `offer-*` commands in this directory have deliberately narrow jobs. `offer-check-provision` decodes retained canonical Mini outcomes and views with the pinned Lean Host and checks exact build, source, resource, and grant pins. Its verdict says `currentAuthorityVerified:false`. `offer-render-task` runs as one task account and stages **one** config, executable pin list, and `install-controller --render-only` unit. Its `stage.json` hashes the input manifest and all rendered outputs; rerunning verifies exact bytes, while an incomplete stage refuses inspection-free overwrite. `offer-check-authority` uses that account's frontend and custody keys to make **fresh signed Mini queries** before unit installation. `offer-check-pair` compares those two account handoffs before either controller is installed. A successful query does not authorize a future publication if a grant is revoked or the target root changes; the actual MCP write remains a native admission at use time.

All path-bearing manifests are owned mode 0600 files with absolute canonical paths. Output, state, workspace, and controller working directories are new, private 0700 directories. Put them under each task account's home or a reviewed private service root. Use disjoint task UIDs, private keys, state, workspaces and runtime roots. Keep the operator's Mini Store, host socket, operator keys, and fn bridge outside both worker mounts. The worker runtime roots must have a distinct operator owner and mode 0755; the launcher mounts them read-only. Directory mode alone does not make bytes immutable to their owner, so recheck pins at each restart and protect the operator account. Record exact source and executable SHA-256 values in the offer manifests; a pin is an operator-selected byte identity, while the separately retained Host build manifest carries its source qualification.

First, qualify a Linux Mini Host, `mini`, Store helper, signature helper, `grain-runtime`, `bwrap`, `launch-gate`, upstream `hermes-acp`, and a per-UID `host-frontend` image against their exact source/build evidence. Check the frontend's final accepted source hash and signed two-UID gate before deploying it; an unqualified WIP binary is not an entrance. Stage two nonsecret Hermes runtime roots with `hermes-acp` and byte-identical `grain-runtime` MCP client executables. Stage separate workspaces containing private `.hermes/config.yaml` with `timeouts.mcp.tool_call` below the command's bounded `wallTimeSeconds`. Use distinct loopback fixture endpoints for the first smoke. A paid or BYO provider requires its own signed provider task, custody, budget and gateway acceptance; a fixture endpoint is not a substitute.

Run the native provisioner **once** against a new evidence directory and Store, with exact qualified artifact paths:

```sh
MINI=/ABS/mini STORE_BINARY=/ABS/minidregg-link-sqlite-store \
SIGNATURE_BINARY=/ABS/minidregg-credential-signature-verifier \
  scripts/workroom/hosted-provision.sh /ABS/minidregg-host /ABS/new-provision
```

Do not rerun birth or delegation merely because a shell stopped or a response was lost. Inspect the retained attempt and use the native client's exact lookup/recovery path before deciding what was accepted. Keep the complete private provision; its four custody keys and Store never go into the public evidence archive. A new Store avoids collision with other uses of the fixed 780x task IDs.

Create an operator-owned 0600 offer manifest and run the read-only snapshot check. This schema is literal; fill each SHA from the selected artifact or source, not from a path name:

```json
{
  "profile":"mini-hosted-workroom-780x-v1",
  "fn":{"mode":"deferred"},
  "provision":"/ABS/new-provision",
  "sourceRoot":"/ABS/staged-reviewed-source-root",
  "hostBuildManifest":"/ABS/qualified-host-build/manifest.txt",
  "hostBuildManifestSha256":"64-lowercase-hex",
  "hostSha256":"64-lowercase-hex",
  "miniSha256":"64-lowercase-hex",
  "storeSha256":"64-lowercase-hex",
  "signatureSha256":"64-lowercase-hex",
  "pinnedConfigSha256":"64-lowercase-hex",
  "baseASha256":"64-lowercase-hex",
  "baseBSha256":"64-lowercase-hex",
  "hostedProvisionSourceSha256":"64-lowercase-hex",
  "baseProvisionSourceSha256":"64-lowercase-hex"
}
```

```sh
deploy/grain-host/offer-check-provision /ABS/operator-private/offer.json \
  > /ABS/operator-private/provision-check.json
```

The `sourceRoot` contains exact staged copies of `scripts/workroom/hosted-provision.sh` and `scripts/workroom/provision.sh`; the check pins both before reading the provision. The check requires all nine retained installed outcome products in order, four born-grain views, current source-authored profile files, and both base configs. It asks the pinned Host to decode each retained `outcome.bin` and `view.bin` and compares that canonical projection with the saved JSON. This establishes consistency of the **retained snapshot**, not a fresh authority decision, cryptographic verification of a copied observation, or exact call/receipt binding. Retain original signed observations and accepted calls privately. Resolve any uncertain attempt through native exact lookup. The later live signed queries and MCP smoke are independent gates.

Start one **operator-owned** persistent native Mini host at its private 0700 socket using the provision's pinned config. The operator starts two instances of the qualified frontend, each with its own dedicated operator-owned directory and public host-config copy. The frontend CLI is:

```text
host-frontend PRIVATE_HOST_SOCKET PUBLIC_TASK_SOCKET PUBLIC_CONFIG TASK_UID HOST_SHA256
```

The private host socket and its `.config` stay operator-owned mode 0600. The two public configs must be byte-identical to that private host config and pinned by the operator. The frontend grants only one chosen task UID directory traverse, config read and socket connect, verifies Linux peer credentials plus the exact pinned v2 envelope, and relays without retry. It denies fn operator operations. Keep a separate operator service/manifest for each frontend; confirm each listener's systemd unit, MainPID, socket owner and task-UID ACL before giving the socket to a controller. A copied config or ACL is **not** authorization; Mini signs and checks the resulting query or command.

Transfer only A's controller/tool custody bytes to task account A and only B's bytes to account B, under private paths. The task manifests pin those bytes by SHA-256. Each account stages a reviewed 0600 task manifest (fields below) using its own copied native base config, same pinned Host and Mini binaries, its frontend's public config/socket, and its own paths. Use `"peer":"a"` for 7801/7802, `"peer":"b"` for 7803/7804. The base config SHA must equal the operator's `baseASha256` or `baseBSha256` above. `frontConfigSha256` must equal `pinnedConfigSha256`; the frontend itself compares the complete bytes with the private host pin.

```json
{
  "profile":"mini-offer-task-v1", "peer":"a",
  "baseConfig":"/ABS/task-a/base.json", "baseConfigSha256":"64-lowercase-hex",
  "frontConfig":"/ABS/operator-front-a/host.config", "frontConfigSha256":"64-lowercase-hex",
  "provisionConfigSha256":"64-lowercase-hex",
  "frontSocket":"/ABS/operator-front-a/host.sock",
  "mini":"/ABS/mini", "miniSha256":"64-lowercase-hex",
  "host":"/ABS/minidregg-host", "hostSha256":"64-lowercase-hex",
  "runtime":"/ABS/grain-runtime", "runtimeSha256":"64-lowercase-hex",
  "launcher":"/ABS/bwrap", "launcherSha256":"64-lowercase-hex",
  "gateSha256":"64-lowercase-hex", "hermesSha256":"64-lowercase-hex",
  "rendererSourceSha256":"64-lowercase-hex",
  "installerSourceSha256":"64-lowercase-hex",
  "unitDir":"/ABS/task-a/.config/systemd/user",
  "outputDir":"/ABS/task-a/render-new", "stateDir":"/ABS/task-a/state-new",
  "cwd":"/ABS/task-a/controller-cwd", "workspace":"/ABS/task-a/workspace",
  "runtimeRoot":"/opt/mini-offer/runtime-a",
  "controllerKey":"/ABS/task-a/controller.key", "controllerKeySha256":"64-lowercase-hex",
  "toolKey":"/ABS/task-a/tool.key", "toolKeySha256":"64-lowercase-hex",
  "wallTimeSeconds":1500, "reserve":"3", "charge":"1"
}
```

As **each task account**, with its `systemd --user` manager available, run:

```sh
deploy/grain-host/offer-render-task /ABS/task-a/offer-task.json
deploy/grain-host/offer-check-authority /ABS/task-a/offer-task.json /ABS/task-a/new-signed-readback
systemd-analyze --user verify /ABS/task-a/render-new/rendered.service
```

Repeat with B's distinct paths and signer. Do not install if either fresh readback fails. The readback checks both fresh unheld grains, worker witness observation, empty shared content, and exact generation-1 parent policy. It retains signed observation bytes and a `friendReady:false` verdict. Check both stage manifests again immediately before installation. The installer refuses active/conflicting units, wrong executable bytes, exposed custody or journal/task mismatch. It only installs; it does not start the controller. A partial render directory without `stage.json` is intentionally blocked—inspect it and select a fresh output directory rather than rerunning a half-written stage.

Before either installation, the operator checks the two private manifests and retained signed readbacks together. Run with read access to both task homes; this command does not use either custody key or write to the Store:

```sh
deploy/grain-host/offer-check-pair \
  /ABS/operator-private/offer.json \
  /ABS/task-a/offer-task.json /ABS/task-b/offer-task.json \
  /ABS/task-a/new-signed-readback /ABS/task-b/new-signed-readback \
  > /ABS/operator-private/pair-handoff.json
```

It requires distinct non-root manifest owners, nonoverlapping mounts/state/keys/frontends, matching Host/Mini/runtime pins, exact rendered-stage hashes, and one shared content root in the two signed readback snapshots. `pair-handoff.json` still says `friendReady:false`; it is a deployment preflight, not future native authorization. Recheck if either account or artifact changes.

Then, as each task account, install its reviewed unit with the existing installer:

```sh
deploy/grain-host/install-controller \
  --config /ABS/task-a/render-new/runtime-config.json \
  --runtime /ABS/grain-runtime --pins /ABS/task-a/render-new/pins.json \
  --unit-dir /ABS/task-a/.config/systemd/user
```

Use B's rendered paths in B's account. Retain the rendered and installed unit hashes and `systemctl --user show` `FragmentPath` in the operator evidence.

Start the shared native Host service first, then explicitly start `mini-grain-controller@7801.service` in A's user manager and `@7803.service` in B's. Check exact `FragmentPath`, active MainPID, private control socket, journal binding, no pending/hold/uncertain external effect, and the frontend unit/socket for that UID. A controller file on disk alone is not a running or authorized grain. Before an external key is offered, drive one bounded actual Hermes ACP prompt per account through its controller and fixed loopback provider fixture. Require a scoped `mini-grain-t<TASK>-o<OP>.service` bound to that controller, an accepted native publication call on content 8001, independently signed readback by the correct worker, and a fenced/empty worker cgroup after completion. For the second peer, reread the current shared root before writing and retain a corrected publication against it. Do not label an uncertain tool hold or lost broker response as a successful publication. The fresh [two-account A→B→A sequence](../../docs/evidence/2026-09-26-cross-uid-hermes/README.md) records that complete native path; the earlier [single-account hosted pair run](../../docs/evidence/2026-09-26-hosted-pair-linux/README.md) has a separate unresolved B stale-target limit.

The fn bridge remains an **operator stage**, outside either frontend and worker. When a current native Host profile and a qualified fn image are explicitly matched, use [render-operator-bridge.sh](../../scripts/fn-e1e2/render-operator-bridge.sh) to pin the remote fn executable closure. Export the specific accepted Mini call, independently verify its package, and render a strict provenance article with [render-grain-origin-r.lean](../../scripts/fn-e1e2/render-grain-origin-r.lean) before a reviewed operator posting path. Retain the fn Store acceptance and B readback separately. The current historical `run-grain-r.sh` uses a two-store harness; it is not an automatic persistent feed for arbitrary friend prompts. Until that exact Mini/fn profile and path pass, keep `fn.mode` deferred and make no fn delivery claim.

After the controller is active and its private socket is live, use [offer-render-entry](offer-render-entry) **as that task account** to bind a reviewed `grain-ssh` wrapper and [render-friend-key](render-friend-key) to the exact task manifest, rendered stage, installed unit, runtime pin and chosen public key. Its six arguments are `ABS_TASK_MANIFEST ABS_GRAIN_SSH GRAIN_SSH_SHA256 RENDER_FRIEND_KEY_SHA256 hard|soft FRIEND_PUBKEY`; it prints one `restrict,command=` line for review and does not install it. Hard is the normal entry; render a distinct soft-key line only for an explicit background-continuation choice. Once installed by the operator in that account's `authorized_keys`, the friend connects with `ssh -T TASK_ACCOUNT@HOST`, waits for `attached ...`, and enters `hermes PROMPT`, `status`, `conversation new`, or `disconnect` as lines. The current connector streams ACP text and prints the full controller journal for `status`; it has no shell prompt or line-editing UI. A lost hard SSH connection physically stops the owned worker and fences its Mini generation. An uncertain hard interruption may require operator reconciliation before another attachment. A soft loss leaves the bounded worker running, and a later connection reattaches to the same controller and retained Hermes session when its signed state permits.

```sh
offer-render-entry /ABS/task-a/offer-task.json /ABS/operator-bin/grain-ssh \
  GRAIN_SSH_SHA256 RENDER_FRIEND_KEY_SHA256 hard /ABS/reviewed-friend.pub \
  > /ABS/operator-private/reviewed-authorized-key-line
```

This recipe does not create accounts, modify `authorized_keys`, enable linger, or publish an internet listener. The owner must decide those deployment actions separately. On restart, recheck the artifact and stage manifest hashes, frontend identity, live signed Mini state, and controller journal; never infer authority or settlement from an installed file. If any native call's response is uncertain, keep the original attempt and resolve it by exact lookup before issuing a new command.
