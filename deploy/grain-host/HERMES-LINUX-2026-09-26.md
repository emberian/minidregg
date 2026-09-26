# Upstream Hermes ACP on persvati, 2026-09-26

The actual Nous Research Hermes Agent 0.21.3 ACP entrypoint ran on persvati
inside the Mini grain-host `bwrap` launcher. The source came from the local
`/Users/ember/pug/hermes-agent` checkout whose `main` ref was
`6d8a8bebf70b09554deda5a0fcd95facbbde7b07`. The copied working-tree
snapshot is identified further by `pyproject.toml` SHA-256
`eb0b8daac75c0c0e655282a1a836cb4c8a0bdc266e435a4d77e3295544ccf488`
and `uv.lock` SHA-256
`811a21647251a3fd024a3e2f49c90ac0600c678e500cc08ed51db38c452a6c65`.
These hashes identify the copied files; the ref alone is not a clean-tree
assertion.

Source was copied to `/tmp/mini-hermes-linux.DPzxIW/source`, excluding
`.git`, `.venv`, `build`, tests, apps, evals and website assets. With Python
3.13.7 and `/snap/bin/uv`, the isolated command
`uv sync --locked --no-dev --extra acp --python /usr/bin/python3` installed
65 packages, including `agent-client-protocol==0.9.0`, into
`/tmp/mini-hermes-linux.DPzxIW/venv`. `UV_PROJECT_ENVIRONMENT` and
`UV_CACHE_DIR` pointed inside that scratch tree; downloads, builds and
installs were capped at two concurrent jobs. Nothing was installed in the
global environment or under `~/.hermes`.

The 251 MiB runtime root at `/tmp/mini-hermes-linux.DPzxIW/runtime-root`
contains the copied upstream source and venv, a keyless Linux
`grain-runtime` binary, and a small `/agent/hermes-acp` shell entrypoint.
That entrypoint runs `python -m acp_adapter.entry` with `PYTHONPATH=/agent/source`,
private workspace home/cache paths, configured MCP discovery skipped, and
`HERMES_DISABLE_LAZY_INSTALLS=1`. Its SHA-256 is
`d9b2b31dcce207f8397a7e1606a6d8586a25e661744b610340d83b2c0c25b7ee`.
The staged keyless runtime binary SHA-256 is
`4c72772d506b3b96f3fe5b269f607a08b63705bd4536c777b66c33deb335b02e`;
it is a component-probe build, not the final native acceptance image.

The repeatable `probe-hermes-acp.sh` uses a private scratch workspace and
transient user controller/worker units. It passes `--network none`, exposes
no controller key/config/state mounts, and makes no provider or model call.
It passed upstream `hermes-acp --check`; the real ACP `initialize` returned
protocol v1 and only `hermes-setup` authentication. The worker unit was
inactive after stopping the connector. The raw output is
`HERMES-LINUX-2026-09-26.log` (SHA-256
`6b27fa8b2d88b034f272b0954aa5e65d3b30c5f7886f8ad1572184b05ae44f23`);
the probe script SHA-256 is
`3d29d6049c86037f55fa109aa7402ae24778e29d17ea7d58a33a266731bc221b`.

No authenticated provider profile was present. This establishes a real
upstream Linux ACP initialization in the confined worker, not a model prompt,
native Mini authorization, MCP publication, or hosted service deployment.
