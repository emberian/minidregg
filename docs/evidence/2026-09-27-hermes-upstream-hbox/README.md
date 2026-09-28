# Upstream Hermes ACP staged on hbox, 2026-09-27

The new private tree is `/tank/dregg-preview/hermes-upstream-r1` on hbox
(owner `hbox`, root and runtime-root mode 0700). No earlier Hermes installation
was found in the scoped `/tank` and home inventory. The upstream source is a
**clean `git archive`** of the tracked tree at local Nous Hermes Agent commit
`6d8a8bebf70b09554deda5a0fcd95facbbde7b07`; the local checkout's
untracked `build/` was excluded. The copied `pyproject.toml` is SHA-256
`eb0b8daac75c0c0e655282a1a836cb4c8a0bdc266e435a4d77e3295544ccf488`
and `uv.lock` is SHA-256
`811a21647251a3fd024a3e2f49c90ac0600c678e500cc08ed51db38c452a6c65`.
They match the earlier [real ACP probe](../../../deploy/grain-host/HERMES-LINUX-2026-09-26.md)
on persvati. No Hermes source was modified.

The official uv 0.12.17 Linux release archive was downloaded only into the
private `tool/` directory and verified against its release `.sha256` file.
Archive SHA-256: `fa82fd8dde8e8eefdecada6aa0889666556cfceb690d06e0c3bca49eb3070a63`;
extracted uv SHA-256:
`553a67a24d306a803d5c45678b7c54ed0c8b698d9fe3835d54905811348ccf2a`.
The capped `mini-hermes-uv-r1.service` used Python 3.12.7 and
`uv sync --locked --no-dev --extra acp --python /usr/bin/python3 --no-python-downloads`
with `UV_PROJECT_ENVIRONMENT` inside `runtime-root/venv`, a private uv cache,
and two concurrent downloads/builds/installs. It resolved 259 and installed
65 locked packages; the unit ended successfully. `uv-sync.log` SHA-256 is
`6fa462eaf5bb18762d32a41278673149097d1ee0cd7aa6c4c0591e20d5db836e`.
The resulting 65-entry private `venv-freeze.txt` is SHA-256
`55b2c8d5ba3c199cb81bc98b5eac557e0e5a323da8ed35b7eee15deee0610412`.
No global Python packages or `~/.hermes` state were changed.

The `/agent/hermes-acp` wrapper is byte-identical to the previously reviewed
entry (SHA-256 `d9b2b31dcce207f8397a7e1606a6d8586a25e661744b610340d83b2c0c25b7ee`).
It runs `python -m acp_adapter.entry` from the upstream source and private
venv with `HERMES_HOME=/workspace/.hermes`, private XDG paths,
`HERMES_ACP_SKIP_CONFIGURED_MCP=1`, and `HERMES_DISABLE_LAZY_INSTALLS=1`.
`--check` returned `Hermes ACP check OK`. A direct stdio `initialize` using
Python pipes returned ACP protocol v1 with setup-only authentication and no
prompt. Its raw response is private at `direct-initialize.jsonl`, SHA-256
`392dfb1d9d5f480aa75e63690860c89a47748fb42d1cad11017ce0b45d93f304`.
The direct probe did **not** exercise the Mini sandbox, provider, MCP, or a
model.

The copied Mini launcher SHA-256 is
`05010aaa0977c55a1dc1feaf54f622f8473f4dda21817149e5ac90714bd17f1c`;
its locally compiled `launch-gate` SHA-256 is
`2cf1d29ad7fcbce8e2e476ce803bc0c77785f720ceca02ba77e2530b849e7fb6`.
The older keyless `grain-runtime` SHA-256
`4c72772d506b3b96f3fe5b269f607a08b63705bd4536c777b66c33deb335b02e`
is present **only for an ACP initialization component probe**. It is not the
current v3 MCP/provider build. The no-network user-unit probe failed before
Hermes ran: `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted`.
Direct `unshare -Urn` also failed writing `uid_map`, while hbox reports
`kernel.apparmor_restrict_unprivileged_userns=1`; this is consistent with a
host namespace policy restriction. Probe controller/worker units stopped and
the retained debug scratch containing only a dummy `test-only-key` was
removed. The failed first probe log SHA-256 is
`0f69ebbf5e91e5cdbd35140e978bcdd018b207c0e34a2039a47f6fa2e76cd24f`.
No host-network substitute, global sysctl change, credential copy, MCP call,
or provider/model request was made.

The hbox bubblewrap package is 0.10.0-1, and `/usr/bin/bwrap` is root-owned
SHA-256 `cccc95aebe85694cf34ca7e359308c019da692740f5bb909c3401363b06d9413`.
It has no package AppArmor profile. The distro fallback
`/etc/apparmor.d/unprivileged_userns` denies capabilities, while its existing
`crun` and `slirp4netns` profiles use a `flags=(unconfined)` profile with a
`userns,` rule. A [candidate dedicated profile](mini-grain-bwrap.apparmor)
(SHA-256 `d9162a29ac987a26ab3548e2c63dadfa1f9eb1f2f58d027202dc67cd02336bdf`)
passed `apparmor_parser -Q -T`. It attaches only to a proposed root-owned,
`root:hbox` mode-0750 copy at `/usr/local/libexec/mini-grain-bwrap`.
The private test launcher differs from the reviewed launcher in one executable
path at `sandbox=(...)`; `bash -n` passed and its SHA-256 is
`efda87a5033fc24bb074cc68bfcca8686a448cd4e10175ca8d74b2c6884961a7`.
After source review, the exact distro ELF was copied to that dedicated path
as `root:hbox` mode 0750, the profile was installed root-owned at
`/etc/apparmor.d/mini-grain-bwrap` without replacing an existing profile,
and `apparmor_parser -a -T` loaded it. The root-owned binary and profile
hashes equal the values above. `/usr`, `/usr/local`, and
`/usr/local/libexec` are root-owned and mode 0755. The global
`kernel.apparmor_restrict_unprivileged_userns` remained `1`, and the generic
`/usr/bin/bwrap` still refuses the same user+network namespace operation;
its refusal log SHA-256 is
`ed3471f7900377f86150471417911309833a36d664cb5af7409e139103f67ddf`.

The dedicated ELF then created a fresh net namespace distinct from the host
namespace. It exposed only `lo` with `127.0.0.1`/`::1`, and `ip route get
1.1.1.1` returned `Network is unreachable` without sending traffic. The
keyless [namespace proof](namespace-proof.log) is retained here and under the
hbox root, SHA-256
`2b4e5e7947b3ce0377e889c34e78bbb9e569dc962454a44b02ba91c67060eea5`.
Using the one-line private launcher variant with the original bounded probe,
the real upstream `hermes-acp --check` passed in a no-network systemd user
worker; ACP `initialize` returned protocol v1/setup-only authentication in a
second no-network worker; both workers and the dummy controller stopped.
The keyless [successful probe log](probe-profile.log) is retained here and
under the hbox root, SHA-256
`3ce19739d609931b86e4b4cc55cfb8871e9ee8ef7de379dfd252eb564a0f135a`.
The second worker reported about 55 MiB peak memory. No provider bridge was
mounted and no prompt, MCP tool, provider, or model call occurred. This is a
real confined upstream ACP startup, not the integrated Mini/provider journey.

For the integrated worker, compose a separately pinned runtime root with the
current source-qualified `/agent/grain-runtime` and
`/agent/grain-provider-bridge`, then requalify the no-network worker with
those exact binaries. Preserve this r1 root as the
upstream-source and no-provider startup baseline. The controller's generated
custom Bonsai profile and actual Mini MCP journey need that worker boundary
and their own acceptance evidence.
