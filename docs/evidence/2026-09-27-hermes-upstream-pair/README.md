# Distinct upstream Hermes roots for hosted A/B review

The hbox roots are:

| Peer | Runtime root | Scoped launcher |
| --- | --- | --- |
| A | `/tank/dregg-preview/hermes-upstream-a-r1/runtime-root` | `/tank/dregg-preview/hermes-upstream-a-r1/launcher/bwrap` |
| B | `/tank/dregg-preview/hermes-upstream-b-r1/runtime-root` | `/tank/dregg-preview/hermes-upstream-b-r1/launcher/bwrap` |

They are distinct private directories, created sequentially from the
[qualified r2 source/venv root](../2026-09-27-hermes-upstream-hbox-r2/README.md).
Each initial copy passed a full `rsync -a --checksum --delete --dry-run`
comparison to r2 with an empty diff. `grain-runtime` was then replaced
atomically in each with the source-qualified Mini `cb55b81` Linux release
binary. Each final root differs from r2 **only** at `grain-runtime` (plus
its parent directory timestamp); the retained
[checksum diff](rsync-cb55-diff.log) SHA-256 is
`4a1ee32ee7a73560858430c3219e3691ce8acb0533c9102a57c84ddd5cb58bf3`.
A full checksum tree comparison of A against B was empty; the retained
[empty result](rsync-a-b-check.log) is SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
These checks compared file contents and metadata, omitting directory
timestamps on the final post-replacement comparison.

The pinned members in **both** roots are:

| Member | SHA-256 |
| --- | --- |
| upstream `pyproject.toml` | `eb0b8daac75c0c0e655282a1a836cb4c8a0bdc266e435a4d77e3295544ccf488` |
| upstream `uv.lock` | `811a21647251a3fd024a3e2f49c90ac0600c678e500cc08ed51db38c452a6c65` |
| `/agent/hermes-acp` wrapper | `d9b2b31dcce207f8397a7e1606a6d8586a25e661744b610340d83b2c0c25b7ee` |
| `/agent/grain-runtime` (`cb55b81`) | `7cb370ec7292004842c4680b77736cee9bda408665085b09f75b61c04036e40c` |
| `/agent/grain-provider-bridge` | `2877ef2a5293ee0b2a7c22d0c0216dab865d3174dd68b312889661cb4f90cfcb` |
| launcher `bwrap` | `efda87a5033fc24bb074cc68bfcca8686a448cd4e10175ca8d74b2c6884961a7` |
| sibling `launch-gate` | `2cf1d29ad7fcbce8e2e476ce803bc0c77785f720ceca02ba77e2530b849e7fb6` |

The retained [runtime pin](runtime-pin-cb55.txt) SHA-256 is
`c9ea0a76f9fe93c999788b3e46310def260b03a21dc44519a929b028f699a7d6`.
The builder attests the `cb55b81` source archive SHA-256
`2e59a86c1780b49897cdcb631b1cf518a58b4df87aa9b35101ca216261805927`,
37-file source manifest SHA-256
`86bbfbfd545b8a90ac5f8db6bd2bf9fa01aa741211b9ea633ff840a575cd4c61`,
and an offline locked release build with 37/37 source readback. The r2 root
and its earlier `18166e5` evidence were not changed.

A bounded **no-network** probe on each root passed real upstream
`hermes-acp --check` and ACP protocol-v1 `initialize` with setup-only
authentication. [Peer A log](probe-a.log) SHA-256 is
`cae036ba9a20d2f9b839314afc835c6fd935884169bef1f74feb25d43824583a`;
[peer B log](probe-b.log) SHA-256 is
`7da2f2b785b31ad38f13bc9881c2a897c73ad84610c00bf76f8b0c169613396d`.
All six transient controller/worker units were `not-found/inactive` after
probe cleanup. No provider socket, Mini MCP, model prompt, paid request, or
Store mutation was involved. These are the runtime-root and launcher pins
for reviewable A/B controller configs; actual provider/app authority and
per-peer workspaces remain to be qualified.
