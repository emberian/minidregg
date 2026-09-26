# MCP delivery deadline after native publication — 2026-09-26

The corrected Mac synthetic ACP acceptance **failed its final MCP response assertion**. The Mini host nevertheless confirmed the exact joint tool settle, parent generation-3 no-op witness, and object 7003 scalar publication in operation 61. `confirmed-publication.json` is a selected field copy of that retained native outcome. `mcp-results.json` shows that the MCP client received `controller did not settle the tool call` for both `mini_publish` and the subsequent `mini_read_resource`; there is no signed post-publication readback in this run. This is a deadline/reporting failure, not a native refusal and not a full acceptance PASS.

The MCP publication request was written at 06:33:37 local time. The broker's internal `reply_rx.recv_timeout(300s)` expired around 06:38:37. Native tool reserve was confirmed at 06:39:34; the joint source was written at 06:40:24; its native outcome was confirmed at 06:43:15. The second MCP read then timed out around 06:43:37. The complete original evidence remains at `/tmp/mga-joint-055601` on the Mac for replay and runtime diagnosis. This fixture uses a deterministic ACP protocol peer, not upstream Hermes or a model call.

| Artifact | SHA-256 |
| --- | --- |
| Frozen acceptance script | `28d8c8cc734c8efd4a4a320c88bd9742f6d82931958409fb265a5cc81afa74ae` |
| Frozen runtime binary (`grain-runtime-joint-fix-20260926`) | `675f48d960bb691219d800ebdd2bd3db810c62a91245b43d87e67003cbb6e2c5` |
| Runtime source `main.rs` at this image | `b4a2449ff1b6469e5c453af6508c66f3a7095d89f90bda3f8108beb3e6230e1a` |
| Mac Mini host (`minidregg-host-final-b-fast`) | `c2a1fd3699338f28eaf1d076b53cbd1bf27b4438b857b0482666205b334a394c` |
| Retained operation-61 `call.bin` | `7d5595f61fd6a40ec11a1a0d36ded5a04013e3c69a0193f7a7fd9600b6af7891` |
| Retained operation-61 `outcome.json` | `45f43a9984a5d0aa3093ec0c8316823b14916ba1627b5641602b075489a20729` |
| Pinned Mini config | `26a882dc82f25221cee9c9463ecbadcaa42e47b224be294a0acf00115c12d640` |
| Retained MCP response stream | `d9e7d75a96bae44402b4d32eca98f393ac15ea799c96befce77be40f7cc55cc5` |

The accepted call is `/tmp/mga-joint-055601/runtime-state/attempt-0000000000000061/call.bin`; the exact pinned config is `/tmp/mga-joint-055601/deployment/pinned-config.json`. Neither binary call nor private deployment state is copied here.
