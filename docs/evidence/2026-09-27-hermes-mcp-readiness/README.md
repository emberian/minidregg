# cb55 Hermes MCP catalog and first-call readiness

This is a source/config inspection only. No controller, broker, model request,
GitWeb tool, or Mini Store mutation was run for this check. The real upstream
Hermes built-in-only first call was measured separately in the
[65,536-token Bonsai evidence](../2026-09-27-hermes-context-64k/README.md).

The exact committed `cb55b81` source files checked here match the current
working bytes:

| Source | SHA-256 |
| --- | --- |
| `native/grain-runtime/src/mcp.rs` | `d52cf36a6505140937b226933a50ed8856dda71f1841457419350da8fad18743` |
| `native/grain-runtime/src/main.rs` | `40a24ea5f2eb703985da5cd966db3121787d9862a605520fbc83043cce4b593c` |
| `native/grain-runtime/src/provider.rs` | `6e9708667c063765deac5d373af965c500b26713dcb6d4db07fa1681e3c2b622` |
| `native/grain-runtime/src/provider_profile.rs` | `0f76b323d601cf33bb67ec9c7b4ee62b6996ed51b5fce4e9ec8152a83ad49eb7` |

The hbox A and B 64k review configs are SHA-256
`836c5918735afdbe2d2e82b8b6bb598e1612196de1ac2da3262ec331470a89c1`
and `37c054f320d79527df36d53cea3ee719a87743858ffcb4eb7f85907edc802853`.
Their keyless [A](a-config-summary.json) and [B](b-config-summary.json)
projections are identical in the measured fields: model input 65,024,
output 512, two iterations, upstream `127.0.0.1:18081`, provider request
timeout 180 s, and Hermes worker wall 600 s. Each has zero birth/application/
session families, registered shared applications, API routes and lifetime
routes, with no app-API Host pins. `tool_catalog()` therefore produces the
default catalog; `mcp::tools_for_catalog` exposes only
`mini_grain_status`, `mini_read_resource`, and `mini_publish`. It does not
expose GitWeb or app API tools in either rendered config.

The source contains conditional definitions for resource/application/session
birth and for `mini_gitweb_read`, `mini_gitweb_edit`, and
`mini_application_api`. Their application selector enums come from confirmed,
operator-named routes, not a fabricated app name. The r3 app and five session
births are accepted, but INSTALL completion, tickets, START, enrollment and
usable dispatch routes remain unfinished. The rendered configs have no pins
from which a source-owned full GitWeb catalog can be produced. A
full-catalog first model request cannot be truthfully measured now without
inventing tools or changing Store authority. The necessary next gate is an
accepted app/session/ticket lineage plus separately pinned dispatch/lifetime
routes, followed by an exact `tools/list` capture and first model request
from the real broker. No provisional schema size is presented as that result.

The measured upstream built-in-only request used **8,947 prompt tokens** and
**140.74 s** on the local 65,536-token service; server prompt evaluation
alone took 138.55 s. This excludes even today's three Mini tools. An 180 s
provider timeout leaves only **39.26 s** after that baseline for MCP schemas,
generation, delivery and any larger prompt. The exact full-catalog duration
remains unknown. The cb55 source permits `providerTask.timeoutSeconds` up to
600 and a scoped command `wallTimeSeconds` up to 1,800. For the first
authorized full-catalog pilot, a **provisional** pair is 360 s per provider
request and 1,500 s outer Hermes worker wall. Upstream `max_iterations=2`
allows two normal API calls and its finalizer can make one extra toolless
summary request (`agent/turn_finalizer.py` SHA-256
`ec83f0b11d0bde2fb9d419cc33157d2e352f08575e62a50254a629a1cc271f5b`).
Three maximum-length provider waits would consume 1,080 s,
leaving 420 s for startup, MCP calls and response processing. This is a
bounded test budget, **not** a
claim that the full catalog succeeds within it; actual call/usage evidence
must determine the final pair. The current 180/600 review configs were not
edited by this lane.

The existing local 64k model unit remains the same invocation with its
original [03:16:33 UTC deadline](../2026-09-27-hermes-64k-deadline/README.md).
This check did not restart it or issue another model request.
