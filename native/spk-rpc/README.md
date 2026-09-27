# Mini SPK RPC transport

This standalone crate speaks Sandstorm's actual two-party Cap'n Proto protocol
over the **already connected** supervisor end of an AF_UNIX socketpair. The
packaged application's `sandstorm-http-bridge` receives the other end on fd 3,
acts as the two-party client, exports `MainView`/`UiView`, and bootstraps the
supervisor's `SandstormApi`. `SupervisorConnection::from_connected_stream`
returns a typed view client and the RPC future; the owning application service
must drive that future on a Tokio `LocalSet` throughout the process lifetime.
There is no listener, app launcher, HTTP facade, or Mini admission rule here.

The included Sandstorm schemas are from upstream commit
`a97cf3ee19d3bf2761cd597583ca5d998de425d8`; exact file digests are in
`schema/SHA256SUMS`. The compiled closure is `grain`, `web-session`,
`api-session`, `util`, `identity`, `powerbox`, `activity`, `supervisor`, and `ip`.
The `schema/capnp/persistent.capnp` code-generation input comes from Cap'n Proto
1.5.0, with only its unused `persistent` annotation omitted: `capnpc` 0.27
otherwise generates a duplicate Rust module for the annotation and the
`Persistent` interface. The interface ID and method schema remain unchanged;
none of these pinned Sandstorm schemas uses that annotation.

`SessionParameters` are protocol fields, **not evidence of authorization**.
The trusted Mini controller must check the exact resource, generation,
subject, current grant, and operation before it passes values or invokes an
app method. Every app delivery, including GET, is external execution. This
crate does not offer a caller-facing authentication endpoint or synthesize
permissions from a URL, HTTP header, or unverified role. Its current
`SandstormApi` and `SessionContext` implementations fail closed on unsupported
methods. The typed operations are `getViewInfo`, `newSession` for `WebSession`
or `ApiSession`, and `dispatch_web` for GET, HEAD, POST, PUT, PATCH, and DELETE.
`getViewInfo` retains ordered permission definitions and role definitions,
including localized title/description text, obsolete and default flags,
each role's raw permission bitset, and the view's denied-permission bitset.
Permission and role IDs are list indexes. These are app-supplied descriptors,
not effective grants: `RoleAssignment.none` means the single declared default
role or an empty set, whereas `allAccess` is a separate assignment. The decoder
rejects duplicate/invalid permission names and multiple defaults. It preserves
bitset lengths rather than treating missing bits as an authorization rule;
the Mini controller must reconcile a committed descriptor with current sharing
authority before it supplies session permissions.
`permission_schema_source_bytes` projects those exact ordered role-relevant
fields to bounded JSON for Lean authoring, with an explicitly supplied schema
version because ViewInfo has none. The source JSON is untrusted; the Lean
`Host.ApplicationPermissionSchemaAuthoring` parser validates it and emits the
strict canonical schema bytes/root. This crate does not hash an authoritative
schema or pack effective permission bits into a dispatch identity.
The latter sends exact typed request content, cookies, accept/encoding,
ETag preconditions, and whitelisted additional headers. It returns the
Sandstorm response union, status where the union defines one, response
headers/cookies, and inline or bounded streamed body. Every dispatch needs a
caller-supplied response bound and deadline; a deadline after send means
delivery may be uncertain. The older `get_inline` remains for the initial
fixture and rejects streamed/non-content replies.

The bridge passes the `path` text, including a query suffix, to its HTTP
upstream. The Cap'n Proto schema has no separate raw-query or arbitrary-header
field: request/response additional headers are limited to Sandstorm's
whitelists, and response status codes are limited by its response union. This
crate rejects unsupported request headers rather than silently dropping them.
WebSocket, streaming *request* bodies, WebDAV methods, persistence, powerbox,
and Sandstorm API callbacks are not connected. There is no HTTP fallback.
Incoming Cap'n Proto traversal is capped at 16 MiB and 64 nesting levels;
request content and collected response content have explicit byte bounds.
The identity capability attached to `UserInfo` answers `getProfile` from the
same supplied session parameters; it does not authenticate those parameters.
The pinned packaged HTTP bridge accepts `ApiSession` only when its
`BridgeConfig.apiPath` is nonempty; a typed request can therefore fail on an
app that exposes only a web view. Its config is read inside the package from
`/sandstorm-http-bridge-config` by the app launcher, outside this crate.

Run the focused gate with `CARGO_BUILD_JOBS=2 cargo nextest run --manifest-path
native/spk-rpc/Cargo.toml`. The interoperability test uses both ends of a real
Unix socketpair and generated pinned interfaces: it bootstraps the supervisor
capability, queries view metadata, starts Web and API sessions carrying identity
and permission fields, calls the identity profile capability back across the
socket, sends a typed `WebSession.get` and a body-carrying POST with query,
cookie, and whitelisted header to a fake app server, then checks typed error,
stream completion, overflow, and unsupported-header refusal.
It does not run a third-party SPK, the packaged bridge, or the Mini controller.
