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
methods. The first typed operations are `getViewInfo`, `newSession` for
`WebSession` or `ApiSession`, and a bounded inline `WebSession.get`. Streamed
bodies, response variants beyond inline content, other methods, cookies,
headers, WebSocket, persistence, and powerbox callbacks require explicit
controller and transport work before use. An unsupported response is an error,
not an HTTP fallback. Incoming Cap'n Proto traversal is capped at 16 MiB and
64 nesting levels; each inline body also has a caller-supplied byte bound.
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
socket, and sends a typed `WebSession.get` to a fake app server.
It does not run a third-party SPK, the packaged bridge, or the Mini controller.
