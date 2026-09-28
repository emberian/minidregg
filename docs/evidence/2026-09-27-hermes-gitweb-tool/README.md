# Hermes GitWeb tool source gate (2026-09-27)

The unforked Hermes MCP worker now offers `mini_gitweb_read` and
`mini_gitweb_edit` for an operator-listed application. The worker runs fixed
`/usr/bin/git` commands inside its existing confinement. A temporary loopback
Git smart-HTTP proxy sends each exact GET/POST through the controller's
`__mini_gitweb_http_raw` broker route, which uses the existing lifetime v3
dispatch, fresh installed permit, mark-send, and settlement path. The worker
receives no app or payer signing key. `mini_application_api` now projects a
bounded UTF-8 response body for model use while its raw exact reply remains in
the controller journal.

Each proxy listener requires a fresh 256-bit Git child header before it
forwards anything; it consumes that header locally. Public MCP calls cannot
invoke `__*` internal broker operations. A read rejects a `git-receive-pack`
POST before its Mini call, and each local HTTP request has a 10-second absolute
read deadline.

Authenticated `git-upload-pack` POST is permitted for clone/read; only
`git-receive-pack` POST mutates. A canonical empty bare repository with
default branch `master` can receive its first commit.

The edit accepts one ordinary relative text path (at most 256 bytes), content
at most 8192 bytes, and one commit message at most 256 bytes. It clones branch
`master`, writes the file without following a checkout symlink, commits,
permits one `git-receive-pack` POST, and compares `git ls-remote` with the
new commit. The proxy rejects bodies over 24 KiB, unsupported routes,
ambiguous HTTP lengths, transfer encoding, and a second receive-pack POST.
Any uncertain controller result stops the child and retains its native
uncertainty; there is no automatic mutating retry. A legitimate pack over the
current 24 KiB Mini request limit fails explicitly and requires a separately
reviewed larger wire profile.

Exact source SHA-256 at this gate:

```text
b69789af85b1ee6c842dca4434eeb45182a672956344934855190c81c6e1a52d  native/grain-runtime/src/application_api_tools.rs
fcf66488382fb7fc9df5ae3cdf0ec0c042dc6afb9bb27ea334a7dbb53d6adb97  native/grain-runtime/src/main.rs
d52cf36a6505140937b226933a50ed8856dda71f1841457419350da8fad18743  native/grain-runtime/src/mcp.rs
57f4a8c547930d8bbd53db42f4ff0720caca690e1f591089f0ef5980bfd77c92  native/grain-runtime/src/gitweb_worker.rs
```

In `native/grain-runtime`: `cargo nextest run` passed 135/135 and
`cargo clippy --all-targets -- -D warnings` passed. Focused tests include
bounded readable HTTP projection and an uncertain receive-pack call forwarded
once with its Git child stopped, unauthorized loopback/refused read-mode POST,
and hidden broker-name refusal. An isolated actual `/usr/bin/git` plus
`git http-backend` test passed first edit/push from an empty bare repo, read,
then second edit/push against the existing repo; this CGI fake-forward does
not exercise Mini admission or SPK custody. Git checkout expansion is constrained by the
existing worker `/tmp` tmpfs/cgroup, not a separate repository-size quota in
this helper. This is a source/component gate. The same-r3
Store still lacks accepted app, ticket and lifetime grant lineage, so no
native GitWeb dispatch, real model call, or hard-reconnect journey is claimed.
