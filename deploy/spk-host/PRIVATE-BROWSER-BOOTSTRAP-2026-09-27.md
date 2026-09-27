# Private browser bootstrap component — 2026-09-27

This qualification used a fresh owner-private Persvati custodian at
`/run/user/1000/mini-spk-browser-probe-20260927`, one self-signed test
certificate for `friend-a.localhost`, loopback TLS port 18443, and an SSH
local forward of that same port. It did not install browser trust, change DNS,
open a public listener, run an SPK, or touch a Mini Store. The private
custodian directory and one-time marker are retained for review; both test
services are stopped.

The operator can initialize a **new** custodian with:

```sh
spk-hostd init-custodian ABS_NEW_OWNER_PRIVATE_DIR friend-a.localhost:18443 APP SUBJECT SESSION TICKET
```

The parent directory must already be owner-private beneath protected
ancestors. Initialization refuses an existing directory; it writes 256-bit
`bootstrap.token`, `browser.token` and `api.token` in distinct 0600 files and
only SHA-256 hashes in 0600 `custodian.json`. It prints no token. An operator
must deliver the bootstrap token privately to the intended friend. For the
private route, place a reviewed certificate and key for that exact hostname as
0600 `tls.crt`/`tls.key`, run `spk-hostd serve-http-unavailable DIR` and
`spk-browser-proxy DIR 18443` under the same custodian UID, then forward
`127.0.0.1:18443` over existing SSH. The proxy binds only Persvati loopback
and forwards to the fixed sibling `DIR/http.sock`; the browser needs an
explicit hostname-to-loopback mapping and trust decision for that certificate.
Separate friends require separate Unix accounts, hostnames, ports, certs,
tokens and fixed Mini coordinates. No public reverse proxy is installed.

On Persvati, the bounded release build used `CARGO_BUILD_JOBS=2 cargo build
--locked --release --bin spk-hostd --bin spk-browser-proxy`. The first
`spk-hostd` ELF SHA-256 was
`d25c478466c4d46ae92ac5ffdc5ee3cf0aca2044bf11cc2339c9a6e518243c3f`;
after the exact stale-socket fix, the second `spk-hostd` ELF SHA-256 was
`0c7d6fccc0967a4510cb493d2e1bb2cccf4d843e7f0f92c9bd3b78234c552ed8`.
the `spk-browser-proxy` ELF SHA-256 was
`0dd31ab31e09405ebab60a0436391008300701de81185bb7c5b89a1cbdf4a6eb`.
The test certificate SHA-256 was
`ccd1859b12ed15ffcc8aad18079d0c0a0255b9430ac14afe4b69d0a575df37e2`.
The certificate was trusted only by `curl --cacert` for this test.

The two transient user units had `MemoryMax=256M`, `TasksMax=16`,
`RuntimeMaxSec=180`, `KillMode=control-group` and `NoNewPrivileges=yes`:
`mini-spk-browser-http-probe-20260927.service` and
`mini-spk-browser-tls-probe-20260927.service`. The Unix socket was owner UID
1000/mode 0600; the custodian directory was mode 0700, and config/token files
were mode 0600. HTTPS GET `/__mini/bootstrap` returned 200 and a 290-byte
tokenless form. Same-origin POST carried the bootstrap token in its bounded
form body, returned 303 to constant `/`, created `bootstrap.used`, and set
`__Host-mini_spk_session` with `Secure; HttpOnly; SameSite=Strict; Path=/`.
Replaying the token was refused. A subsequent cookie-authenticated direct
GitWeb GET returned 503 because native dispatch admission is not wired. A
laptop `ssh -L 127.0.0.1:18443:127.0.0.1:18443` test reached the same TLS
form with HTTP 200. Tokens, cookie values and private response headers were
not printed or copied into this evidence.

Stopping the first HTTP unit exposed a retained, unbound Unix socket path.
The revised source removes only an exact owner/mode/inode socket when connect
returns `ConnectionRefused` while holding the private service flock. A live
second instance and any other connect error refuse. The focused stale-socket
test passed, and a second transient HTTP unit
`mini-spk-browser-http-restart-probe-20260927.service` started over the
retained path and returned form HTTP 200. It too is now inactive/MainPID 0
with an empty ControlGroup; no loopback port listener remains. A stale socket
pathname may remain after SIGTERM, to be checked on the next start.

After rustfmt, the exact final source-matched release binaries were rebuilt:
`spk-hostd` SHA-256
`df7a054590cf04ee6c129290bef7daa41bb3aa1be476cb7e007ef6f6202f31c2`
and `spk-browser-proxy` SHA-256
`11dbb7ada4a4469aec2fd10384041192ac3fc698691dacdc0a5465434089c4a9`.
They ran in two final 60-second-capped transient units against the already
consumed private custodian. The form again returned HTTPS 200 and an
authenticated GitWeb GET returned 503; no second bootstrap POST occurred.
Both final units stopped inactive/MainPID 0 with empty ControlGroups, and
port 18443 closed.

The final source files are `native/spk-host/src/http_entrance.rs`,
`native/spk-host/src/bin/spk-hostd.rs`,
`native/spk-host/src/bin/spk-browser-proxy.rs`, and the crate Cargo manifest
and lockfile. Their SHA-256 values and the final focused test result are in
`PRIVATE-BROWSER-BOOTSTRAP-2026-09-27.log`. The previously committed 503-only
HTTP entrance evidence covers the earlier source snapshot; it is not being
relabeled as this later bootstrap build.

This is a private transport/bootstrap gate only. The participant signer,
Mini dispatch authoring and exact checked readback are absent; every app
request remains 503. The serial TLS proxy has no general availability or
public-facing reverse-proxy qualification.
