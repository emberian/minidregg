# Isolated fn transport for the GitWeb preview

The private hbox node is running under
`/tank/dregg-preview/fn-gitweb-r3-20260927`. This is a **new** format-8 Store;
the protected `/tank/fn/node` and the older preview at
`/tank/fn/scratch/mini-selected-receiver-20260927-2` were not changed. The
systemd **user** unit is `mini-fn-gitweb-preview-r3.service`, invocation
`7ab63ee537434f278d80ffdbb13b038e`. It runs with `MemoryMax=8G`,
`CPUQuota=150%`, `TasksMax=64`, and no automatic restart. The observed peak
after setup was about 60 MiB. hbox user lingering is enabled; the transient
unit does not survive a reboot without an explicit start from the pinned
config.

The unit runs the qualified format-8 image
`/tank/fn/gates/qual-bbf52159-20260925/build/images/bbf52159dcab19228bd6cd0b855b99dd6d68758d/fn-host`
(SHA-256 `432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505`),
with core SHA-256 `6e569af117ba4afcf52bfd74f2a40ac222ead7701bb0b84bac799c53521bfe9e`.
The listener is **only** `127.0.0.1:11213` and requires STARTTLS before
AUTHINFO. Its private control socket is
`/tank/dregg-preview/fn-gitweb-r3-20260927/control.sock` (mode 0600).
The root, config, TLS private key, password and cursor artifacts are all
under hbox-owned private paths; the password is not in these logs. The
config SHA-256 is
`5eb98f78d8a26f7d9a47762ea2381aa7f0fb67b283ee7d59b9e8347bc5ab169f`;
the pinned self-signed certificate SHA-256 is
`ae2be87dc39bb01962b3f153c17995e4146935630960a2a945641445b23e3db7`.
It was generated with a two-day validity for this bounded preview.

`fn.test` is the sole group. The Store is format 8 with
`max-article-octets=1,048,576` and `max-record-octets=67,108,864`.
`selected-mini-gateway` was freshly bootstrapped and registered for exact
`fn.test`, query version 1, view version 0, registration epoch 1. Its
history is `f4b53b367d8571ade77685aa2106c2638cb03876c7a358f8ce88647535b007d9`,
incarnation is `78f24ec2a52acdd4a9b4898c9455c10aad29702258d654a502de0a69f65034a1`.
The registered cursor SHA-256 is
`8ffefcd65314629f44370b9eac4c42456d0930e45660a55195b0f36110c75e4b`,
ACK 0 and frontier 2. An initial read-only poll advanced a *candidate* cursor
to position 2 with a zero-byte event; it was **not ACKed**. Store status shows
two setup transactions and zero articles. No POST, Mini Store operation,
public listener, or external send occurred. The fn registration/cursor is a
transport scope, not a Mini event20 receipt.

The exact native operator and consumer command forms were checked against
the qualified fn source's `AGENTS.md`, `docs/operator.md`, and
`tests/test_native_consumer_e2.py`. The initial one-shot setup script is
[provision-hbox.sh](provision-hbox.sh); its current version includes the
parent-directory and system-OpenSSL corrections but was not rerun end-to-end
after the partial setup. Its first attempt refused before
creating the preview root because `/tank/dregg-preview` was absent and
root-owned; an operator created that 0700 hbox-owned parent. The second
attempt created only `fn.toml` and then the packaged OpenSSL CLI refused its
unconfigured dynamic library path. A state-checked
[resume script](resume-after-cert-tool-hbox.sh) used the system OpenSSL CLI
for certificate and random-secret generation; the fn process itself uses
the qualified image and its pinned OpenSSL runtime. It did not rerun init or
registration after an uncertain result. The [setup result](resume-r1.log),
[read-only verifier](verify-hbox.sh), [verdict](verify-r2.log), and
[invocation journal](journal-r1.log) are keyless.

Read-only checks passed: exact image/core hash, unit and cgroup state,
loopback-only listener, protected file/socket modes, format-8 profile,
registered/position cursor byte equality, ACK 0/frontier 2, and zero-article
Store. Cleartext AUTHINFO returned `483`; the pinned TLS certificate verified,
unauthenticated GROUP returned `480`, and the private posting login over TLS
returned `281` followed by `211` for `fn.test`. The latter sent **no** article.
The last [verification log](verify-r2.log) excludes credential values.

The actual signed GitWeb selected atom and assembled article do not yet exist
in the retained r3 Mini fixture. The join's selected-file cap is 1,000,000
bytes, which leaves only 48,576 bytes under this fn article profile for the
carrier envelope at its extreme. **Measure the exact assembled `article.eml`
from `join.sh prepare` and refuse POST if it exceeds 1,048,576 bytes.** A
larger artifact requires an explicit offline profile change or a new node;
the estimated ~66 KiB payload alone is not a measured article size. Event20
registration and event19 neutral-progress Mini receipts are separate and
must be admitted by the join owner before selected publication.

For operator inspection without secrets:

```sh
ssh hbox 'systemctl --user show mini-fn-gitweb-preview-r3.service -p ActiveState -p InvocationID -p MemoryPeak'
ssh hbox 'bash -s' < docs/evidence/2026-09-27-fn-preview-node/verify-hbox.sh
```

The setup script deliberately refuses an existing root. After a host reboot,
inspect the retained Store and cursor first; never run `init`, `bootstrap`,
or `register` again merely because the transient user unit is absent. A
bounded restart uses the same pinned image/config and a new user unit
invocation, followed by fresh read-only status and cursor checks. The private
control socket grants operator administration and should not be exposed to
the posting caller.
