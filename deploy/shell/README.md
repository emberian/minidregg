# Shell entrance

## Two modes, and what each one means for your key

| mode | the key line | where your Mini key lives | who can read and sign as you |
|---|---|---|---|
| **hosted shell** (`mode=shell`, `mini-shell-ssh`) | `restrict,pty,command=".../mini-shell-ssh ..."` | in your session home **on the box** | you, **and the box's operator (root and the `mini` user)**: they can read your key file and sign as you, and read everything you store |
| **proxy** (`mode=proxy`, `mini-socket-proxy`) | `restrict,command=".../mini-socket-proxy MINI SOCKET"` | **on your own machine**; it never leaves it | you. The operator still sees what the Store keeps (what you write, when, as which subject) but holds no key that signs as you |

The hosted shell is a convenience: nothing to install, one `ssh`. The proxy is
the private mode (PRIVACY.md tier B): you run the same `mini` binary locally and
the box only relays its frames. A proxy key's session is a byte pipe to the
public socket: `mini socket-proxy` accepts socket frames that name the
deployment's pinned config and a public-socket operation, relays each on its own
socket connection, and closes the pipe on anything else (a stray byte, a wrong
config pin, an operator operation; the module header of `native/resource-client/src/proxy.rs`). The
one other thing a proxy key can ask for is a signed provider-credential exchange,
relayed to the box's key broker (`mini-socket-proxy`). It never runs a shell;
`ssh friend@host 'cmd'` exits 64. There is no workspace or home on the box for a proxy key.

`render-shell-key mode=proxy ABS_PROXY_WRAPPER ABS_MINI ABS_PUBLIC_SOCKET FRIEND.pub`
prints the proxy line; `render-shell-key [mode=shell] ...` (below) the hosted one.

## The friend's three commands (proxy mode)

Get `mini` for your machine (Linux x86-64 `bin/mini` or macOS arm64
`bin/clients/aarch64-apple-darwin/mini` from the candidate; check its SHA-256
against the published `SHA256SUMS`). Put `Host mini-box` with your ssh key in
`~/.ssh/config`, and send the operator your **ssh** public key for a
`mode=proxy` line. Then:

```
mini join --key ~/.mini/me.key
    # prints three lines: your Mini public key, your next key's public half and its
    # co-signature (K-PREROTATE); send all three to your sponsor
mini --remote mini-box join --key ~/.mini/me.key --sponsor-plan offer.json --dir ~/.mini/box
    # offer.json is what your sponsor's `enroll offer NAME` printed. The Host
    # re-decodes it over the proxy and checks it commits to YOUR next key
    # (a plan committing another key is refused); you sign possession. Prints a JSON object
    # whose `possessionSignature` is the signature: send it to your sponsor
mini --remote mini-box join --key ~/.mini/me.key --welcome welcome.json --dir ~/.mini/box --verifier /ABS/PATH/minidregg-host
    # welcome.json is your sponsor's `enroll welcome NAME`; makes your workspace.
    # --verifier is the pinned native Host on your machine; without it the command errors
```

and from then on

```
mini --remote mini-box shell --workspace ~/.mini/box/workspace --home ~/.mini/home
```

is the same shell as the hosted one (every verb below), running on your
machine. `MINI_SSH` names another ssh program, as `GIT_SSH` does.

## Signing consent: the three variables

`mini` signs nothing the box chose. Before any key signs an intent, an
observation or a plan, a **consent provider selected on the signing machine**
rebuilds the exact bytes from the retained request and an independently
admitted copy of the source, and the client refuses on any difference (one
changed byte included; `client_consent::tests::remote_signing_plan_with_one_changed_byte_is_refused_before_signing`).
Without a provider the client refuses to sign at all. Three variables select it,
always as absolute paths, and always together:

| variable | names | from the candidate |
|---|---|---|
| `MINI_LOCAL_HOST` | the native Host image used for pure codecs (author, inspect, signatures, assemble) | `bin/minidregg-host` |
| `MINI_CONSENT_HOST` | the consent provider, run as `PROVIDER CONFIG stdio` | `bin/minidregg-client-consent` |
| `MINI_CONSENT_CONFIG` | the provider's configuration: the deployment config, whose `storageBinary`, `storageRoot` and `signatureBinary` name a Store helper, a **locally admitted** Store and a verifier on the signing machine | your own file |

The Linux friend bundle is `bin/clients/x86_64-unknown-linux-gnu/` (mini, both
consent executables, the verifier and the Store helper; `provenance.json`
`.clients["x86_64-unknown-linux-gnu"].consent` pins each). A workspace records
the three paths when it is made and refuses a different selection later in the
same process.

The default (full) provider reads a locally admitted Store, which a friend's own machine does not have. Thin consent is the mode that needs none. With
`MINI_THIN_CONSENT=1` the client uses consent frames 230-232, which read no Store:
the provider checks what custody signs against its own command and the target
views the Host served under the member's observe grants, and refuses a turn it
cannot display, naming the unsigned input (`thin_mode` and `thin_plan` in
`native/resource-client/src/client_consent.rs`; the statement is `Kernel/NativeThinConsent.lean`).
It displays invocations and delegations. A birth (`create`) signs through its own thin arm,
frames 234/235: the provider re-authors the member's retained source at the coordinates the
Host's draft carries and checks the plan against it, still reading no Store (`birth` in
`native/resource-client/src/workspace.rs`, `set_thin_birth_source`; the statement is
`Kernel/NativeThinBirth.lean`).
Status: **exists** (code and unit tests). It is **not journeyed**: the scripts are
`native/resource-client/journey.d/jpriv2.sh` (enrol, then write and read over
`--remote`, with a consent config naming no Store) and
`native/resource-client/journey.d/jthin-consent.sh`, and no recorded passing run of
either is in `docs/evidence/`. The macOS client has no consent pair
(`consent: null` in its `clients_json` provenance entry, `deploy/candidate/build.sh`) and cannot sign.
When the client is given a Host path and `MINI_CONSENT_HOST` is unset, it takes
`minidregg-client-consent` beside that Host (the hosted shell's case, since the
candidate ships both in `bin/`; `with_consent` in `client_consent.rs`), and the provider then
reads the deployment config and its Store with the session's own permissions.

Under split tenancy a hosted member's account (`mini-s-NAME`) cannot read the Store, which the
Store operator owns. That is the isolation boundary, so the member's full consent runs box-side,
delegated (`native/resource-client/src/consent_proxy.rs`). Per member, a socket-activated `mini
serve-controller-consent` runs as the Store operator, holds the verifier that replays the Store,
and answers only that member's consent frames (220-227). Its listener is owned by the member and
sits in the member's own 0700 directory. The member's session selects it with
`MINI_CONSENT_SOCKET`, `MINI_CONSENT_PEER_UID` (0: systemd creates the listener),
`MINI_CONSENT_SHA256` (the provider) and `MINI_CONSENT_CONFIG_SHA256` (the pinned config),
alongside the three variables above. The client refuses a peer, provider or config that differs
from these pins before it sends a frame. The member gains no read access: what comes back is the
consent answer for its own request. The service keeps its warm verifier between connections
(with `--idle-seconds N` it ends after N quiet seconds and restarts from its retained frontier on
the next connection, paying a provider start and a Store admission). The unit pair is the
one `deploy/spk-host/controller-world.py` renders for controllers.

The sponsor's side, in their (hosted) shell (grammar: `ENROLL` and `PROVISION` in `native/resource-client/src/shell_grammar.rs`):

```
enroll plan NAME PUBLIC-KEY-HEX NEXT-PUBLIC-KEY-HEX COSIGN-HEX   # the three lines `mini join --key` printed
enroll offer NAME > offer.json       # hand to the friend
enroll seal NAME SIGNATURE-HEX       # the signature join printed
enroll submit NAME
provision NAME SUBJECT FUNDING PREDICATE   # optional: an account + factory grant so they can create
enroll welcome NAME > welcome.json   # hand to the friend
```

This is the friend-keeps-the-key procedure. The other procedure the operator has is
the hosted account, where the member's key is made by their own `keygen` on the box
and enrolled by `mini-reenroll` (`OPERATOR.md`; the door runs the same steps for
strangers, `deploy/door/README.md`). In both, no process on the box holds a secret
the member did not make there.

`mini shell` is one participant's session over the client contract. Each verb
is exactly one `mini` client operation, run in-process through the same
dispatcher as the command line; the shell adds word syntax, file-name
confinement and the spelling of documented proposal requests, and decides
nothing. `help` lists the verbs and the operation each one is.

## Binding a key to a session

One authorized key is one session. The forced command fixes the client, the
deployment (Host, pinned config, public socket), the workspace and the session
home; the connecting friend chooses none of them.

```
restrict,pty,command="/ABS/mini-shell-ssh /ABS/mini /ABS/host /ABS/pinned-config.json /ABS/public/mini.sock /ABS/homes/NAME/workspace /ABS/homes/NAME" ssh-ed25519 AAAA... friend
```

`mini-shell-ssh` is the candidate's `bin/mini-line`, installed as a root-owned
copy under that name (on the box, `/usr/local/lib/mini/mini-shell-ssh`, with the
`motd.txt` an interactive login prints beside it). It reads the box's
`/etc/mini/session-*` settings once, holds the member's call slot (two at once, a
third is refused with exit 75) and hands a one-verb line to the member's resident
shell; it never runs a system shell.

`render-shell-key WRAPPER MINI HOST CONFIG SOCKET WORKSPACE HOME FRIEND.pub`
prints that line after checking the paths and the key; it installs nothing.
`restrict` removes forwarding and agent access; `pty` is re-allowed so that
`ssh -t` gets the interactive shell.

## Using it

```
ssh -t friend@host                 # interactive: prompt, Tab completion, Up/Down
ssh friend@host 'read shared'      # one verb; the exit code is the verb's
ssh -T friend@host < script.mini   # script: one verb per line, stops at the first failure
```

`SSH_ORIGINAL_COMMAND` is parsed by the shell's own word syntax and never
reaches a system shell. Words: bare, `'literal'`, `"escaped"`, a whole JSON
value starting with `{` or `[`, or `@FILE` for `HOME/requests/FILE`. File names
are plain names inside the session home; nothing may name a path outside it.

Composition is ordinary shell piping between sessions, for example a
delegation handed from one participant to another:

```
ref=$(ssh sponsor@host 'export grant-newcomer')
ssh newcomer@host "import shared $ref"
```

(This is the form `native/resource-client/shell-journey.sh` runs in J3.)

## Templates

The files shell verbs compile in or load unchanged (room templates, the chat,
private-room, job, market and story laws, the Hermes roles, the MUD sheets) live
with the client that embeds them, in `native/resource-client/templates/`
(its README maps each verb to its files). They moved there from
`deploy/shell/templates/` so that one home holds them; nothing on a box reads
them from disk.

## Endings

stdout carries the client's own output. stderr ends every failed verb with one
line whose first word says who decided (the reply bytes are `RESPONSE_NO_RECORD`, `RESPONSE_NEVER_FORWARDED` and `RESPONSE_HOST_OUTCOME` in `native/host-operations.rs`):

| exit | first word | meaning |
|---|---|---|
| 0 | | done |
| 1 | `error:` | the client stopped; the Host was not asked or did not answer |
| 2 | `usage:` | the line did not parse |
| 3 | `refused:` / `charged:` | the Host answered with no record (reply byte 253: decided before any append, so nothing happened; its outcome decoded by the Host's own `inspect outcome`, the frame kept in `HOME/refusals/`), the socket never forwarded the request (reply byte 254), or the Host admitted a charged failure (only the price posted) |
| 4 | `undecided:` | the Host answered under its outcome envelope (reply byte 255, whatever it decodes to), or uncertain, contention, unavailable or absent as an answer: the effect is unknown; `lookup ID` asks again, and nothing is repeated |

A refusal is recognised only from the Host's no-record marker (253), recorded by
the client where the Host answered: never from a 255 frame, whatever it decodes
to, and never from error text. `pay` and `topup` keep a record per request: a rerun after a lost
reply looks the payment up instead of paying again; `again` pays once more.

## Key files in `enroll plan`

`enroll plan NAME KEYFILE NEXT-PUBLIC-KEY-HEX COSIGN-HEX` names a secret key file under
the sponsor's session home (`keys/KEYFILE`); it is for keys that already live on the
box. The hex form above never puts the newcomer's secret on the box. Both need the
newcomer's next public key and its co-signature (their words, never a file in the
sponsor's home), or `--no-prerotation` to enrol without one
(the `enroll plan` grammar in `shell_grammar.rs` and its `--no-prerotation` flag).
