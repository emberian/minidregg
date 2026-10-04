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
config pin, an operator operation). It never runs a shell; `ssh friend@host
'cmd'` exits 64. There is no workspace or home on the box for a proxy key.

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
    # prints your Mini public key and your next key's public half (two lines of
    # 64 hex; K-PREROTATE); send both to your sponsor
mini --remote mini-box join --key ~/.mini/me.key --sponsor-plan offer.json --dir ~/.mini/box
    # offer.json is what your sponsor's `enroll offer NAME` printed. The Host
    # re-decodes it over the proxy and checks it commits to YOUR next key
    # (a plan committing another key is refused); you sign possession. Prints a signature:
    # send it to your sponsor
mini --remote mini-box join --key ~/.mini/me.key --welcome welcome.json --dir ~/.mini/box
    # welcome.json is your sponsor's `enroll welcome NAME`; makes your workspace
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

What this does **not** yet give a proxy friend: the provider is a full peer. It
replays the Store named by `storageRoot` from genesis and refuses a rollback or
a rewritten prefix, and there is no command that hands a friend such a Store;
so on a friend's own machine signing stays refused until one exists. The macOS
client has no consent pair (`consent: null` in provenance) and cannot sign.
When the client is given a Host path and `MINI_CONSENT_HOST` is unset, it takes
`minidregg-client-consent` beside that Host (the hosted shell's case, since the
candidate ships both in `bin/`), and the provider then reads the deployment
config and its Store with the session's own permissions.

The sponsor's side, in their (hosted) shell:

```
enroll plan NAME PUBLIC-KEY-HEX NEXT-PUBLIC-KEY-HEX COSIGN-HEX   # the three lines `mini join --key` printed
enroll offer NAME > offer.json       # hand to the friend
enroll seal NAME SIGNATURE-HEX       # the signature join printed
enroll submit NAME
provision NAME SUBJECT FUNDING PREDICATE   # optional: an account + factory grant so they can create
enroll welcome NAME > welcome.json   # hand to the friend
```

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

## Endings

stdout carries the client's own output. stderr ends every failed verb with one
line whose first word says who decided:

| exit | first word | meaning |
|---|---|---|
| 0 | | done |
| 1 | `error:` | the client stopped; the Host was not asked or did not answer |
| 2 | `usage:` | the line did not parse |
| 3 | `refused:` | the Host refused; its outcome is decoded by the Host's own `inspect outcome` and the frame kept in `HOME/refusals/` |
| 4 | `undecided:` | the Host answered uncertain, contention, unavailable or absent; `lookup ID` asks again |

A refusal is recognised from the Host's reply byte or outcome type, recorded by
the client where the Host answered, never from error text.

## Known limit

`enroll plan NAME KEYFILE NEXT-PUB-HEX COSIGN-HEX` (a secret key file in the
sponsor's session home) still signs with both keys in one process; it is kept for
hosted sessions whose keys are on the box anyway. The next key and its
co-signature are the friend's words, never a file in the sponsor's home. A newcomer
who keeps their key uses `enroll plan NAME PUBLIC-KEY-HEX NEXT-PUBLIC-KEY-HEX COSIGN-HEX`
and `mini join` (above); no process on the box ever holds their secret.
