# Shell entrance

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

Enrollment (`enroll plan|seal`) signs with the sponsor's key and the
newcomer's key in one process, so today the newcomer's secret must be readable
from the sponsor's session home. That is the current contract, not a shell
choice; independent provisioning (lane M3) removes it.
