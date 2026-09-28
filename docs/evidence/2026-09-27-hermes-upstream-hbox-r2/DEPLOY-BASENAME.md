# Deploy-compatible Hermes launcher basename

The committed r2 probe used the private launcher name
`bwrap-hbox-profile`. The Mini controller and `install-controller` require
the configured launcher program's basename to be exactly `bwrap`, with its
`launch-gate` sibling. This is a deployment preflight requirement, not a new
sandbox policy.

On hbox, a new private
`/tank/dregg-preview/hermes-upstream-r2/launcher/bwrap` was copied from
`bwrap-hbox-profile` without changing its contents. Both have SHA-256
`efda87a5033fc24bb074cc68bfcca8686a448cd4e10175ca8d74b2c6884961a7`;
the sibling `launch-gate` has SHA-256
`2cf1d29ad7fcbce8e2e476ce803bc0c77785f720ceca02ba77e2530b849e7fb6`.
Both are hbox-owned mode 0700 beneath the private r2 root. The launcher
still invokes the same root-owned, AppArmor-qualified
`/usr/local/libexec/mini-grain-bwrap` and retains `--unshare-net`.
No runtime-root member or venv was replaced.

The bounded r2 probe was run again with that **exact** deploy-compatible
launcher path. [Its keyless log](probe-deploy-name.log), SHA-256
`072c7536242d947364753ee39ab3c3c8e9847917c3fdd85aa1f90698dc226fcb`,
records the real upstream ACP `--check` and protocol-v1 `initialize`
passing in separate no-network user units. Both workers and the dummy
controller were subsequently inactive (`LoadState=not-found`). The second
worker peaked at about 55 MiB. The same current Mini binaries remained
staged; no provider bridge, prompt, MCP, or model request was made.

The controller can now name
`/tank/dregg-preview/hermes-upstream-r2/launcher/bwrap` in a reviewable
scoped command. Full hosted acceptance still requires a current Mini Host,
provider custody, and an actual app/MCP handoff.
