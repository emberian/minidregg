# Resident privilege and process custody

The resident consumes app-controlled Cap’n Proto bytes. Identity-switching
capabilities therefore cannot remain with its parser, even when a syscall
filter restricts their nominal target. A new user namespace can change the
meaning of credentials and capabilities. The boundary must establish the
host identity before app input, rather than rely on every parser remaining
uncompromised.

## Fixed bootstrap, two unprivileged parsers

The root broker renders a fixed generation unit. Its trusted environment
selects separate operator and app UID/GID pairs; app packets cannot select
either. The unit begins with only SETUID, SETGID and SETPCAP in its capability
bounding set, no ambient capabilities, and no_new_privs. Its executable enters
`resident-bootstrap`, which forks before reading resident configuration or app
bytes. This small bootstrap parses only the broker-selected numeric identities.

The parent retains the unit’s MainPID, switches to the operator identity, clears
supplementary groups and all five capability sets (including bounding and
ambient), and verifies real/effective/saved UID and GID plus no_new_privs.
It denies unshare, setns, namespace-bearing clone and clone3 before the
configuration/SPK/Cap’n Proto consumers begin; ordinary threads still work.

The worker independently switches to the fixed app identity and performs the
same credential/capability checks before parsing its bounded launch JSON. It
closes inherited non-channel descriptors and clears its environment. It keeps
no identity-switching capability. Its private channel accepts one launch with
five inherited descriptors, then only bounded wait/stop commands. UID/GID are
absent from that packet schema.

The worker intentionally does not inherit the operator namespace-denial filter:
the pinned bubblewrap executable must create the app sandbox. Its host identity
is already the separate app UID, with no host capability or supplementary group
that can map another host UID or reach operator custody. This is a distinct
physical boundary from the operator parser. The sandbox’s own namespace and
seccomp floor remains necessary and unchanged.

## Source admission still selects the work

This split creates no launch authority. The existing source-bound preparation,
current native lifecycle claim, journal lock, executable SHA/inode checks and
fd3/image/volume/seccomp/output gate precede the channel send. The worker repeats
the executable and descriptor shape checks. It cannot choose a different app
identity. A partial send or lost reply consumes the one channel; it does not
create permission for a second START.

Package origin and physical custody do not imply a current user grant. The native
source admission and each operation’s current authority remain independent of
the installed package and the resident’s process credentials.

## Reaping is physical evidence, not a receipt

The worker is the actual parent of the app child and owns its waitpid. The
operator receives the retained PID/start identity over the private channel. It
never fabricates a successful app waitpid because it cannot reap a grandchild.
Channel EOF causes the worker to kill/reap its actual direct child; the operator
can then reap its own worker. A channel error does not confirm child death.

All processes remain in the original generation unit and cgroup. KillMode is
control-group. If the worker dies, a direct-child result alone cannot prove that
a descendant is gone. STOP or failed-START reconciliation must independently
audit the exact retained Unit, InvocationID and cgroup and refuse a current job,
new incarnation or populated cgroup before native completion. Pause-for-backup
is not this fence, and a portable archive acknowledgment cannot replace it.

## Qualification and limits

The focused wire checks reject packet identity selectors, unbounded frames and
false reap success after channel loss, and check descriptor close-on-exec. The
explicit root fixture changes credentials only in disposable forked children.
It checks all capability sets, groups and no_new_privs, namespace refusal and
ordinary threading, then launches a harmless inode/SHA-pinned executable and
verifies actual EOF-driven app/worker reaping with an independent root observation.
This fixture does not author a native launch receipt or qualify hosted app
readiness, real browser interaction or provider completion.

A production role still needs its ordinary binary build, source/role seal and
current admitted profile transition. An already claimed failed generation must
first reconcile its exact original operation under the original configuration.
Changing the launcher or role is not permission to reset that retained claim.
