# The Charter of {ORG_NAME}

Founded in {REALM} at height {FOUNDED_AT} by {FOUNDER_NAME}.

This document is prose. What binds is the law installed on `{REALM}-org-{G}` and on each ballot cell
(`law.org`, `law.ballot`), and the delegations listed in `offices.json`. Where this page and the installed
law disagree, the law is what the kernel enforces.

## Offices

- **Leader.** Holds the org cell. Changes only to the result of a closed leader ballot (law.org clause 3).
- **Treasurer.** Pays from the treasury, at most {MAXPAY} gold a turn (the office's `maxDelta`).
- **Recruiter.** Invites and ranks members.

Each office runs until height {TERM_END} or until the leader revokes it. A leader who is replaced takes
their appointees' offices down with them.

## Elections

A ballot has up to eight seats and three candidates. Each member votes once, only in their own seat, and
only while the ballot is open. The returning officer closes it. The tally program (`{TALLY_PROGRAM}`,
regime: {REGIME}) writes the result once.

## Taxes

The rate is {TAX_RATE} per day, capped by the charter at {TAX_MAX}. Tax is collected only from members who
have delegated it (`tithe accept`). A member who has not delegated is skipped, and the journal shows it.
