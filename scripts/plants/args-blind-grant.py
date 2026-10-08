#!/usr/bin/env python3
"""HOST PLANT for objective-call-native-journey.py --plant args-blind-grant (GPT-6 row A, A2).

  scripts/plants/args-blind-grant.py TREE

In TREE (a throwaway copy; files are replaced via temp + rename, hardlink-safe), Kernel/ObjectiveCall.lean's
Grant.judge ignores the call's arguments: the value constraint is skipped and every use charges 0 against
the cap. The delegation theorems (the section `Delegation: every frame receiving delegated authority ...`)
are red under this plant (logs: plant-judge-ignores-args.log), so the plant also removes that section to
let the Host link: the planted binary is what the kernel would ship WITHOUT those theorems. Built into a
Host, row C9 must go red (a grant capped at 10 lets the 20 commit)."""
import os, pathlib, sys

tree = pathlib.Path(sys.argv[1])
path = tree / 'Kernel/ObjectiveCall.lean'
s = path.read_text()
for old, new in [
        ('  else if grant.args.admits args = false then .mismatch .args\n', '  else if false then .mismatch .args\n'),
        ('  else match grant.args.amount args with\n', '  else match (some 0 : Option Nat) with\n')]:
    assert s.count(old) == 1, old
    s = s.replace(old, new)
a = s.index('/-! ## Delegation: every frame receiving delegated authority')
b = s.index('#assert_axioms Journal.posts_state\n')
s = s[:a] + s[b:]
for name in ['Grant.judge_admit', 'spendFrom_some', 'Authorized.spend', 'frameAuthority_spec', 'exec_delegations',
             'invocation_delegated_authority']:
    s = s.replace(f'#assert_axioms {name}\n', '')
tmp = path.with_suffix('.lean.plant-tmp')
tmp.write_text(s)
os.replace(tmp, path)
print(f'planted args-blind-grant in {path}')
