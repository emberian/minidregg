# prod-rowfix

Base: 5896a5945dbce07d17dbbb5b5834318b0f64656e. Scope: pipeline/candidate and driver scripts; no Lean/Rust sources, fixtures, pins, gates, or live service edits.

Decision: install a stable launcher at the service's existing journey-runner path. It holds the results lock and selects runner, rows, lib, and relay formatter from each READY tip's source. An atomic installed bundle on base advance is worse: journeys can process next/green/main at different tips and artifact arrival need not coincide with a warm-base advance. A byte mismatch in ordinary runner execution must refuse before rows; explicit source/rows overrides are test-only and recorded.

Diagnostics: retain systemd service results until evidence capture rather than a scope that may vanish before Result/MemoryPeak is read. Report return code/signal, systemd Result, MemoryPeak and timeout in every FAIL verdict; unknown external signal senders must be stated as unknown instead of guessed. Runner-owned timeout sender is recorded.

Genesis: one candidate-level params helper resolves exactly the numeric zero placeholder to positive wall-clock seconds, preserves positive explicit values, and rejects invalid/missing values. Use it in candidate init and direct example-based genesis drivers without changing fixtures.

Environment: lane has no /srv/artifacts/5896a594... yet. Asked deputy for exact READY set and standing evidence; default is to mirror set to execution host. request_journey executes acceptance outside sandbox. No acceptance job started yet.

Milestone: 5896a594 READY is now visible. First diagnostics plant j501923413 confirmed stale runner refusal and exact-tip launcher PASS. Ordinary rc=17 failure preserved Result=exit-code but systemd returned MemoryPeak=[not set] after deleting the failed cgroup. Added an ExecStopPost hook to record memory.peak while the receiving cgroup still exists; numeric peak assertion remains mandatory. All acceptance evidence is under .rowfix-evidence (uncommitted).

j501985961 passed all plants, but OOM post-hook peak (~3MB at 64M limit) exposed a recreated cgroup measurement. Replaced final measurement with a small row parent and OOMPolicy=continue; parent captures original cgroup memory.peak/events before exiting (also on TERM timeout). Stop-hook evidence is explicitly separate. Added assertion that original OOM peak reaches the 64M limit. Deputy agrees with original-cgroup capture and reporting unidentified external signal senders as unknown rather than inferring a sender.

j502053405 PASS: original OOM peak exactly 67108864, all diagnostics plants pass. Clock helper check PASS. Call alone j502083072 (5896a594 binaries, unchanged call driver, lane runner/rows override) failed after 2052s: MemoryPeak=25769803776 (24GiB), OOMKills=10, systemd Result=exit-code, rc=1; journal explicitly records each kernel OOM kill. Class: scope OOM, not runner timeout or mere parallel load. Evidence .rowfix-evidence/call/5896a594.../rows/call/{scope.properties,cgroup-final.properties,scope.log,call.err,results.json,transcript}. Added SystemdResult, OOMKills, state and runner-stop timing to details per deputy direction; keep systemd Result verbatim in scope.properties.

Compatibility: E historical candidate lacks clock-v2 fields. jhostupgrade must explicitly supply absent v2 operator fields for that historical protocol test before calling the common resolver, preserving its prior E/F/G behavior. SSH and M7 use the common helper before older shipped run.sh init; new packaged run.sh also uses it idempotently. M7 cleanup failures no longer mask a pre-existing verdict.
