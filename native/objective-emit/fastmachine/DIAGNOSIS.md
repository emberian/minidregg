# Why the compiled Lean Core4 machine was 500–2900× slower than the C machine

Lane FASTMACHINE, 2026-10-04. Host hbox (load average 18–28 throughout, so single
runs vary by up to ~2×; every figure below is from the cited log). Logs live in
`/tank/dregg-build/claude-lanes/fastmachine/logs/`. Packets come from
`native/objective-emit/packets.ts` over the preview, extra and market cohorts
(`packets-01`: 42 items, `packets-02`: 238 items).

Evidence classes: **executed** (a binary ran, the log has the line) and **read** (the
compiled C under `.lake/build/ir/Theory/` was read). Nothing below is inferred.

## Counters (executed: `objective-machine-diag profile`, `logs/profile-01.log`)

These counters come from the specification's own `stepRaw` iteration. Each one is a
sum over all ticks.

| | StressWork work(14) | StressCount count(20000) |
|---|---|---|
| ticks | 524,293 | 360,037 |
| heap writes (`set!`) / pushes | 65,544 / 49,163 | 40,012 / 40,014 |
| Σ heap size at heap-mutating ticks (cells copied if the heap is shared) | **2,820,071,476** | **1,601,140,140** |
| Σ stack length per tick (what `step`'s `List.length` walks) | 7,405,671 (max 16) | **3,600,540,107** (max 20,002) |
| Σ de Bruijn index at `bound` (environment walk) | 98,298 (env ≤ 5) | 60,000 |
| Σ record length at `field` frames (`find?`) | 262,136 | 160,008 |
| nodes renamed at `fix` / `mix` | 88 / 0 | 88 / 0 |

The environment lookups, field scans and renames are all O(1)-ish per tick. Two
quantities are quadratic: the heap copied and the stack walked.

## Where the copies come from (read: compiled C, `logs/ir-evidence-01.txt`)

1. **`step` retains the pre-state.** `ObjectiveBendDemandMachine.c:11528` contains
   `lean_inc_ref(v_state); next = stepRaw(v_state)`. So the State is shared inside
   `stepRaw`, and every `set!`/`push` on its heap copies the whole Array, including
   an RC increment of every cell. That is the 2.8·10⁹ / 1.6·10⁹ cells in the table
   above.
2. **`step` computes `List.length` of the stack every tick** (line 11548). That is
   the 3.6·10⁹ list nodes of StressCount.
3. **`stepRaw` copies even when the heap is unique.** At three push sites (the
   argument binding of a closure, the successor binding of `condition`, and a case
   arm) the code reads `state.heap.size` *after* `state.heap.push`. So the compiler
   keeps the old heap alive across the push (`lean_inc_ref(v_heap); push; get_size`,
   lines 9153/9824/10219), and the push copies. `allocateFields` does the same
   per field (line 5888, inside its fold).
4. **`forceWith` re-enters `runBounded` for one tick at a time.** Each tick
   therefore pays for (1) and (2) again. This is the path that admission
   re-execution runs (`executeWith` → `forceWith`).

## Ablation (executed: `objective-machine-diag time`, `logs/ablation-01.log`)

| mode | StressWork | StressCount |
|---|---|---|
| `stepRaw` iterated, nothing retained (only cause 3 remains) | 6,159 ms | 6,441 ms |
| the same + `List.length` per tick (causes 3 + 2) | 8,021 ms | 29,234 ms |
| `runBounded` (causes 1 + 2 + 3) | 19,950 ms | 38,318 ms |

## Conclusion

The cost is entirely in how the definitions use memory, not in the Lean
interpreter or compiler. Lean-native and the IR interpreter cost the same, which the
backends lane had already measured. The fix keeps every definition and replaces
the compiled code:

- decide capacity from the pre-state before the transition (`sizesAfter`, proved
  equal to the sizes of `stepRaw`'s result);
- carry the stack depth as a counter;
- read the heap size before the push at the four sites;
- run `forceWith` as one transition per allowance.

That is `Theory/ObjectiveBendDemandMachineFast.lean`, installed with `@[csimp]`.

## After (executed: `logs/bench-01.log`, same packets, same box)

| | specification code | fast (csimp) | C runtime (process wall) |
|---|---|---|---|
| StressWork `runBounded` | 14,885 ms | 41–43 ms | 20 ms |
| StressWork `forceWith` | 13,100 ms | 45–52 ms | — |
| StressCount `runBounded` | 37,684 ms | 36–292 ms (load) | 10 ms |
| StressCount `forceWith` | 38,130 ms | 25–40 ms | — |

`step`, called on its own one tick at a time (`stepTimes`), stays O(stack depth)
per call: StressCount takes 25–27 s, against 37.6 s for the specification code.
The `step` signature carries no depth, so it has to count the stack. No admission
path calls `step` per tick. `runBounded` and `forceWith` do not count the stack.
The one per-tick `step` caller is `ObjectiveBendEmitC.traceRun`, the
differential's fingerprint oracle.
