# Launch-bound native receiver source checkpoint (2026-09-27)

These new modules were compiled serially in the independent hbox overlay `/tank/dregg-build/minidregg-55d3868-launch-v2-narrow`, over the committed typed v3 Replay source (commit `a2cce78`, SHA-256 `2a1bdafde58aef3aa5c8cbc8c9902abeea23309a6f5b8f62d99db2b628426ea2`) and the immutable prefix-292 dependencies. The three direct `lake env lean -o .lake/build/lib/lean/Kernel/MODULE.olean Kernel/MODULE.lean` checks exited 0 under one atomically claimed seat with `LEAN_NUM_THREADS=2`. Each corresponding `/tmp/mini-v3-MODULE.log` is empty (SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`).

| Module | Source SHA-256 | OLean SHA-256 |
| --- | --- | --- |
| `ApplicationLifecycleBeginV3Receiver` | `85a383fb32d78cf97a7b658c7b19b5325b6c6cc9031d0d9e09762fc7bc202312` | `c4647ed223f0338ab7496a72ea065d570c932e0a2755e4be05f3cb415924d63d` |
| `ApplicationLifecycleClaimV3Receiver` | `2e6f6673178df1b15264bbc3efe93a3608d77a7eb739a0e5a6241ed4eeda02c7` | `5e7bdf207acdf403c1f19497d3f58fec6852e350cbf1b7065d92b819c47eda76` |
| `ApplicationLifecycleCompletionV2Receiver` | `7cbcc0d0c7d6193698da4f0594362209f8432cc2b0839f057fc6529f2338f735` | `8e4e57bca8a884ecb1b69ddde46f0497cf231393fc8a6b6e1b874c00019f5b24` |

Each receiver decodes its own versioned ingress, uses the `Verified` current-tip admission (which joins the original event23/24/25 history), rejects reused transaction identity, submits one durable intent, and confirms only an exact post-CAS byte readback validated as a successor image. BEGIN is pending work; claim reservation is not a physical process assertion. Claim's `withFreshTip` rechecks the exact physical image immediately before handing its source-owned v3 projection to a caller.

This is a Lean source check. No linked Host op66–71 route, full native image, process launch, or resident host acceptance is claimed. The physical consumer must compare the complete v3 projection and preserve a one-shot launch journal; historical receipt lookup cannot perform the physical effect again.
