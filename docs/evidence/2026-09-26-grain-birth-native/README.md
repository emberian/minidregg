# Grain-backed birth: retained pre-submit findings

These are two **failed, fresh** native runs, not accepted resource births.
Each used a separate private Store and fresh keys. The source-matched Linux
Host was SHA-256
`c6c21859e54b3ef96e0ff60b345ef705a6b3e359345a26894fd054aa248c5a`
(181/181 Lean modules and native link); its source manifest was SHA-256
`d856d411b8e066ecc7cccaf09852c4909daa67fbf78060da2952ff1ad5a5e042`.
The source and Store, keys, complete challenges, attempts and logs remain
private under `/tmp/grain-birth-native-acceptance-20260926/` on Persvati.

| Run | Script SHA-256 | Retained native result | Meaning |
| --- | --- | --- | --- |
| r1 | `f391878e004aaf20a2f0ba9c4af139e4344b42c6820e5a7018ace3fa75d39855` | `prepare` returned `observation refused` | The first fixture factory law required the composite mode even for worker factory observation. This diagnosis follows from the installed predicate and source observation request; the public refusal deliberately does not reveal which grant failed. No composite call was assembled. |
| r2 | `eb861f9d786fa597d51ad2d8048b42241e55c37b462f2294d4e110a4fdd2e45d` | `prepare` returned `grain-backed tuple preparation: … Reject.grantTemplate` | The revised factory law admitted observation. Structured birth authoring had stamped newborn grants at genesis height 10, while the retained signed challenge had current logical height 20. Native `TemplateBound` refused the proposed grants before a composite call was assembled. |

Each run's `observation-summary.json` selects only height, image boundary and
the four exact observation grants from the retained challenge. Its
`pre-submit-refusal.json` is the Mini client's retained failure manifest. No
private key, complete source intent, Store, or live configuration is copied
here.

The source fix adds an optional structured `birth.height` sourced from a prior
signed current observation. It generates owner and control grants with
`notBefore = height` and `notAfter = height + template.lifetime`; the native
receiver still checks that height against its current image. Omitted height
retains legacy genesis-height authoring. The general
`birthRootCapability_time_window` theorem and `lake build Host.Json` passed in
the independent Persvati snapshot, log `/tmp/grain-birth-host-json-height.log`
(SHA-256 `b7f13027a7525cb9ada3a5ffd8ae1f2ed5e91ff7b0928d9c3ddaf10d8cd368a0`,
final line `Build completed successfully (3109 jobs).`); fixed source SHA-256 is
`31f400a1d483e0e9fb400fd5a2790f0cfdb497dc5ab9b4f6a2d989a22d863a06`.
No successful r3 or hosted Hermes result is claimed by these artifacts.
