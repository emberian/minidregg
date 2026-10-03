# Experimental Mini IR2 proof harness

This is an offline conformance and privacy-regression harness, not a world proof-admission endpoint. It consumes the actual Lean-emitted local-row IR2 subset through Bread's existing parser, prover and verifier. No source/controller correspondence or complete zero-knowledge/security bound is claimed.

Run `python3 provision.py /absolute/path/to/isolated/breadstuffs` to generate the standalone Cargo manifest. The isolated Bread source must retain its exact root metadata and its pinned `vendor/plonky3-fri-82cfad73` and `vendor/plonky3-challenger-82cfad73` patches. Provisioning does not edit or build Bread. The sibling `bend-proof-entropy` crate supplies OS-seeded cryptographic streams with shared clone state and post-fork refusal.

Build only in a leased, capped remote lane. The exact current harness passed `cargo check --tests` on Persvati with jobs=2 and 8 GiB memory. The actual proof regression still awaits Lean-emitted fixtures; compilation is not evidence that the disclosure succeeds.

`Host/BendTraceIR2Emit.lean` emits one descriptor, two valid witnesses with identical public inputs and different private bits, and a tampered-public vector. Set `BEND_IR2_FIXTURE` to that directory, then use the narrowly filtered release nextest `raw_one_row_hiding_proof_reveals_trace_coefficients`. It exercises the raw backend's one-row shape without modifying any production guard. The test verifies both proofs and attempts recovery using only a public extension-field opening and transcript.

The CLI `prove descriptor.json public.csv trace.csv proof.bin` and `verify descriptor.json public.csv proof.bin` restrict descriptors to the emitted local-row grammar and require a fixed 256-row main trace. That excludes the immediate degree-one counterexample; 256 is an experimental parameter, not a derived zero-knowledge budget. Full FRI, quotient and masking analysis remains open. Public vectors must eventually be derived independently from the exact authorized source/input/result/effects/charge/context; this CLI is not that receiver.
