# V3 physical report and completion consumer (component cut)

The Rust host now asks Mini to author and inspect the exact V2 physical report for an event23 BEGIN and event24 committed claim. INSTALL supplies a materialized image with no running process or volume witness. START supplies a live `hostd` unit and the root-attested persistent volume witness; the host compares operation, unit, invocation, cgroup, PID, image, source volume ID, and retained claim, then rechecks the live observation before signing Mini's exact frame with the separately pinned physical custodian. It inspects the signed report before passing it to op70/71.

The event25 consumer retains the exact assembled ingress and one-shot op38 submit marker. Fresh `installed` outcome is distinct from read-only op39 `replayed` recovery. Both receipts require canonical decimal acceptedCount strictly after the retained event24 claim, without `u64` conversion. Submit borrows its handle; recovery can also reload the exact protected attempt after process restart. Recovery returns a historical-only type and never submits op38 or authorizes a launch. This component does not yet retire the lifecycle marker; the physical caller must perform the source-confirmed successful transition.

Source files and SHA-256 at this gate:

```text
86a7e5430c40493d5b6beda430248f5d693eab9232f18089d06a0a8010049c26  native/spk-host/src/hostd.rs
5ba2d865da7631da11f21d754f1b0184347dccda0b338ee334927e37dee6e40e  native/spk-host/src/lib.rs
3d79881a5805636f564e1b3bfb95167b21b7398d63c42ba61c9f73795888bbb3  native/spk-host/src/lifecycle_v3_claim_native.rs
d365e9b668d41bf441a877a9c604039f11a981695e93959bf3ed7ff995fefe53  native/spk-host/src/lifecycle_v3_completion_native.rs
4d8587a1f7324a52847debc7ef305b246e20f8aa369be7f0be0e6808f529b9a5  native/spk-host/src/lifecycle_v3_report_native.rs
```

Isolated hbox snapshot `/tank/dregg-build/mini-spk-v3-agent/native/spk-host`, 2 Cargo jobs, 4 GiB memory cap: [focused.log](focused.log) 11/11 scoped tests, SHA `36c7a5174f5989c7d980f550a74259990a72b79961afbbd642c5f750b3a1bbac`; [clippy.log](clippy.log) strict all-targets Clippy PASS, SHA `7217f4e2245d3448df28df2c69e184d1ad67cb2060196144d2c081be3cfd2cc4`.

This is a component gate. No source-matched linked Host/Store, INSTALL or START public invocation, STOP transition, or physical acceptance fixture has run. Resident INSTALL/START guards remain closed.
