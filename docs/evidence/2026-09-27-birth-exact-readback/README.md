# Ordinary birth exact readback: source gate

This cut extends the persistent Host's existing exact-CAS path to ordinary resource births. Before the cut, `submitVerifiedLoadedWith` used that path only for `.invoke`. A fresh `.birth` went through `ResourceBirthReceiver.receiveLoaded`; after confirmation, `Host.Main.sessionConfirmed` refreshed the changed image and `NativeHostReplay.extendVerified` re-admitted the just-installed birth. The change retains the first complete `AcceptedBirth` and uses the receiver's full-byte-equal CAS readback to extend the verified tip. Grain-backed births keep their existing route. Historical ordinary births still pass `ResourceBirthReceiver.replay` before any fresh admission. Nonexact, concurrent, uncertain, and rejected results retain the prior reopen/confirmation behavior and birth-specific rejection encoding.

Changed source files, SHA-256:

| File | SHA-256 |
| --- | --- |
| `Kernel/NativeHostReplay.lean` | `b79fec6992e600cfb0c8e307b25193b14eb5537dcb433260756e3a27d3313acd` |
| `Kernel/NativeHost.lean` | `3f8a2828abde5e8d79963995b2625a03792750c995727f0d2cbedff5c3f8e697` |

The new `Derived.ofBirth` accepts only the typed `AcceptedBirth` from native policy and signature admission. Named `ofBirth_intent` and `ofBirth_admission` facts pin its intent and admission variant. The existing `ExactReadback` requires the receiver's `Ready` and `prepare` equality, complete physical readback bytes equal to the prepared candidate, `validateLoaded` on that candidate, and exact original-prefix receipt selection. `extendExact` then appends this one admitted step. Neither a caller-supplied intent nor a digest-only readback can construct that path.

Direct Lean checks used a private writable overlay `/home/ember/build/minidregg-birth-exact-overlay-20260927` over the immutable exact `cb55b81` source/OLean base `/home/ember/build/minidregg-cb55b81-native-20260927` on Persvati. `Kernel.NativeHostReplay` and then `Kernel.NativeHost` both exited 0. Their OLean SHA-256 values are `0ceeedcc3dbc247c72bd330456ba9343d6fd22796e59e6114ad5c8ee0525d622` and `932543058f59e23e15ce09f040a31d2609c141888b172c9d41177ade6bbf0814`. The logs contain only existing axiom reports; `Probe.log` reports `[propext, Classical.choice, Quot.sound]` for the two new projection facts. This is a source/type gate, not a full native build or runtime result.

The deployment gate remains one retained ordinary birth on a copied pre-birth Store: compare original and changed Host outcomes and all four receipt fields, exact post-Store bytes, and cold exact-call lookup after reopening. Time fresh admission, CAS/readback, and post-confirmation session refresh separately. Exercise a nonexact/concurrent or uncertain result to ensure it still follows read-only recovery without minting an exact tip. No live r3 Store is part of this source gate.
