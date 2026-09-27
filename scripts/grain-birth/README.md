# Grain-backed resource birth acceptance

`native-acceptance.sh` creates a fresh Mini Store, new controller/tool keys, and
parent/tool grains 7901/7902. It then submits one worker-authored composite birth
for a previously absent content object 8301. The worker's already reserved
permission budget settles in the same native transaction as the birth, Book
fee, current parent-generation witness, and owner/control grant creation.

The script exact-hash guards `scripts/workroom/provision.sh` and makes a private
copy with an independent grain-birth permission tariff and an installed factory
law: owner 7 may use bare birth; worker 8 may observe the factory with its
observe grant and may birth only through the `birth/mode/grain-backed`
projection. A worker bare-birth attempt must reach
native admission and receive the exact policy rejection. A matching owner-7
bare content birth must succeed under the same enabled profile. The original
workroom provisioner creates an
unrelated content object 8001; 8301 is absent until the composite receipt.

Run only with a source-matched composite native Host and compatible Mini,
Store, and signature binaries. The output directory must not exist. It retains
private keys and the complete Store; keep it private and curate bounded public
evidence separately.

```sh
MINI=/path/to/mini \
STORE_BINARY=/path/to/minidregg-link-sqlite-store \
SIGNATURE_BINARY=/path/to/minidregg-credential-signature-verifier \
sh scripts/grain-birth/native-acceptance.sh /path/to/minidregg-host /new/private/evidence
```

This is a native signed semantic gate. A separate Hermes/MCP run must prove
tool use from an actual hosted worker. Sharing the born resource still requires
a later signed delegation; it is not part of the birth CAS.
