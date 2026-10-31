# Coherent Rust host in the existing Mini package

`rust-host-package.py` creates a fresh stage from a pinned, verified existing
Oracle stage and `veri7vn/tools/appliance/package_host.py` distribution. It keeps
the signed manifest, Mini bridge, public-data declaration and source mappings.
The fixed launcher starts the distribution's Rust host and the existing fd3
bridge. Only that bridge receives the supervisor descriptor. The old adapter
source remains packaged but is never started. Rust owns request state and the
Engine worker; the existing Mini gateway still supplies authenticated tenants.

## Build the U8 source stage first

The Rust distribution's Engine receipt must be the U8 materialization at
`/Users/ember/dev/o7vn/var/appliance-20261029/candidate-u8/APPLIANCE.json`,
SHA-256 `97286fb824bb102a24ac9e7458fc8d8426212ad0bff2b585bd00d6e0462d00a5`.
Its recorded source revision is `c473d28914e480425adb29b4f7f42485b8cfb4e3`.
The retained v7 stage points to U7 and cannot admit this distribution. Reuse its
rootfs and bridge bytes, then build a **new U8 stage** so the full U8 source
closure and exact receipt enter the signed package. Do not substitute the old
U7 receipt or bypass a receipt mismatch.

Run from the Mini repository with a new output directory. `RUST_PAYLOAD` names
the prepared Linux distribution and `RUST_MANIFEST_SHA256` its separately
reviewed manifest digest. The existing source selection is applied to the U8
receipt; a missing or changed selection must be resolved explicitly.

```sh
O7=/Users/ember/dev/o7vn
OUT="$O7/var/mini-rust-u8-20261031"
mkdir "$OUT"
U8="$O7/var/appliance-20261029/candidate-u8"
U8_SHA=97286fb824bb102a24ac9e7458fc8d8426212ad0bff2b585bd00d6e0462d00a5
ROOTFS="$O7/var/oracle-shared-20261027/linux-inputs-v5/rootfs"
ROOTFS_LOCK="$O7/var/oracle-shared-20261027/linux-inputs-v5/rootfs.inventory.json"
ROOTFS_SHA=0d97d99485b4bd33d154e8a29c13f025a6c621b41b369dde41fac0f7f086ee6b
BRIDGE="$O7/var/oracle-runtime-v7/stage/image/opt/oracle-bin/minidregg-oracle-appliance"
BRIDGE_SHA=11cb93bcf78fcb4d984e619c21b5311cea6acb00507f4a5053f33014a9776219
APP_ID=ephaf4h4cx8f9s36hmukm4yzkznyhqjhvj8efp3at9cru2zn10mh
python3 -B deploy/oracle/stage.py data-inventory \
  --appliance "$U8" --appliance-sha256 "$U8_SHA" \
  --selection deploy/oracle/data-selection-v7.json --out "$OUT/data-inventory.json"
```

Review and pin the new inventory digest as `DATA_SHA`, then continue. This
inventory concerns U8 even if its public files match an earlier revision.

```sh
python3 -B deploy/oracle/stage.py stage \
  --rootfs "$ROOTFS" --rootfs-manifest "$ROOTFS_LOCK" --rootfs-sha256 "$ROOTFS_SHA" \
  --appliance "$U8" --appliance-sha256 "$U8_SHA" \
  --bridge "$BRIDGE" --bridge-sha256 "$BRIDGE_SHA" \
  --data-inventory "$OUT/data-inventory.json" --data-sha256 "$DATA_SHA" \
  --app-id "$APP_ID" --version 8 --target "$OUT/u8-base"
python3 -B deploy/oracle/stage.py verify "$OUT/u8-base"
```

Review and pin `$OUT/u8-base/STAGE.json` as `U8_BASE_SHA`. Version 8 here is a
new package input, not a claim that a signed version 8 already exists. The
operator's signing key must match `APP_ID`.

## Add the Rust payload and native image

Create an explicit operator JSON path map. Map the distribution's exact Engine
checkout path to `/opt/oracle`, its admitted regular Python executable to
`/usr/bin/python3.12`, and its exact native image path to
`/opt/oracle-resources/native-image`. For example, using the actual paths from
`host.template.json`:

```json
{
  "/Users/ember/dev/o7vn/var/appliance-20261029/candidate-u8": "/opt/oracle",
  "/operator/linux-rootfs/usr/bin/python3.12": "/usr/bin/python3.12",
  "/operator/immutable/native-image": "/opt/oracle-resources/native-image"
}
```

Save the reviewed map as `$OUT/path-map.json`. The Python hash must match the
regular executable in the pinned rootfs; a virtualenv alias cannot stand in
for a different interpreter. Public files use Mini's `/opt/oracle-data` mount.
Every external file must match the base stage's exact hash or public inventory.

For the native image, supply `$OUT/resources.json` with its exact source and
reviewed digest:

```json
[{"path":"/operator/immutable/native-image", "sha256":"REVIEWED_SHA256", "destination":"/opt/oracle-resources/native-image"}]
```

The adapter checks that hash, copies the image into the fresh stage, and adds
it to the exact signed inventory. Resources cannot overwrite existing members
or use other destination directories. A host path is never mounted automatically.
The host's writable journal and workers use the grain's private
`/var/oracle-host`.

```sh
python3 -B deploy/oracle/rust-host-package.py \
  --stage "$OUT/u8-base" --stage-sha256 "$U8_BASE_SHA" \
  --payload "$RUST_PAYLOAD" --payload-sha256 "$RUST_MANIFEST_SHA256" \
  --path-map "$OUT/path-map.json" --resources "$OUT/resources.json" \
  --target "$OUT/u8-rust"
python3 -B deploy/oracle/stage.py verify "$OUT/u8-rust"
NEW_STAGE="$OUT/u8-rust"
```

The Linux clingo executable needs `libstdc++`, `libm`, `libgcc_s`, `libc` and the
ELF loader; it has no `libclingo.so` dependency. The Rust host needs `libgcc_s`,
`libm`, `libc` and the loader. These are system-library requirements for the
pinned Linux rootfs, alongside the already required Engine Python environment;
there is no new separate clingo shared-library installation step. Check the
actual selected executables inside that rootfs before signing.

Pin the new `STAGE.json` digest. This combined runtime exceeds the standard
aggregate package budget: select the operator profile explicitly for signing,
independent inspection and the operator-owned import configuration. The packer
default remains `standard-v1`. Both profiles retain the individual member limit
below 512 MiB, exact hashes, signing identity and no-overwrite publication.

```sh
"$PACKER" pack "$NEW_STAGE" "$REVIEWED_STAGE_SHA256" "$PRIVATE_KEY" "$NEW_RUNTIME_SPK" \
  --profile operator-appliance-v1
python3 -B deploy/oracle/stage.py verify-package \
  --stage "$NEW_STAGE" --stage-sha256 "$REVIEWED_STAGE_SHA256" \
  --inspector "$INSPECTOR" --inspector-sha256 "$INSPECTOR_SHA256" \
  --package "$NEW_RUNTIME_SPK" --scratch "$PROTECTED_DISK_SCRATCH" \
  --profile operator-appliance-v1 --out "$NEW_POST_PACK_RECEIPT"
```

The operator profile reuses Mini's existing 8 GiB raw and 20 GiB decoded limits;
the packer's receipt records the selected profile. Mini's operator-owned broker
configuration must select `importProfile: "operator-appliance-v1"`. A package or
caller cannot select that broker policy. The packer buffers member bytes,
archive and compressed output in memory, so assembly needs a dedicated machine
with enough memory for several copies of the actual closure; the format ceiling
is not a promise that a small host can pack the largest admitted archive.
Use the remaining operator import and shared-data publication commands in
`README.md`. The Rust
payload must contain a Linux x86-64 host and matching external artifacts; the
Linux rootfs still needs the production Engine's Python dependency closure.
Signing needs the operator's existing private key, the Linux packer and independent
inspector, protected disk scratch, and the published inventory. None is created
by this adapter. A signed package and actual Mini receiving/lifecycle journey
remain required; source checks do not establish either.

Focused check for the central runner:
`python3 -B -m unittest discover -s deploy/oracle -p test_rust_host_package.py`.
