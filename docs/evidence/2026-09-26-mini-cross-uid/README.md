# Mini Host through two Unix accounts, persvati, 2026-09-26

This is a fresh, independent Store and signed four-principal provision under
`/tmp/mini-cross-account-signed-20260926-r1`. It did not use or modify the
running owner demo or hosted 7801/7803 Store. The provision was produced by
`scripts/workroom/hosted-provision.sh` from a private copy and completed in a
bounded 2-CPU, 8-GiB user service (4m40s). Its empty content8001 root was
`97349327118568466779609446662939988221287696762075284738918673226692685974561`.

The operator ran one private `mini serve` and two separate operator-owned
[`host-frontend`](../../../deploy/grain-host/host-frontend.rs) processes. The
private Host socket and Store were under 0700 operator directories. Public
socket/config directories were separate for UID 65534 (`nobody`) and UID 1
(`daemon`); each frontend granted only its named UID ACL traverse, config read,
and socket connect. Each UID had only its own copied tool key and a 0700
attempt directory. These existing system accounts were used for this native
transport gate; they were **not** offered a grain controller, Hermes session,
SSH key, or user manager.

Pinned executable/source identities:

- Certified Linux Mini Host `d413081bb6c6ac1c0699b5fdc22cf3a13fb87930ff49ac147ae994e2c364e7a3`.
- Linux `mini` from committed `d52077e` (ordinary socket v2), executable `fee5bc861d74c9e432db2374ede36b62852a80346a46f1dc89133dfa79bf11eb`, source `main.rs` `ea9990db`, `transport.rs` `4b223ae0`, `meter.rs` `06041295`.
- Frontend source `d4f8941256185eb2745517e4aac1814e78a76b27763f701a37c3dd2dfbf3c7d7`, Linux executable `0675e61e6ae9517439f2eec29fa8c740c069f9f1f52e25e84ba463e6192140dd`.
- Frontend probe source `7c3ac797ef02e626b19cf2527817ff28e1818989e263cee5d04bea53abec5918`.

The final frontend source passed Linux `rustc -D warnings` and two unit tests.
The lock and unknown-connect adversarial checks were run on an earlier
prototype, source SHA `455a5a6ef2166e0be34ae76ae38facbd7a464618c3c321eb495fe56c880c96a3`
(ELF `600e90ee...`): a second instance refused its service lock without
changing the first socket inode or ACL, and an existing socket with a
non-refusal connect error was not unlinked. Hostile default-ACL removal and the
10,008-ms one-byte frame deadline were run on the later source SHA `d419f6f4...`
(ELF `2ca89a3b...`). Pinned v2 op255 returned a frontend refusal. These
adversarial observations were not repeated on final SHA `d4f89412...`; final
source retained those paths and was directly exercised by the signed native
operations below. The previous ordinary client sent v1 and was correctly
refused **before forwarding**. The signed result used fixed d52077e client,
with no v1 fallback.

Signed native observations through the two task-specific sockets:

1. UID 65534 used subject8/cap96 and UID 1 used subject10/cap98 to read the
   same empty content8001 root.
2. UID 65534 used cap95 to create atom7401; native accepted count10. UID 1
   signed-read the resulting root
   `50285950846470776696093012463001984693164252299238213771378138103374475932470`.
3. UID 1 used cap97/98 to edit that atom; native accepted count11. Both
   independently signed-read final root
   `114747236347917914506268887728013117709482223438691102631235357426231257003243`.
4. Subject8 trying subject10's cap98 and subject10 trying subject8's cap96
   each received a signed `observation refused`, with no view file. Neither
   task UID could read the other's key/config or traverse the operator Store
   and private pinned config.

[`a-create-outcome.json`](a-create-outcome.json) and
[`b-edit-outcome.json`](b-edit-outcome.json) retain the exact native confirmed
receipt fields (`transactionId`, `eventId`, `acceptedCount`, `imageBoundary`)
plus status. [`safe.log`](safe.log) records executable hashes, signed roots,
outcome and final signed-view file hashes, ownership and physical service PIDs
without keys or Store contents. Its SHA-256 is
`6410597629f9eb7819ffe5350343f03abf592accc4ed1a9270671bbcfe4e2860`.
The exact scratch operation and privacy commands are retained as
[`operation.sh`](operation.sh) and [`privacy.sh`](privacy.sh); they contain
fixture-specific absolute paths and no credentials. This result proves
separate Unix accounts can reach one private Mini Host through per-UID
frontends and that these particular signed grants were enforced. It does not
prove task-account controller/Hermes launch, per-tenant backend availability,
or cancellation of a native operation after the frontend forwards it.
