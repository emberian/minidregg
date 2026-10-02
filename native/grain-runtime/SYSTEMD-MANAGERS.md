# Controller and worker manager contract

A managed controller selects its manager from the root-owned registration
`/etc/mini/controllers/TASK.json`. The strict schema is:

```json
{
  "protocol": "mini-controller-registration-v1",
  "task": "8781",
  "config": "/var/lib/mini/hermes/controller.json",
  "manager": "system",
  "workerManager": "user",
  "serviceUid": 1000
}
```

`residentConfig` may name an additional canonical absolute resident config path.
The controller checks its exact task, config path and effective UID. Registration
bytes and path remain pinned for the process lifetime and are checked again at
manager operations. An explicit `MINI_GRAIN_CONTROLLER_REGISTRATION` may select an
isolated root-owned registration named `TASK.json`; it never falls back when
missing. This is host operational custody, not native budget or member authority.
Existing registrations need an explicit `workerManager` addition.

Production controllers use the system manager with the registered service UID;
workers use that UID's user manager and the existing bwrap isolation. The runtime
never probes a second manager after a failure. Manager commands use explicit
manager flags and UID-bound local bus addresses. Controller cgroup proofs retain
the canonical unit, current MainPID, recursive physical stop proof and existing
launch-gate fences. All startup, quiescence and config migration consumers share
those checks.

Both runtime and launcher expose `--controller-manager-protocol` with exact output
`mini-controller-manager-v1`. Before a cross-manager launch reserves work, the
runtime checks the launcher's protocol. Gate initialization and worker launch
receive a fresh observed controller manager/unit/MainPID/InvocationID tuple.
The lifetime gate authenticates and retains that incarnation, monitors its pidfd,
and terminates the sandbox if the controller dies. A user-worker `BindsTo` cannot
express a system-controller dependency; the lifetime gate supplies that link.
Gate fencing of retained work does not require the old controller to remain alive.

For an existing unregistered user-manager fixture, explicitly set all three:

```
MINI_GRAIN_CONTROLLER_MANAGER=user
MINI_GRAIN_WORKER_MANAGER=user
MINI_GRAIN_CONTROLLER_UNIT=mini-grain-controller@TASK.service
```

A missing registration with no fixture variables permits an unscoped runtime to
open, but cannot establish managed physical proof. A system-manager fixture must
use a real root-owned registration. Contradictory environment values refuse.

Adopting a legacy controller requires retaining and stopping its **actual** old
manager/unit and scoped worker/custody processes before registration. A new
system-unit MainPID alone does not prove orphan processes in the old user cgroup
are gone. Registration does not silently reclassify old process evidence, move
journals, change worker identities or grant native authority.

Receiving checks must include the joined runtime, root registration, exact system
unit, fresh signed quiescence and worker lifetime gate. Module tests and isolated
launcher crash probes do not alone qualify the complete service deployment.

The root launcher obtains its launch descriptor from `grain-runtime
controller-launch CONFIG ROOT_REGISTRATION`, run as the registered service UID.
The read-only command validates the actual root record and private configuration,
and returns `mini-controller-launch-v1` with exact task, unit, manager, worker
manager, service UID, runtime, configuration, transport and file hashes. Consumers
pass `environment` unchanged; the registry variable is
`MINI_GRAIN_CONTROLLER_REGISTRATION`. Producer and runtime consumer share the
same source constants. A projection launches nothing and grants no native room,
account or allowance authority.

Qualify the actual service scope after registration. On the receiving host, a
user-manager filesystem namespace activated by credential `ReadWritePaths`
remapped root-owned archive metadata; a direct registrar check did not qualify
that launch. The joined protected controller uses an actual system service with
its registered service UID and separately managed user workers. Both launcher
components must expose the exact controller lifetime protocol used by the runtime.

Launch readiness also queries the configured native Mini `operator-status`.
Its current owner-private control endpoint must return `mini-operator-drain-v1`
serving with open admission, positive Mini/Host process identities and exact
Host/config hashes. The native CLI verifies the fresh response nonce and peer
custody. A descriptor naming an operator socket or a filesystem mode cache is
not enough: public-mode `mini serve` can admit some signed work while refusing
later private provider settlement. Source controllers use `mini serve-operator`
and repeat this read-only check before resident work starts.

The protected registration may include optional `roomRouting` operational intent:
`{"workspace":"/canonical/member/workspace","roomCell":"99","inboxRoot":"/canonical/private/inbox"}`.
Paths must be canonical absolute paths, and roomCell a nonzero canonical u64
decimal. `controller-launch` projects it unchanged. It does not assert a current
assignment, recipient, account custody or controller liveness. Activation must
still consume the native registration/current-assignment selector and its fresh
signed room/grant/account evidence; a private advisory pointer is not authority.
