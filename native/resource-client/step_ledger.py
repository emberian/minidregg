"""Retained single-effect step ledger shared by world adapters.

A ledger lives inside a caller-owned JSON state object and is persisted by the
caller's own `persist` callback before and after every step. Each step holds at
most one native effect.

- A completed step never repeats.
- A reentrant step's native consumer owns its exact journal, so entering it
  again resumes or refuses by itself.
- Any other interrupted step fences every later step. It is continued only by
  its own `recover` decision (an exact lookup or a signed read reporting the
  effect `done` or definitely `absent`), or by an operator `settle` that cites
  retained evidence. Nothing is authored again by default.

Used by scripts/spk-platform/ws-continuity-fixture.py (app attachment and the
document connector) and native/resource-client/composed-scenario.py.
"""
import threading


class LedgerFenced(RuntimeError):
    """An interrupted step must be recovered or settled before anything else."""


def _require(condition, message, error=RuntimeError):
    if not condition:
        raise error(message)


class StepLedger:
    def __init__(self, state, persist, key="steps", lock=None):
        self.state = state
        self.persist = persist
        self.lock = lock or threading.RLock()
        with self.lock:
            self.value = state.setdefault(key, {"done": [], "pending": None, "settled": []})
            self.value.setdefault("settled", [])

    def done(self, name):
        return name in self.value["done"]

    def result(self, name, default=None):
        return self.value.get("results", {}).get(name, default)

    def pending(self):
        return self.value["pending"]

    def step(self, name, action, evidence, reentrant=False, effect_only=False,
             recover=None, keep=False, before=None):
        """Run `action` once as step `name`; True if it ran (or was recovered).

        `evidence` names where this attempt retains its artifacts. `before` is
        a small JSON value retained with the pending attempt (for example the
        attempts that existed before it) that `recover(pending)` may use. With
        `keep`, the action's JSON result is retained and later returned by
        `result(name)` without running the action again.
        """
        with self.lock:
            if name in self.value["done"]:
                return False
            pending = self.value["pending"]
            if pending is not None and pending["name"] != name:
                raise LedgerFenced(f"step {pending['name']} is unsettled; inspect {pending['evidence'][-1]} before {name}")
            if pending is not None and not (pending["reentrant"] and reentrant):
                if recover is None:
                    raise LedgerFenced(f"step {name} is unsettled; inspect {pending['evidence'][-1]} and settle it from evidence")
                verdict = recover(pending)
                decision = None if verdict is None else verdict[0]
                pending.setdefault("recoveries", []).append(
                    {"decision": decision, "evidence": None if verdict is None else verdict[1]})
                if decision == "done":
                    self._complete(name, verdict[2] if keep and len(verdict) > 2 else None, keep)
                    return True
                if decision != "absent":
                    self.persist()
                    raise LedgerFenced(f"step {name} has an undecided outcome; retained {pending['evidence'][-1]}")
                pending["evidence"].append(str(evidence))
                if before is not None:
                    pending["before"] = before
            elif pending is not None:
                pending["evidence"].append(str(evidence))
            else:
                self.value["pending"] = {"name": name, "reentrant": bool(reentrant),
                                         "effectOnly": bool(effect_only), "evidence": [str(evidence)]}
                if before is not None:
                    self.value["pending"]["before"] = before
            self.persist()
        value = action()
        with self.lock:
            self._complete(name, value, keep)
        return True

    def _complete(self, name, value, keep):
        if keep:
            self.value.setdefault("results", {})[name] = value
        self.value["done"].append(name)
        self.value["pending"] = None
        self.persist()

    def settle(self, name, disposition, evidence, reason, root, write_record, confirmed=None, sha=None):
        """Settle an interrupted step from its retained evidence.

        `absent`: the cited artifact shows the attempt made no effect (a
        definite refusal, or a failure before any submission); the step is
        authored again. `confirmed`: the cited artifact is a native confirmation
        of an effect-only step (one that leaves no adapter-side result), which
        `confirmed(path)` must accept; the step is complete. Anything else stays
        fenced for exact native recovery.
        """
        with self.lock:
            pending = self.value.get("pending")
            _require(pending is not None and pending["name"] == name, "no such unsettled step")
            _require(disposition in ("absent", "confirmed"), "settlement disposition must be absent or confirmed")
            _require(evidence.is_file() and not evidence.is_symlink() and evidence.is_relative_to(root),
                     "settlement evidence must be a retained file under this evidence root")
            _require(any(evidence.is_relative_to(attempt) for attempt in pending["evidence"]),
                     "settlement evidence belongs to another step's attempts")
            _require(isinstance(reason, str) and 0 < len(reason) <= 400, "settlement reason required")
            if disposition == "confirmed":
                _require(pending.get("effectOnly") is True,
                         "this step leaves adapter results; a confirmed attempt needs exact continuation, not settlement")
                _require(confirmed is not None and confirmed(evidence),
                         "confirmed settlement requires the retained native confirmation")
            record = {"type": "mini-spk-step-settlement-v1", "step": name, "disposition": disposition,
                      "attempts": pending["evidence"], "evidence": str(evidence),
                      "evidenceSha256": sha(evidence) if sha else None, "reason": reason}
            path = write_record(record)
            self.value["settled"].append(str(path))
            if disposition == "confirmed":
                self.value["done"].append(name)
            self.value["pending"] = None
            self.persist()
            return record
