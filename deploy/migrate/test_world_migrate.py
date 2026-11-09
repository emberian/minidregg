"""deploy/migrate/test_world_migrate.py: world-migrate's comparison on two small captures (python3 -m pytest)."""
import copy
import importlib.machinery
import importlib.util
import pathlib

_path = pathlib.Path(__file__).with_name("world-migrate")
_loader = importlib.machinery.SourceFileLoader("world_migrate", str(_path))
_spec = importlib.util.spec_from_loader("world_migrate", _loader)
wm = importlib.util.module_from_spec(_spec)
_loader.exec_module(wm)


def world(sponsor="7"):
    def say(author, text, h):
        return {"author": author, "kind": "say", "text": text, "to": None, "re": None, "status": None, "height": h}
    lobby = {"founder": "100", "topic": None, "pin": None, "members": ["100", "300"],
             "entries": [say("100", "welcome", 5), say("300", "hello everybody", 90)]}
    return {"sponsor": {"subject": sponsor, "balance": 10}, "agents": {"lobby-hermes": {"subject": "900"}}, "members": {
        "house": {"name": "house", "workspace": True, "subject": "100", "publicKey": "aa", "balance": 50,
                  "refs": {"lobby": {"kind": "object", "created": True}, "welcome": {"kind": "object", "created": True}},
                  "rooms": {"lobby": copy.deepcopy(lobby)}, "stories": {},
                  "documents": {"welcome": {"lines": [{"text": "# Welcome", "author": "100", "struck": False, "marks": []}]}},
                  "cells": {}, "attempts": {}},
        "ember3": {"name": "ember3", "workspace": True, "subject": "300", "publicKey": "cc", "balance": 340,
                   "refs": {"lobby": {"kind": "object", "created": False}, "research-consent": {"kind": "object", "created": True}},
                   "rooms": {"lobby": copy.deepcopy(lobby)}, "stories": {"tale": {"role": "player", "look": "The hallway"}},
                   "documents": {}, "cells": {"research-consent": {"declaration": ["1"], "entries": {"1": "1"}}},
                   "attempts": {"create-research-consent": {"acceptedCount": 80}}}}}


def kinds(items):
    return sorted((i[0], i[1], i[2]) for i in items)


def test_the_same_world_under_new_ids_has_no_difference():
    a, b = world(), world(sponsor="7")
    # every id the comparison must see through: the room's founder and members, each author, the agent
    for m in b["members"].values():
        m["rooms"]["lobby"]["entries"][0]["height"] = 1005
    b["agents"]["lobby-hermes"]["subject"] = "901"
    assert wm.diff(a, b) == []


def test_a_lost_message_a_changed_cell_and_a_short_balance_fail():
    a, b = world(), world()
    for m in b["members"].values():
        m["rooms"]["lobby"]["entries"].pop()          # ember3's say did not carry
    b["members"]["ember3"]["cells"]["research-consent"]["entries"]["1"] = "0"
    b["members"]["ember3"]["balance"] = 333
    bad = wm.failing(wm.diff(a, b))
    assert kinds(bad) == [("balance", "ember3", "balance"), ("cell", "ember3", "research-consent"),
                          ("messages", "ember3", "lobby (by ember3)")]


def test_a_renumbered_subject_is_an_id_and_the_seed_accounts_content_is_informational():
    a, b = world(), world()
    b["members"]["house"]["documents"]["welcome"]["lines"][0]["text"] = "# Welcome to Mini"
    for m in b["members"].values():                    # house renumbered: every reference to 100 follows
        for e in m["rooms"]["lobby"]["entries"]:
            e["author"] = "101" if e["author"] == "100" else e["author"]
        m["rooms"]["lobby"]["founder"] = "101"
        m["rooms"]["lobby"]["members"] = ["101", "300"]
    b["members"]["house"]["subject"] = "101"
    b["members"]["house"]["documents"]["welcome"]["lines"][0]["author"] = "101"
    items = wm.diff(a, b)
    assert kinds(items) == [("document", "house", "welcome"), ("id", "house", "subject")]
    assert wm.failing(items) == []


def test_an_addition_is_reported_but_is_no_loss():
    a, b = world(), world()
    b["members"]["ember3"]["refs"]["feedback"] = {"kind": "object", "created": False}
    items = wm.diff(a, b)
    assert kinds(items) == [("ref", "ember3", "feedback")] and wm.failing(items) == []
    assert "added by the new world" in wm.render(items)


class FakeShell:
    """The member lines carry_grains sends, answered as the worker would: an install is undecided until its
    exact retry; the carried grain is listed from its route phase on and runs only once START completes."""

    def __init__(self, start_after=1):
        self.lines, self.listed, self.running, self.shares = [], False, False, []
        self.start_after, self.retries = start_after, 0
        self.share_undecided, self.renewed = False, 0

    def __call__(self, name, line, check=True):
        import json
        self.lines.append((name, line))
        req = "ab" * 16
        if line.startswith("apps install"):
            self.listed = True
            return 1, "", f"undecided: install request {req} was accepted"
        if line.startswith("apps retry"):
            self.retries += 1
            self.running = self.retries >= self.start_after
            return (0, f"request {req}: installed", "") if self.running else (1, "", f"undecided: request {req} starting")
        if line.startswith("apps list"):
            grains = [{"grain": "a2", "owner": "house", "appId": "app", "class": "S", "state": "running",
                       "routes": ["house"] + self.shares, "carriedFrom": "a1", "carriedImageSha256": "e" * 64}] if self.listed else []
            return 0, json.dumps({"receipt": {"grains": grains}}), ""
        if line.startswith("apps status"):
            return 0, json.dumps({"state": "running" if self.running else "never-begun"}), ""
        if line.startswith("apps share"):
            self.shares.append(line.split()[3])
            if self.share_undecided:
                return 1, "", "undecided: the route is bound but not enrolled; exact retry: mini apps renew"
            return 0, "{}", ""
        if line.startswith("apps renew"):
            self.renewed += 1
            return 0, "{}", ""
        raise AssertionError(line)


def carry_dir(tmp_path, claimed=None):
    import json
    d = tmp_path / "migrate"
    d.mkdir()
    before = {"members": {"house": {"grains": {"a1": {"appId": "app", "class": "S", "shares": ["sage"], "imageSha256": "e" * 64}}}}}
    (d / "before.json").write_text(json.dumps(before))
    staged = tmp_path / "apps" / "carried" / "a1"
    staged.mkdir(parents=True)
    (staged / "carry.json").write_text("{}")
    if claimed:
        (staged / "claimed").write_text(claimed)
    wm.APPS_STATE = str(tmp_path / "apps")
    return d


def test_a_carry_counts_once_it_runs_and_is_shared_again(tmp_path, monkeypatch):
    d = carry_dir(tmp_path)
    shell = FakeShell(start_after=2)
    monkeypatch.setattr(wm, "member", shell)
    monkeypatch.setattr(wm.time, "sleep", lambda _: None)
    assert wm.carry_grains(str(d)) == []
    assert [l for _, l in shell.lines if l.startswith("apps install")] == ["apps install app --class S --carry a1"]
    assert shell.shares == ["sage"]


def test_a_grain_that_does_not_start_is_left_and_a_rerun_resumes_its_claim(tmp_path, monkeypatch):
    d = carry_dir(tmp_path)
    shell = FakeShell(start_after=10 ** 6)
    monkeypatch.setattr(wm, "member", shell)
    monkeypatch.setattr(wm.time, "sleep", lambda _: None)
    problems = wm.carry_grains(str(d))
    assert len(problems) == 1 and "carried as a2 but not running" in problems[0], problems
    assert shell.shares == []
    # The worker claimed the carry for the first request: the re-run retries that request, never a second install.
    (tmp_path / "apps" / "carried" / "a1" / "claimed").write_text("cd" * 16)
    shell.start_after, shell.lines = shell.retries + 1, []
    assert wm.carry_grains(str(d)) == []
    assert not [l for _, l in shell.lines if l.startswith("apps install")]
    assert ("house", "apps retry " + "cd" * 16) in shell.lines
    assert shell.shares == ["sage"]


def test_a_grain_no_capture_lists_is_named_not_lost(tmp_path):
    import json
    grains = tmp_path / "apps" / "grains"
    grains.mkdir(parents=True)
    for g, owner, state in [("a1", "house", "running"), ("a7", "nobody", "stopped"), ("a8", "nobody", "deleted")]:
        (grains / f"{g}.json").write_text(json.dumps({"grain": g, "owner": owner, "state": state, "appId": "app"}))
    wm.APPS_STATE = str(tmp_path / "apps")
    world = {"members": {"house": {"grains": {"a1": {}}}, "sage": {"workspace": False}}}
    assert [x["grain"] for x in wm.uncaptured_grains(world)] == ["a7"]


def test_verify_releases_the_staging_copies_and_keeps_the_rollback_export(tmp_path):
    import json
    apps = tmp_path / "apps"
    for p in ["carried/a1/export", "exports/a1", "retired-1794/exports/a1", "exports/a2", "carried/a2"]:
        (apps / p).mkdir(parents=True)
    d = tmp_path / "migrate"
    (d / "grains" / "a1" / "export").mkdir(parents=True)
    wm.APPS_STATE = str(apps)
    before = {"members": {"house": {"grains": {"a1": {"imageSha256": "e" * 64}, "a2": {"exportError": "refused"}}}}}
    assert wm.release_carried(str(d), before) == ["a1"]
    assert not (apps / "carried/a1").exists() and not (apps / "exports/a1").exists()
    assert not (apps / "retired-1794/exports/a1").exists()
    # an uncarried grain's copies and the walk's own export (the rollback copy) stay
    assert (apps / "exports/a2").is_dir() and (apps / "carried/a2").is_dir()
    assert (d / "grains/a1/export").is_dir()
    record = json.loads((d / "grains/a1/released.json").read_text())
    assert len(record["removed"]) == 3
    # released once: a re-run removes nothing, even a copy that reappeared
    (apps / "exports/a1").mkdir()
    assert wm.release_carried(str(d), before) == []
    assert (apps / "exports/a1").is_dir()


def test_an_undecided_share_is_settled_by_its_exact_retry(tmp_path, monkeypatch):
    d = carry_dir(tmp_path)
    shell = FakeShell(start_after=1)
    shell.share_undecided = True
    monkeypatch.setattr(wm, "member", shell)
    monkeypatch.setattr(wm.time, "sleep", lambda _: None)
    assert wm.carry_grains(str(d)) == []
    assert shell.renewed == 1 and shell.shares == ["sage"]
