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
