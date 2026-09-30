# sim.py: a COPY OF THE RULES, NOT THE KERNEL. It extends planning/place/p-templates-sim.py to the MUD laws.
#
# It models Pred.eval (Pred/Core.lean:193-211), with the k-sloteq atoms (eqSlots, leSlots: new[a], new[b],
# failing closed when either is absent). The not-yet-landed K-PRED-OFFSET atom leSlotsOff a b k is modelled
# as new[a] <= new[b] + k. The projection it evaluates over follows the source: old = project(pre, pre),
# new = project(pre, post) (Compiler/CanonicalPolicyAdmission.lean:190-191,
# Kernel/DeclaredResourceProjection.lean:28-36). Joint slots are joint/index/{i}/resource/field/{n}/{view} for
# every target of the command (K-JOINT-INDEX, NOT LANDED: the id-keyed original is at
# c-c2:Kernel/DeclaredResourceController.lean:176-180). clock/now is present in old and new (K-CLOCK,
# NOT LANDED). The Book (kelp, the cure's burn) is a dict with a solvency check standing in for
# Batch.admission's sourceSolvent. A stale-read guard (guardFailed) is a CAS the kernel runs before any law;
# it is NOT modelled.
#
# What passing this shows: the clauses are right and in the right order for the J-MUD rows below. What it
# does not show: anything about the Host. The gates are MUD-AREA's jmud1.sh, MUD-INVENTORY's jmud2.sh,
# MUD-COMBAT's jmud3.sh, MUD-MOBS-QUESTS's jmud4.sh and MUD-ORG's jmud5.sh.
#
# usage: python3 sim.py [TEMPLATES_MUD_DIR]      prints the assertion table, exits non-zero on a mismatch
import json, sys, os, re

D = (sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))).rstrip("/") + "/"
REALM = json.load(open(D + "tidewrack/realm.json"))
CONST = {"{" + k + "}": v for k, v in REALM["constants"].items() if k != "derivation"}

KEYS = {"eq": {"type", "slot", "value"}, "le": {"type", "slot", "value"}, "memberOf": {"type", "slot", "values"},
        "writeOnce": {"type", "slot"}, "monotone": {"type", "slot"}, "not": {"type", "predicate"},
        "all": {"type", "predicates"}, "any": {"type", "predicates"}, "witnessed": {"type", "identifier"},
        "eqSlots": {"type", "left", "right"}, "leSlots": {"type", "left", "right"},
        "leSlotsOff": {"type", "left", "right", "offset"}}

def canon(v):
    assert isinstance(v, str) and str(int(v)) == v, f"non-canonical int {v!r}"
    return int(v)

def host_parse(p):  # Host/Json.lean:206-230 exact keys + canonical signed decimals; eqSlots/leSlots per k-sloteq
    assert set(p) == KEYS[p["type"]], p
    t = p["type"]
    if t in ("eq", "le"): canon(p["value"])
    if t == "leSlotsOff": canon(p["offset"])
    if t == "memberOf": [canon(x) for x in p["values"]]
    if t == "not": host_parse(p["predicate"])
    if t in ("all", "any"): [host_parse(c) for c in p["predicates"]]
    if t in ("eqSlots", "leSlots", "leSlotsOff"): assert p["left"] and p["right"]

def load(f, subs):
    s = open(D + f).read()
    for k, v in {**CONST, **subs}.items(): s = s.replace(k, v)
    left = set(re.findall(r"\{[A-Z0-9_]+\}", s))
    assert not left, f"{f}: unbound placeholders {left}"
    j = json.loads(s)
    host_parse(j)
    return j

def ev(p, old, new):
    t = p["type"]
    if t == "eq": return new.get(p["slot"]) == int(p["value"])
    if t == "le": return p["slot"] in new and new[p["slot"]] <= int(p["value"])
    if t == "memberOf": return p["slot"] in new and new[p["slot"]] in [int(x) for x in p["values"]]
    if t == "writeOnce":
        o = old.get(p["slot"]); return o is None or o == 0 or new.get(p["slot"]) == o
    if t == "monotone":
        return p["slot"] in old and p["slot"] in new and old[p["slot"]] <= new[p["slot"]]
    if t == "eqSlots": return p["left"] in new and p["right"] in new and new[p["left"]] == new[p["right"]]
    if t == "leSlots": return p["left"] in new and p["right"] in new and new[p["left"]] <= new[p["right"]]
    if t == "leSlotsOff":
        return p["left"] in new and p["right"] in new and new[p["left"]] <= new[p["right"]] + int(p["offset"])
    if t == "not": return not ev(p["predicate"], old, new)
    if t == "all": return all(ev(c, old, new) for c in p["predicates"])
    if t == "any": return any(ev(c, old, new) for c in p["predicates"])
    return False  # witnessed under failClosed

def fslots(prefix, pre, post):
    s = {f"{prefix}resource/field/{k}/before": v for k, v in pre.items()}
    s.update({f"{prefix}resource/field/{k}/after": v for k, v in post.items()})
    s.update({f"{prefix}resource/field/{k}/delta": v - pre[k] for k, v in post.items() if k in pre})
    return s

def judge(law, verb, subj, targets=(), i=0, now=0):
    """targets: list of (pre, post) field dicts in command order; `i` is the target whose law is judged.
    now=None projects no clock/now slot (wave-c, before K-CLOCK): a clause reading it must refuse."""
    old = {"request/verb": verb, "request/subject": subj}
    if now is not None: old["clock/now"] = now
    new = dict(old)
    if targets:
        pre, post = targets[i]
        old.update(fslots("", pre, pre)); new.update(fslots("", pre, post))
        for j, (p, q) in enumerate(targets):
            old.update(fslots(f"joint/index/{j}/", p, p)); new.update(fslots(f"joint/index/{j}/", p, q))
    if ev(law, old, new): return None
    return next(k for k, c in enumerate(law["predicates"]) if not ev(c, old, new))

def compose(*parts):
    ps = []
    for p in parts: ps += p["predicates"] if p["type"] == "all" else [p]
    return {"type": "all", "predicates": ps}

def names(f):  # clause names from the grammar file's "-- N name" comments; 0 = management
    out = {0: "management"}
    for line in open(D + f):
        m = re.match(r"--\s+(\d+)\s+([a-z-]+)", line)
        if m: out[int(m.group(1))] = m.group(2)
    return out

FIELDS = {k: v for f in ["sheet", "room", "item", "quest", "org"] for k, v in
          json.load(open(D + f + "/fields.json"))["kinds"].items()}
def F(ckind, **kv):
    return {int(FIELDS[ckind][k.replace("_", "-")]): v for k, v in kv.items()}

F_, REF, A, B, C, RAT, TALLY = 7, 9, 11, 12, 13, 21, 30
MG = lambda: load("law.management.json", {"{W_FOUNDER}": str(F_)})
def sheet_law(s, home="105", hpmax=None, neg_respawn=None):
    subs = {"{S}": str(s), "{REF}": str(REF), "{HOME}": home}
    if hpmax: subs["{HPMAX}"] = hpmax
    if neg_respawn: subs["{NEG_RESPAWN}"] = neg_respawn
    return compose(MG(), load("sheet/law.sheet.json", subs))
SN = names("sheet/law.sheet")

def sheet(s, at=102, hp=10, bal=0, eq=0, alive=1, deaths=0, intent=0, target=0, respawn=0,
          asthma=0, paralysis=0, clumsiness=0, ward=0, skill=0):
    return F("sheet", id=s, at=at, hp=hp, bal=bal, eq=eq, alive=alive, deaths=deaths, intent=intent,
             target=target, respawn=respawn, aff_asthma=asthma, aff_paralysis=paralysis,
             aff_clumsiness=clumsiness, def_ward=ward, skill=skill)
def upd(x, ckind, **kv): y = dict(x); y.update(F(ckind, **kv)); return y

DIRS = json.load(open(D + "room/fields.json"))["directions"]
def room(rid, dark=0, leased=0, until=0, exits=None, locks=None):
    r = F("room", id=rid, area=2, dark=dark, leased=leased, until=until, shop=0)
    for d, to in (exits or {}).items():
        k = DIRS.index(d)
        lk = (locks or {}).get(d, 0)
        r[8 + 3 * k] = to; r[9 + 3 * k] = 1 if lk else 0; r[10 + 3 * k] = lk
    return r
QUAY = room(101, exits={"n": 102, "d": 201})
SQUARE = room(102, exits={"s": 101, "w": 103, "n": 104, "nw": 105, "ne": 106})
CELLAR = room(201, dark=1, exits={"u": 101, "n": 202, "e": 203}, locks={"n": 5001})
ARCH = room(202, exits={"s": 201, "n": 204})
JUNCTION = room(203, exits={"w": 201, "e": 205, "s": 206})
PLOT = lambda until: room(302, leased=1, until=until, exits={"w": 301})
ROW = room(301, exits={"s": 110, "e": 302, "n": 303})
def item(iid, kind, owner, where=0, charges=0, worn=0):
    return F("item", id=iid, kind=kind, owner=owner, where=where, worn=worn, charges=charges)
KEY = lambda o: item(5001, 1, o)
LANTERN = lambda o, ch=100: item(6001, 2, o, charges=ch)

rows, bad = [], 0
def show(jrow, what, law, nm, verb, subj, targets=(), i=0, now=0, expect=None):
    global bad
    got = judge(law, verb, subj, list(targets), i, now)
    label = "admitted" if got is None else f"refused: law-denied: {got} {nm[got]}"
    want = "admitted" if expect is None else f"refused: law-denied: {expect} {nm[expect]}"
    ok = label == want
    bad += not ok
    rows.append((jrow, what, label, "ok " if ok else "BAD"))

def pair(pre, post): return (pre, post)
def obs(x): return (x, x)

# ---------------------------------------------------------------- J-MUD-1 the graph (owner moves)
LB = sheet_law(B)
b0 = sheet(B, at=101)
show("J-MUD-1 r3", "B go n (quay -> square)", LB, SN, 2, B, [pair(b0, upd(b0, "sheet", at=102)), obs(QUAY), obs(SQUARE)])
b1 = sheet(B, at=102)
show("J-MUD-1 r4", "B forges a destination no exit reaches (square -> 201)", LB, SN, 2, B,
     [pair(b1, upd(b1, "sheet", at=201)), obs(SQUARE), obs(CELLAR)], expect=16)
show("J-MUD-1 r6", "B names a room it is not in as 'from'", LB, SN, 2, B,
     [pair(b0, upd(b0, "sheet", at=201)), obs(SQUARE), obs(CELLAR)], expect=14)
show("J-MUD-1 r6b", "B go n to the square naming the cellar as joint 2", LB, SN, 2, B,
     [pair(b0, upd(b0, "sheet", at=102)), obs(QUAY), obs(CELLAR)], expect=15)
show("J-MUD-1 r5", "B go d into the dark cellar, no light", LB, SN, 2, B,
     [pair(b0, upd(b0, "sheet", at=201)), obs(QUAY), obs(CELLAR)], expect=18)
show("J-MUD-1 r5b", "B go d holding a lit lantern (joint 3)", LB, SN, 2, B,
     [pair(b0, upd(b0, "sheet", at=201)), obs(QUAY), obs(CELLAR), obs(LANTERN(B))])
show("J-MUD-1 r5c", "B go d with C's lantern", LB, SN, 2, B,
     [pair(b0, upd(b0, "sheet", at=201)), obs(QUAY), obs(CELLAR), obs(LANTERN(C))], expect=18)
show("J-MUD-1 r5d", "B go d with a burnt-out lantern (charges 0)", LB, SN, 2, B,
     [pair(b0, upd(b0, "sheet", at=201)), obs(QUAY), obs(CELLAR), obs(LANTERN(B, 0))], expect=18)
bc = sheet(B, at=201)
show("J-MUD-1 r7", "B go n through the locked door, no key", LB, SN, 2, B,
     [pair(bc, upd(bc, "sheet", at=202)), obs(CELLAR), obs(ARCH)], expect=17)
show("J-MUD-1 r8", "B go n holding the key (joint 3)", LB, SN, 2, B,
     [pair(bc, upd(bc, "sheet", at=202)), obs(CELLAR), obs(ARCH), obs(KEY(B))])
show("J-MUD-1 r9", "B go n showing C's key", LB, SN, 2, B,
     [pair(bc, upd(bc, "sheet", at=202)), obs(CELLAR), obs(ARCH), obs(KEY(C))], expect=17)
show("J-MUD-1 r9b", "B go e (unlocked) from the cellar, no key needed", LB, SN, 2, B,
     [pair(bc, upd(bc, "sheet", at=203)), obs(CELLAR), obs(JUNCTION)])
br = sheet(B, at=301)
show("J-MUD-6 r7", "B enters a manse whose lease ran out (until 50, now 60)", LB, SN, 2, B,
     [pair(br, upd(br, "sheet", at=302)), obs(ROW), obs(PLOT(50))], now=60, expect=19)
show("J-MUD-6 r8", "B enters it after renewal (until 90, now 60)", LB, SN, 2, B,
     [pair(br, upd(br, "sheet", at=302)), obs(ROW), obs(PLOT(90))], now=60)
show("J-MUD-1 r1", "anyone reads a sheet", LB, SN, 1, C)
show("J-MUD-1 r1b", "C writes B's at", LB, SN, 2, C,
     [pair(b0, upd(b0, "sheet", at=102)), obs(QUAY), obs(SQUARE)], expect=1)

# ---------------------------------------------------------------- J-MUD-3 combat (the MUD §2.3 script)
LA, LB = sheet_law(A), sheet_law(B)
t = 10                                               # clock/now
a0 = sheet(A, at=102); b0 = sheet(B, at=102)
a1 = upd(a0, "sheet", intent=1, target=B, skill=1)   # A: strike B bite
show("J-MUD-3 r1", "A strike B bite (intent; bal 0 <= now 10)", LA, SN, 2, A, [pair(a0, a1)], now=t)
a2 = upd(a1, "sheet", bal=t + 3, intent=0, target=0, skill=0)
b1 = upd(b0, "sheet", hp=7, aff_asthma=1)
res = [pair(a1, a2), pair(b0, b1)]
show("J-MUD-3 r2", "referee resolves: A bal := now+3, cleared", LA, SN, 2, REF, res, 0, t)
show("J-MUD-3 r2b", "... and on B: hp 10 -> 7, asthma := 1", LB, SN, 2, REF, res, 1, t)
show("J-MUD-3 r2c", "referee resolves A's strike with no clock/now slot (A side)", LA, SN, 2, REF, res, 0, None, expect=28)
show("J-MUD-3 r2d", "... charging bal := now+2, one short of COST", LA, SN, 2, REF,
     [pair(a1, upd(a2, "sheet", bal=t + 2)), pair(b0, b1)], 0, t, expect=28)
ac = upd(a0, "sheet", intent=2, target=B, skill=4)
ac2 = upd(ac, "sheet", eq=t + 4, intent=0, target=0, skill=0)
bG = upd(b0, "sheet", hp=9, aff_clumsiness=1)
show("J-MUD-3 r2e", "referee resolves A's gust: eq := now+4 (A side)", LA, SN, 2, REF, [pair(ac, ac2), pair(b0, bG)], 0, t)
show("J-MUD-3 r2f", "... and on B: hp 10 -> 9, clumsiness := 1", LB, SN, 2, REF, [pair(ac, ac2), pair(b0, bG)], 1, t)
show("J-MUD-3 r2g", "... eq := now+3, one short of ECOST", LA, SN, 2, REF,
     [pair(ac, upd(ac2, "sheet", eq=t + 3)), pair(b0, bG)], 0, t, expect=29)
show("J-MUD-3 r2h", "... the gust with no clock/now slot (A side)", LA, SN, 2, REF, [pair(ac, ac2), pair(b0, bG)], 0, None, expect=29)
show("J-MUD-3 r3", "A strikes again inside 3 ticks (now 11)", LA, SN, 2, A,
     [pair(a2, upd(a2, "sheet", intent=1, target=B, skill=1))], now=t + 1, expect=10)
show("J-MUD-3 r3b", "A strikes again once balanced (now 13)", LA, SN, 2, A,
     [pair(a2, upd(a2, "sheet", intent=1, target=B, skill=1))], now=t + 3)
show("J-MUD-3 r3c", "A casts inside equilibrium (eq 20, now 13)", LA, SN, 2, A,
     [pair(upd(a2, "sheet", eq=20), upd(a2, "sheet", eq=20, intent=2, target=B, skill=4))], now=t + 3, expect=11)
show("J-MUD-3 r3d", "asthmatic B casts", LB, SN, 2, B,
     [pair(b1, upd(b1, "sheet", intent=2, target=A, skill=4))], now=t, expect=13)
show("J-MUD-3 r4", "referee strikes B for A with no intent of A's", LB, SN, 2, REF,
     [pair(a2, upd(a2, "sheet", bal=t + 6)), pair(b1, upd(b1, "sheet", hp=4))], 1, t + 3, expect=26)
a3 = upd(a2, "sheet", intent=1, target=B, skill=1)
show("J-MUD-3 r4b", "referee resolves but does not charge A's balance", LB, SN, 2, REF,
     [pair(a3, upd(a3, "sheet", intent=0, target=0, skill=0)), pair(b1, upd(b1, "sheet", hp=4))], 1, t + 3, expect=27)
show("J-MUD-3 r4c", "referee resolves A's strike on B in another room", LB, SN, 2, REF,
     [pair(upd(a3, "sheet", at=101), upd(a3, "sheet", at=101, bal=t + 6, intent=0, target=0, skill=0)),
      pair(b1, upd(b1, "sheet", hp=4))], 1, t + 3, expect=26)
# cure: B sends 1 kelp to REF (a Book transfer); the referee burns it and lowers asthma
book = {("B", "kelp"): 1}
def send(who, asset, n):
    if book.get((who, asset), 0) < n: return "refused: bookRefused"
    book[(who, asset)] -= n; return "admitted"
rows.append(("J-MUD-3 r5a", "B cure asthma: send 1 kelp to REF (Book model)", send("B", "kelp", 1), "ok "))
show("J-MUD-3 r5", "... referee writes aff-asthma := 0 on B", LB, SN, 2, REF,
     [pair(b1, upd(b1, "sheet", aff_asthma=0))], now=t)
r = send("B", "kelp", 1)
bad += r != "refused: bookRefused"
rows.append(("J-MUD-3 r5b", "B cure asthma again with 0 kelp (Book model)", r, "ok " if r == "refused: bookRefused" else "BAD"))
show("J-MUD-3 r5c", "B clears its own asthma (no burn)", LB, SN, 2, B,
     [pair(b1, upd(b1, "sheet", aff_asthma=0))], now=t, expect=8)
show("J-MUD-3 r6", "bad table: hp 7 -> -33 and the death it implies", LB, SN, 2, REF,
     [pair(a3, upd(a3, "sheet", bal=t + 6, intent=0, target=0, skill=0)),
      pair(b1, upd(b1, "sheet", hp=-33, alive=0, deaths=1, respawn=t + 3))], 1, t + 3, expect=22)
show("J-MUD-3 r6a", "bad table, non-lethal: hp 10 -> 3 (7 > MAXHIT 6)", LB, SN, 2, REF,
     [pair(a3, upd(a3, "sheet", bal=t + 6, intent=0, target=0, skill=0)), pair(b0, upd(b0, "sheet", hp=3))],
     1, t + 3, expect=22)
show("J-MUD-3 r6b", "referee heals B (hp 7 -> 9)", LB, SN, 2, REF, [pair(b1, upd(b1, "sheet", hp=9))], now=t, expect=21)
# death: A at hp 1 struck by B for 3
aL = sheet(A, at=102, hp=1, bal=t + 3)
bS = sheet(B, at=102, intent=1, target=A, skill=1)
bS2 = upd(bS, "sheet", bal=t + 3, intent=0, target=0, skill=0)
aD = upd(aL, "sheet", hp=-2, alive=0, deaths=1, respawn=t)
show("J-MUD-3 r8", "B kills A: hp 1 -> -2, alive 0, deaths 0 -> 1", LA, SN, 2, REF, [pair(bS, bS2), pair(aL, aD)], 1, t)
show("J-MUD-3 r8a", "... the same blow leaving alive = 1", LA, SN, 2, REF,
     [pair(bS, bS2), pair(aL, upd(aL, "sheet", hp=-2))], 1, t, expect=6)
show("J-MUD-3 r8b", "... the same blow counting 2 deaths", LA, SN, 2, REF,
     [pair(bS, bS2), pair(aL, upd(aD, "sheet", deaths=2))], 1, t, expect=5)
# 33 death-needs-hp (SHEET-ITEM-LAW referee_kills_healthy_sheet): the referee zeroes alive at hp 3, no attacker.
aH3 = sheet(A, at=102, hp=3)
smite = upd(aH3, "sheet", alive=0, deaths=1, respawn=t)          # respawn = now + RESPAWN (0): clause 25 met
show("J-MUD-3 r8c", "referee smites A at hp 3: alive 0, deaths +1 (no hp change)", LA, SN, 2, REF,
     [pair(aH3, smite)], now=t, expect=33)
show("J-MUD-3 r8d", "... the same smite with no clock/now slot", LA, SN, 2, REF,
     [pair(aH3, smite)], now=None, expect=25)
show("J-MUD-3 r8e", "... the smite as a lethal hit (hp 3 -> -1) with no attacker", LA, SN, 2, REF,
     [pair(aH3, upd(smite, "sheet", hp=-1))], now=t, expect=26)
show("J-MUD-3 r8f", "B kills A as in r8, no clock/now slot", LA, SN, 2, REF, [pair(bS, bS2), pair(aL, aD)], 1, None, expect=25)
show("J-MUD-3 r9", "dead A strikes B", LA, SN, 2, A,
     [pair(aD, upd(aD, "sheet", intent=1, target=B, skill=1))], now=t + 5, expect=7)
show("J-MUD-3 r9b", "B strikes dead A (the referee resolves it)", LA, SN, 2, REF,
     [pair(bS, bS2), pair(aD, upd(aD, "sheet", hp=-5))], 1, t + 5, expect=26)
aP = upd(aD, "sheet", intent=9)
show("J-MUD-3 r10a", "dead A prays", LA, SN, 2, A, [pair(aD, aP)], now=t + 5)
show("J-MUD-3 r10b", "dead A writes alive := 1 itself", LA, SN, 2, A,
     [pair(aD, upd(aD, "sheet", alive=1, hp=10))], now=t + 5, expect=7)
aR = upd(aP, "sheet", alive=1, hp=10, at=105, intent=0)
show("J-MUD-3 r10c", "shrine (referee) revives A at 105, hp 10", LA, SN, 2, REF, [pair(aP, aR)], now=t + 5)
show("J-MUD-3 r10d", "referee revives A without a prayer", LA, SN, 2, REF,
     [pair(aD, upd(aD, "sheet", alive=1, hp=10, at=105))], now=t + 5, expect=23)
show("J-MUD-3 r10e", "referee revives A at the quay, not the shrine", LA, SN, 2, REF,
     [pair(aP, upd(aR, "sheet", at=101))], now=t + 5, expect=23)
show("J-MUD-3 r11", "stranger C writes B's hp", LB, SN, 2, C, [pair(b1, upd(b1, "sheet", hp=1))], now=t, expect=1)
show("J-MUD-3 r12", "referee lowers A's deaths 1 -> 0", LA, SN, 2, REF, [pair(aR, upd(aR, "sheet", deaths=0))], now=t, expect=4)
bP = sheet(B, at=102, paralysis=1)
show("J-MUD-3 r14", "paralysed B strikes", LB, SN, 2, B,
     [pair(bP, upd(bP, "sheet", intent=1, target=A, skill=1))], now=t, expect=12)
bW = sheet(B, at=102, ward=1)
aE = sheet(A, at=102, intent=1, target=B, skill=2)
show("J-MUD-3 r15", "warded B envenomed (paralysis := 1)", LB, SN, 2, REF,
     [pair(aE, upd(aE, "sheet", bal=t + 3, intent=0, target=0, skill=0)), pair(bW, upd(bW, "sheet", hp=8, aff_paralysis=1))],
     1, t, expect=31)
show("J-MUD-3 r15b", "referee raises B's ward with no defend intent", LB, SN, 2, REF,
     [pair(b0, upd(b0, "sheet", def_ward=1))], now=t, expect=32)
show("J-MUD-3 r14b", "paralysed B walks (square -> quay)", LB, SN, 2, B,
     [pair(upd(bP, "sheet", at=102), upd(bP, "sheet", at=101)), obs(SQUARE), obs(QUAY)], now=t, expect=12)
show("J-MUD-3 r14c", "paralysed B casts gust (mental: paralysis does not stop it)", LB, SN, 2, B,
     [pair(bP, upd(bP, "sheet", intent=2, target=A, skill=4))], now=t)
show("J-MUD-3 r15c", "unwarded B envenomed (paralysis := 1)", LB, SN, 2, REF,
     [pair(aE, upd(aE, "sheet", bal=t + 3, intent=0, target=0, skill=0)), pair(b0, upd(b0, "sheet", hp=8, aff_paralysis=1))],
     1, t)
bD = sheet(B, at=102, intent=3)
show("J-MUD-3 r15d", "referee raises B's ward on B's defend intent", LB, SN, 2, REF,
     [pair(bD, upd(bD, "sheet", def_ward=1, bal=t + 3, intent=0))], now=t)
show("J-MUD-3 r15e", "B lowers its own ward (the owner never writes combat fields)", LB, SN, 2, B,
     [pair(bW, upd(bW, "sheet", def_ward=0))], now=t, expect=8)
# the rat: a mob sheet under the same law, RESPAWN 20
LR = sheet_law(RAT, home="201", hpmax="8", neg_respawn="-20")
r0 = sheet(RAT, at=203, hp=2); bK = sheet(B, at=203, intent=1, target=RAT, skill=1)
show("J-MUD-4 r2", "B kills the rat, respawn := now+20", LR, SN, 2, REF,
     [pair(bK, upd(bK, "sheet", bal=t + 3, intent=0, target=0, skill=0)),
      pair(r0, upd(r0, "sheet", hp=-1, alive=0, deaths=1, respawn=t + 20))], 1, t)
show("J-MUD-4 r2b", "... with respawn := now+5 (too soon)", LR, SN, 2, REF,
     [pair(bK, upd(bK, "sheet", bal=t + 3, intent=0, target=0, skill=0)),
      pair(r0, upd(r0, "sheet", hp=-1, alive=0, deaths=1, respawn=t + 5))], 1, t, expect=25)
show("J-MUD-4 r2e", "... with respawn := now+19 (one short)", LR, SN, 2, REF,
     [pair(bK, upd(bK, "sheet", bal=t + 3, intent=0, target=0, skill=0)),
      pair(r0, upd(r0, "sheet", hp=-1, alive=0, deaths=1, respawn=t + 19))], 1, t, expect=25)
show("J-MUD-4 r2f", "B kills the rat with no clock/now slot", LR, SN, 2, REF,
     [pair(bK, upd(bK, "sheet", bal=t + 3, intent=0, target=0, skill=0)),
      pair(r0, upd(r0, "sheet", hp=-1, alive=0, deaths=1, respawn=t + 20))], 1, None, expect=25)
rD = sheet(RAT, at=203, hp=-1, alive=0, deaths=1, respawn=t + 20, intent=9)
show("J-MUD-4 r2c", "referee revives the rat early (now+10)", LR, SN, 2, REF,
     [pair(rD, upd(rD, "sheet", alive=1, hp=8, at=201, intent=0))], now=t + 10, expect=23)
show("J-MUD-4 r2d", "referee revives the rat at now+20, in the cellar", LR, SN, 2, REF,
     [pair(rD, upd(rD, "sheet", alive=1, hp=8, at=201, intent=0))], now=t + 20)
rw = sheet(RAT, at=205)
show("J-MUD-4 r1", "the rat wanders back into the dark cellar", LR, SN, 2, RAT,
     [pair(sheet(RAT, at=203), sheet(RAT, at=201)), obs(JUNCTION), obs(CELLAR)], now=t, expect=18)

# ---------------------------------------------------------------- J-MUD-2 unique items
IN = names("item/law.item")
LI = lambda kind="1", iid="5001": compose(MG(), load("item/law.item.json", {"{REF}": str(REF), "{ID}": iid, "{KIND}": kind}))
sw = item(7001, 3, A)
LS = LI("3", "7001")
show("J-MUD-2 r4", "A gives the sword to B (owner write)", LS, IN, 2, A, [pair(sw, upd(sw, "item", owner=B))])
show("J-MUD-2 r4b", "A gives the same sword to C from the SAME pre-state (law alone)", LS, IN, 2, A,
     [pair(sw, upd(sw, "item", owner=C))])   # admitted: per-step law; the durable CAS refuses it (item/README.md)
show("J-MUD-2 r4c", "... the give to C chained after the give to B", LS, IN, 2, A,
     [pair(upd(sw, "item", owner=B), upd(sw, "item", owner=C))], expect=1)
show("J-MUD-2 r5", "C writes owner := C on A's sword", LS, IN, 2, C, [pair(sw, upd(sw, "item", owner=C))], expect=1)
show("J-MUD-2 r6", "A recharges the lantern (charges up)", LI("2", "6001"), IN, 2, A,
     [pair(LANTERN(A, 5), LANTERN(A, 9))], expect=3)
show("J-MUD-2 r6b", "referee burns a lantern charge", LI("2", "6001"), IN, 2, REF, [pair(LANTERN(A, 5), LANTERN(A, 4))])
show("J-MUD-2 r7", "referee moves A's sword to itself", LS, IN, 2, REF, [pair(sw, upd(sw, "item", owner=REF))], expect=4)
show("J-MUD-2 r7b", "A changes the sword's kind", LS, IN, 2, A, [pair(sw, upd(sw, "item", kind=1))], expect=2)
aH = sheet(A, at=203)
show("J-MUD-2 r8", "A drops the sword where it stands (203)", LS, IN, 2, A,
     [pair(sw, upd(sw, "item", owner=REF, where=203)), obs(aH)])
show("J-MUD-2 r8b", "A drops the sword into room 101 from 203", LS, IN, 2, A,
     [pair(sw, upd(sw, "item", owner=REF, where=101)), obs(aH)], expect=6)
fl = item(7001, 3, REF, where=203)
show("J-MUD-2 r9", "referee hands the floor sword to B, who stands there", LS, IN, 2, REF,
     [pair(fl, upd(fl, "item", owner=B, where=0)), obs(sheet(B, at=203))])
show("J-MUD-2 r9b", "... to C, who is in 101", LS, IN, 2, REF,
     [pair(fl, upd(fl, "item", owner=C, where=0)), obs(sheet(C, at=101))], expect=7)
show("J-MUD-2 r9d", "referee hands the floor sword to B naming C's sheet as joint 1", LS, IN, 2, REF,
     [pair(fl, upd(fl, "item", owner=B, where=0)), obs(sheet(C, at=203))], expect=7)
show("J-MUD-2 r9e", "B takes the floor sword itself (not the referee)", LS, IN, 2, B,
     [pair(fl, upd(fl, "item", owner=B, where=0)), obs(sheet(B, at=203))], expect=1)
show("J-MUD-2 r9c", "B keeps the sword but leaves where = 203", LS, IN, 2, REF,
     [pair(fl, upd(fl, "item", owner=B)), obs(sheet(B, at=203))], expect=5)

# ---------------------------------------------------------------- J-MUD-4 the quest and its reward
QN = names("quest/cellar-key/law.quest")
qsubs = {"{S}": str(B), "{REF}": str(REF), "{QUEST}": "1", "{RAT}": str(RAT)}
LQ = compose(MG(), load("quest/cellar-key/law.quest.json", qsubs))
q0 = F("quest", id=1, owner=B, state=0, started=0, rewarded=0)
rat1 = sheet(RAT, at=201, deaths=1)
q1 = upd(q0, "quest", state=1, started=1)
show("J-MUD-4 r3", "B accepts (0 -> 1, started := rat deaths 1)", LQ, QN, 2, B, [pair(q0, q1), obs(rat1)])
show("J-MUD-4 r3b", "B accepts recording a stale deaths count 0", LQ, QN, 2, B, [pair(q0, upd(q0, "quest", state=1)), obs(rat1)], expect=5)
show("J-MUD-4 r4a", "referee marks done before the rat died again", LQ, QN, 2, REF, [pair(q1, upd(q1, "quest", state=2)), obs(rat1)], expect=5)
rat2 = sheet(RAT, at=201, deaths=2, alive=0)
q2 = upd(q1, "quest", state=2)
show("J-MUD-4 r4", "referee marks done after the rat's deaths moved", LQ, QN, 2, REF, [pair(q1, q2), obs(rat2)])
show("J-MUD-4 r4c", "B marks its own quest done", LQ, QN, 2, B, [pair(q1, q2), obs(rat2)], expect=5)
LK = compose(MG(), load("item/law.item.json", {"{REF}": str(REF), "{ID}": "5001", "{KIND}": "1"}),
             load("item/law.item-reward.json", {"{REF}": str(REF), "{QUEST}": "1"}))
KN = {**IN, **{k: v for k, v in names("item/law.item-reward").items() if k}}
key0 = KEY(REF)
show("J-MUD-4 r5", "early reward: quest at 1, key REF -> B", LQ, QN, 2, REF,
     [pair(q1, upd(q1, "quest", rewarded=1)), pair(key0, KEY(B))], 0, expect=7)
show("J-MUD-4 r5b", "... the key's law refuses it too", LK, KN, 2, REF,
     [pair(q1, upd(q1, "quest", rewarded=1)), pair(key0, KEY(B))], 1, expect=8)
show("J-MUD-4 r5c", "referee gives the reserved key with no quest in the command", LK, KN, 2, REF,
     [pair(key0, KEY(B))], 0, expect=8)
show("J-MUD-4 r6", "reward at state 2: rewarded 0 -> 1 (quest side)", LQ, QN, 2, REF,
     [pair(q2, upd(q2, "quest", rewarded=1)), pair(key0, KEY(B))], 0)
show("J-MUD-4 r6b", "reward at state 2: key REF -> B (key side)", LK, KN, 2, REF,
     [pair(q2, upd(q2, "quest", rewarded=1)), pair(key0, KEY(B))], 1)
show("J-MUD-4 r6c", "... key REF -> C on B's quest", LK, KN, 2, REF,
     [pair(q2, upd(q2, "quest", rewarded=1)), pair(key0, KEY(C))], 1, expect=8)
show("J-MUD-4 r6d", "B later gives the key to D (C here)", LK, KN, 2, B, [pair(KEY(B), KEY(C))])
show("J-MUD-4 r7", "rewind 2 -> 1", LQ, QN, 2, REF, [pair(q2, q1), obs(rat2)], expect=4)

# ---------------------------------------------------------------- J-MUD-5 a ballot
BN = names("org/law.ballot")
seats = {f"{{SEAT_{k}}}": str(s) for k, s in enumerate([A, B, C, 0, 0, 0, 0, 0])}
LBAL = compose(MG(), load("org/law.ballot.json", {**seats, "{N}": "1", "{G}": "1", "{OFFICE}": "1", "{NCAND}": "3",
                                                   "{OFFICER}": str(A), "{TALLY}": str(TALLY)}))
bal0 = F("ballot", id=1, org=1, office=1, open=1, result=0, ncand=3, **{f"vote_{k}": 0 for k in range(8)})
v1 = upd(bal0, "ballot", vote_1=2)
show("J-MUD-5 r5", "B votes 2 in seat 1", LBAL, BN, 2, B, [pair(bal0, v1)])
show("J-MUD-5 r6", "B votes again, 3", LBAL, BN, 2, B, [pair(v1, upd(v1, "ballot", vote_1=3))], expect=5)
show("J-MUD-5 r7", "C writes A's seat", LBAL, BN, 2, C, [pair(v1, upd(v1, "ballot", vote_0=3))], expect=4)
closed = upd(v1, "ballot", vote_0=2, vote_2=3, open=0)
show("J-MUD-5 r8", "C closes the ballot (not the officer)", LBAL, BN, 2, C, [pair(upd(closed, "ballot", open=1), closed)], expect=3)
show("J-MUD-5 r8b", "C votes after close", LBAL, BN, 2, C, [pair(closed, upd(closed, "ballot", vote_2=1))], expect=4)
show("J-MUD-5 r9", "tally writes result 2", LBAL, BN, 2, TALLY, [pair(closed, upd(closed, "ballot", result=2))])
show("J-MUD-5 r9b", "tally writes a result while open", LBAL, BN, 2, TALLY,
     [pair(upd(v1, "ballot"), upd(v1, "ballot", result=2))], expect=6)
ON = names("org/law.org")
LO = compose(MG(), load("org/law.org.json", {"{G}": "1", "{FOUNDER}": str(A), "{TAX_MAX}": "50"}))
g0 = F("org", id=1, leader=A, ballot=0, tax_rate=0, treasurer=0, recruiter=0)
done = upd(closed, "ballot", result=2)
show("J-MUD-5 r10", "A hands leader to candidate 2 by ballot 1", LO, ON, 2, A,
     [pair(g0, upd(g0, "org", leader=2, ballot=1)), obs(done)])
show("J-MUD-5 r10b", "A hands leader to C against the result", LO, ON, 2, A,
     [pair(g0, upd(g0, "org", leader=C, ballot=1)), obs(done)], expect=3)
show("J-MUD-5 r10c", "A reuses ballot 1 for a second handover", LO, ON, 2, A,
     [pair(upd(g0, "org", ballot=1), upd(g0, "org", leader=2, ballot=1)), obs(done)], expect=3)

w = max(len(r[1]) for r in rows)
print(f"{'':3} {'row':12} {'move':{w}}  verdict")
for jrow, what, label, mark in rows:
    print(f"{mark} {jrow:12} {what:{w}}  {label}")
print(f"\n{len(rows)} rows, {len(rows) - bad} as expected, {bad} not")
sys.exit(1 if bad else 0)
