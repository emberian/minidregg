import json, sys, time, urllib.request
base = sys.argv[1]
H = {"X-Sandstorm-Username": "Grain%20owner", "Content-Type": "application/json"}
tst = int(time.time())
body = json.dumps({"_type": "location", "lat": 52.52, "lon": 13.405, "tst": tst, "tid": "sm", "acc": 10}).encode()
for _ in range(30):
    try:
        urllib.request.urlopen(urllib.request.Request(base + "/pub", data=body, headers=H), timeout=10).read()
        break
    except Exception:
        time.sleep(1)
else:
    raise SystemExit("never came up")
got = json.load(urllib.request.urlopen(urllib.request.Request(base + "/api/0/last", headers=H), timeout=10))
assert any(r.get("tst") == tst and r.get("lat") == 52.52 and r.get("lon") == 13.405 for r in got), got
other = json.load(urllib.request.urlopen(urllib.request.Request(base + "/api/0/last", headers={"X-Sandstorm-Username": "Someone%20else"}), timeout=10))
assert not any(r.get("tst") == tst for r in other), other
print(json.dumps({"status": "PASS", "tst": tst}))
