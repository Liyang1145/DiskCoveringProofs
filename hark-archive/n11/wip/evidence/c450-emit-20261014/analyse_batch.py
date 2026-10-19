"""Batch result analysis: per-segment GREEN/RED, axiom sets, rate, and the
terminal-module check. Reads the batch-results-*.json + gate logs.

Usage: python analyse_batch.py [results.json]
"""
import json
import re
import sys
from collections import Counter, defaultdict
from datetime import datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent
LOGS = HERE / "logs"
ALLOWED = ("propext", "Classical.choice", "Quot.sound")
ax_re = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]")
err_re = re.compile(r":\d+:\d+:\s*error\s*:")

res_paths = sorted(HERE.glob("batch-results-*.json"))
if len(sys.argv) > 1:
    res_paths = [Path(sys.argv[1])]
if not res_paths:
    print("no batch-results-*.json yet")
    raise SystemExit(0)
res_path = res_paths[-1]
doc = json.loads(res_path.read_text(encoding="utf-8"))
print(f"results file: {res_path.name}")

rows = doc if isinstance(doc, list) else doc.get("rows", doc)
emit = [r for r in rows if r.get("phase") == "emit"]
gates = [r for r in rows if r.get("phase") == "gate"]
rootb = [r for r in rows if r.get("phase") == "rootbuild"]

print(f"\nemit rows : {len(emit)}  failures: {sum(1 for r in emit if r['exit'] != 0)}")
print(f"gate rows : {len(gates)}  failures: {sum(1 for r in gates if r['exit'] != 0)}")

# ---- per-segment rollup ----
by_seg = defaultdict(lambda: [0, 0, 0])
for r in gates:
    k = r["key"]
    by_seg[k][0] += 1
    if r["exit"] == 0:
        by_seg[k][1] += 1
    else:
        by_seg[k][2] += 1
print("\nper-segment (modules gated / green / failed):")
for k in sorted(by_seg, key=lambda s: int(s.split("=")[1])):
    t, g, f = by_seg[k]
    flag = "GREEN" if (f == 0 and t == 34) else ("PARTIAL" if f == 0 else "RED")
    print(f"  {k:>6}  {t:>3}/34 green  failed={f}  {flag}")

# ---- axiom sets across ALL gated modules ----
sets = Counter()
reports = 0
mods_with_reports = 0
for r in gates:
    if r["exit"] != 0:
        continue
    logp = Path(r.get("log", ""))
    if not logp.exists():
        continue
    txt = logp.read_text(encoding="utf-8", errors="replace")
    leaf = r["module"].split(".")[-1]
    mine = []
    flat = re.sub(r"\s*\n\s*", " ", txt)
    for m in ax_re.finditer(flat):
        if leaf in m.group(1):
            mine.append(tuple(a.strip() for a in m.group(2).split(",")))
    if mine:
        mods_with_reports += 1
    for s in mine:
        sets[s] += 1
        reports += 1
print(f"\nmodules with >=1 module-only axiom report: {mods_with_reports}/{len(gates)}")
print(f"total module-only axiom reports: {reports}")
print(f"distinct axiom sets: {len(sets)}")
for s, c in sets.most_common():
    bad = [a for a in s if a not in ALLOWED]
    print(f"  x{c}  {list(s)}  {'OK' if not bad else 'FORBIDDEN: ' + str(bad)}")

# ---- rate ----
times = []
for r in gates:
    logp = Path(str(r.get("log", "")) + ".result.json")
    if logp.exists():
        j = json.loads(logp.read_text(encoding="utf-8-sig"))
        try:
            times.append((datetime.fromisoformat(j["finished"])
                          - datetime.fromisoformat(j["started"])).total_seconds())
        except Exception:
            pass
if times:
    avg = sum(times) / len(times)
    print(f"\nmodules timed: {len(times)}  avg {avg:.1f}s/module  "
          f"min {min(times):.0f}s  max {max(times):.0f}s")
    left = 782 - len(times)
    print(f"remaining {left} modules -> ~{left * avg / 3600:.1f} h at this rate")

# ---- terminal module ----
term = HERE.parent.parent / "lean" / "N11Formalization" / "C450Source36Segment.lean"
if term.exists():
    t = term.read_text(encoding="utf-8")
    print("\nterminal module C450Source36Segment:")
    for pat in ("c450Segs.drop 36", "remaining_count : remainingSegs.length = 0",
                "source36_paid", "source35_remaining_split"):
        print(f"  {'OK ' if pat in t else 'MISS'} {pat}")

if rootb:
    print(f"\nROOT BUILD: exit={rootb[0]['exit']} log={rootb[0]['log']}")
