"""Post-Segment-gate analysis: did source13_paid close, and if not, WHERE?

Separates three failure locations so a chain failure is not reported as a pilot
failure:
  (A) my emitted files  -> errors mentioning C450Source13*
  (B) the predecessor chain -> errors mentioning C450Source12* / its deps
  (C) other / infrastructure

Also extracts the axiom list for source13_paid SPECIFICALLY.
Usage: python segment_gate_verdict.py <SegmentGateLog>
"""
import re
import sys
from pathlib import Path

log = Path(sys.argv[1])
res = Path(str(log) + ".result.json")
txt = log.read_text(encoding="utf-8", errors="replace")
lines = txt.splitlines()

print("=" * 72)
print("SEGMENT GATE VERDICT")
print("=" * 72)
if res.exists():
    import json
    m = json.loads(res.read_text(encoding="utf-8-sig"))
    print(f"wrapper exit        : {m['exit']}")
    print(f"build mode          : {m['build']}")
    print(f"started             : {m['started']}")
    print(f"finished            : {m['finished']}")
    print(f"project             : {m['project']}")
else:
    print("!! no .result.json next to log")

err_re = re.compile(r"([^\s:]*\.lean):(\d+):(\d+):\s*error\s*:", re.I)
errs = []
for l in lines:
    mm = err_re.search(l)
    if mm:
        errs.append((mm.group(1), mm.group(2), l.strip()))

print(f"\nREAL Lean errors    : {len(errs)}")
mine = [e for e in errs if "C450Source13" in e[0]]
pred = [e for e in errs if "C450Source12" in e[0]]
other = [e for e in errs if e not in mine and e not in pred]
print(f"  (A) in MY files (C450Source13*)      : {len(mine)}")
print(f"  (B) in predecessor chain (Source12*) : {len(pred)}")
print(f"  (C) elsewhere                        : {len(other)}")
for tag, grp in (("A", mine), ("B", pred), ("C", other)):
    for f, ln, txtl in grp[:6]:
        print(f"     [{tag}] {Path(f).name}:{ln}: {txtl[:150]}")

# --- the theorem itself ---
print("\n--- source13_paid axiom report (the decisive item) ---")
ax_re = re.compile(r"'([^']*source13_paid)' depends on axioms:\s*\[([^\]]*)\]")
hits = []
for l in lines:
    mm = ax_re.search(l)
    if mm:
        hits.append([a.strip() for a in mm.group(2).split(",")])
if hits:
    for h in set(map(tuple, hits)):
        AL = ("Classical.choice", "Quot.sound", "propext")
        bad = [a for a in h if a not in AL]
        print(f"  {list(h)}   {'EXACTLY ALLOWED TRIO' if not bad else 'FORBIDDEN: ' + str(bad)}")
else:
    print("  (no axiom report for source13_paid in this log)")

# --- did the DECLARATION even appear / is it sorry-free ---
print("\n--- declaration check ---")
for pat, label in ((r"source13_paid", "source13_paid mentioned"),
                   (r"\bsorry\b", "sorry"),
                   (r"native_decide", "native_decide"),
                   (r"ofReduceBool", "Lean.ofReduceBool"),
                   (r"declaration uses 'sorry'", "declaration-uses-sorry"),
                   (r"\bunsolved goals\b", "unsolved goals"),
                   (r"function expected|unknown identifier|unknown constant",
                    "elaboration errors")):
    c = len(re.findall(pat, txt))
    print(f"  {label:28}: {c}")

# --- was the predecessor actually BUILT during this run? ---
print("\n--- did the run build predecessors? ---")
for pat in ("C450Source12Segment", "C450Source12Data", "C450Source12GroupedC01",
            "C450Source11Segment"):
    print(f"  mentions {pat:26}: {txt.count(pat)}")
