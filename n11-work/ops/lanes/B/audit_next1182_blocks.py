#!/usr/bin/env python3
"""Audit the exact eight consecutive id blocks used by Next1182's biUnion."""
from pathlib import Path
import json, hashlib

LANE = Path(__file__).resolve().parent
ROOT = LANE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization"
MAN = ROOT / "n11-work/evidence-20261028/evidence/rest1182-emission-manifest.json"
ids = json.loads(MAN.read_text(encoding="utf-8-sig"))["ids"]
parts = [ids[i*168:(i+1)*168] for i in range(7)] + [ids[7*168:]]
assert len(ids) == 1182 and [len(p) for p in parts] == [168]*7 + [6]
assert all(len(set(p)) == len(p) for p in parts)
bounds = []
for p in parts:
    lo, hi = min(p), max(p)
    bounds.append([lo, hi])
    assert all(lo <= x <= hi for x in p)
assert all(bounds[i][1] < bounds[i+1][0] for i in range(7))
for i in range(8):
    for j in range(i+1, 8):
        assert set(parts[i]).isdisjoint(parts[j])
top = (LEAN / "Paid16GeneralNext1182.lean").read_text()
assert "Finset.univ.biUnion part" in top
assert "maxRecDepth" not in top
report = {
    "manifest": str(MAN.relative_to(ROOT)),
    "ids": len(ids), "part_sizes": [len(p) for p in parts],
    "bounds": bounds, "pairwise_disjoint": True,
    "top_sha256": hashlib.sha256(top.encode()).hexdigest().upper(),
    "scope": "exact manifest/literal-block audit only; not Lean elaboration",
}
(LANE / "audit_next1182_blocks-report.json").write_text(json.dumps(report, indent=2)+"\n")
print(json.dumps(report, indent=2))
