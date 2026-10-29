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
sub_sources = [(LEAN / f"Paid16GeneralNext1182S{i:02}.lean").read_text() for i in range(1, 9)]
assert all("maxRecDepth" not in s for s in sub_sources)
top = (LEAN / "Paid16GeneralNext1182.lean").read_text()
assert "Finset.univ.biUnion part" in top
assert "maxRecDepth" not in top
assert "Fin.sum_univ_eight" not in top and "Fin.sum_univ_succ" in top
assert top.count("private theorem block_s") == 57
assert top.count("all_goals norm_num") == 57
assert top.count(").mp h with rfl |") == 57
assert "decide +kernel" not in top
assert "Finset.all_eq_true.mp (s := Paid16GeneralNext1182S" not in top
assert "simp only [Paid16GeneralNext1182S" not in top
assert "<;> norm_num" not in top
assert "all_goals omega" not in top
assert top.count("private theorem part_s") == 8
assert top.count("private theorem disjoint_s") == 28
assert "theorem lower_bound" in top
assert top.count("have hb := (part_s") == 8
assert "exact (part_s01_bounds n h).1" not in top
assert top.count("fin_cases j") == 8
assert top.count("exact (hij rfl).elim") == 8
assert top.count("change Disjoint (part i) (part j)") == 1
assert top.count("simpa [part, Function.onFun] using disjoint_s") == 56
assert top.count(".symm") == 56
assert top.count("| (change Disjoint Paid16GeneralNext1182S") == 56
assert top.count("; exact disjoint_s") == 56
report = {
    "manifest": str(MAN.relative_to(ROOT)),
    "ids": len(ids), "part_sizes": [len(p) for p in parts],
    "bounds": bounds, "pairwise_disjoint": True,
    "part_bound_theorems": top.count("private theorem part_s"),
    "literal_block_bound_theorems": top.count("private theorem block_s"),
    "max_block_cases": 21,
    "interval_disjoint_theorems": top.count("private theorem disjoint_s"),
    "pairwise_dispatch_diagonal_cases": top.count("exact (hij rfl).elim"),
    "pairwise_dispatch_off_diagonal_cases": top.count(
        "simpa [part, Function.onFun] using disjoint_s"
    ),
    "defeq_fallback_branches": top.count(
        "| (change Disjoint Paid16GeneralNext1182S"
    ),
    "literal_membership_block_proofs": top.count("all_goals norm_num"),
    "global_lower_bound_transfers": top.count("have hb := (part_s"),
    "direct_part_lower_bound_exacts": top.count("exact (part_s"),
    "kernel_decide_checks": top.count("decide +kernel"),
    "top_sha256": hashlib.sha256(top.encode()).hexdigest().upper(),
    "scope": "exact manifest/literal-block audit only; not Lean elaboration",
}
(LANE / "audit_next1182_blocks-report.json").write_text(json.dumps(report, indent=2)+"\n")
print(json.dumps(report, indent=2))
