#!/usr/bin/env python3
"""Source/API audit of the seven frozen-cap wrappers; no Lean credit claimed."""
import hashlib, json, re
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization"
IDS = (1409, 2337, 2341, 2356, 2360, 2368, 2370)
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest().upper()
def block(text, name):
    m = re.search(rf"theorem {name}\b(.*?)(?=\n/theorem |\nend\b)", text, re.S)
    if not m: raise AssertionError(f"missing theorem {name}")
    return m.group(1)
tree = LEAN / "FrozenCapPublicExcludedTree.lean"
tree_text = tree.read_text()
cap = LEAN / "PaidCellCertificateM.lean"
cap_text = cap.read_text()
latest = (ROOT / "n11-work/ops/ci/LATEST.md").read_text()
census_path = ROOT / "n11-work/ops/lanes/C/residual389-census.json"
census = json.loads(census_path.read_text())
records = []
for node in IDS:
    b = block(tree_text, f"excluded_{node}_tree")
    row = LEAN / f"FrozenCapRowCap{node}.lean"
    records.append({
        "id": node, "in_residual_census": node in census["residual_ids"],
        "requires_hf0": "(hf0 :" in b, "requires_hg": "(hg :" in b,
        "requires_valid_packet": "PaidCellCertificateM.Valid p" in b,
        "row_cap_module_present": row.is_file(),
        "row_cap_module_in_latest_ci_errors": row.stem in latest,
    })
packet_fields = cap_text.split("structure Packet", 1)[1].split("def PA", 1)[0]
checks = {
    "seven_records": len(records) == 7,
    "all_in_residual_census": all(r["in_residual_census"] for r in records),
    "all_conditional_on_hf0_and_hg": all(r["requires_hf0"] and r["requires_hg"] for r in records),
    "all_require_valid_packet": all(r["requires_valid_packet"] for r in records),
    "all_row_cap_modules_present": all(r["row_cap_module_present"] for r in records),
    "all_row_caps_red_in_latest_ci": all(r["row_cap_module_in_latest_ci_errors"] for r in records),
    "packet_has_no_fixed_f0_or_g_field": "f0Lo" not in packet_fields and "g :" not in packet_fields,
}
report = {
    "scope": "source/API gap audit only; no Lean elaboration and no residual payment",
    "source_sha256": {"FrozenCapPublicExcludedTree.lean": sha(tree),
        "PaidCellCertificateM.lean": sha(cap), "residual389-census.json": sha(census_path)},
    "records": records, "checks": checks, "all_checks_pass": all(checks.values()),
    "first_missing_link": ("Every tree exclusion needs fixed equalities f0Lo(W,slopeQ)=F0 and "
        "g(W,slopeQ)=G for an arbitrary Valid packet. The Packet structure has no fields forcing "
        "those equalities, and no bridge theorem supplies them."),
    "conclusion": ("The seven frozen-cap wrappers do not instantiate a residual payment. They exclude "
        "a packet only after fixed F0/G identifications, and their row-cap dependencies are red in "
        "the latest CI snapshot."),
}
out = HERE / "audit_frozen_cap_api_gap-report.json"
out.write_text(json.dumps(report, indent=2) + "\n")
print(out.relative_to(ROOT)); print(json.dumps(checks, indent=2))
if not report["all_checks_pass"]: raise SystemExit(1)
