#!/usr/bin/env python3
"""Exact audit of the lane-B 373 -> lane-C 346 residual reduction.

The 27-id difference is checked against the archive refinement modules already
consumed by lane C.  This is source/set bookkeeping, not Lean elaboration,
kernel credit, or payment of any residual radius.
"""
from __future__ import annotations

import ast
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization"
C = ROOT / "n11-work/ops/lanes/C"
B373 = C / "residual373-conditional-census.json"
C389 = C / "residual389-census.json"
C346_AUDIT = C / "verify_census_346.py"
BRIDGE = LEAN / "LaneBResidual346Bridge.lean"
TARGETS = HERE / "TARGETS.txt"
OUT = HERE / "audit_residual373_to_346_bridge-report.json"
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|implemented_by)\b|"
    r"\bLean\.ofReduceBool\b|\bmaxHeartbeats\s+0\b")


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def literal_removed() -> set[int]:
    tree = ast.parse(C346_AUDIT.read_text())
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(
                isinstance(t, ast.Name) and t.id == "REMOVED" for t in node.targets):
            return set(ast.literal_eval(node.value))
    raise AssertionError("REMOVED assignment not found")


def module_for(node: int) -> Path:
    name = f"EnergyTerminalBatchB13Refine{node:04d}.lean"
    if node == 40:
        name = "EnergyTerminalBatchB13Refine40.lean"
    return LEAN / name


def main() -> int:
    old = json.loads(C389.read_text())["residual_ids"]
    b373_data = json.loads(B373.read_text())
    b373 = set(b373_data["residual_ids"])
    b16 = set(b373_data["removed_ids"])
    c43 = literal_removed()
    c346 = set(old) - c43
    extra27 = c43 - b16

    modules = {}
    for node in sorted(extra27):
        path = module_for(node)
        source = path.read_text()
        modules[str(node)] = {
            "path": str(path.relative_to(ROOT)),
            "sha256": sha(path),
            "has_new_radius": "new_radius" in source,
            "forbidden": bool(FORBIDDEN.search(source)),
        }

    targets = [line.strip() for line in TARGETS.read_text().splitlines()
               if line.strip() and not line.startswith("#")]
    bridge = BRIDGE.read_text()
    checks = {
        "old_census_389": len(old) == 389 and len(set(old)) == 389,
        "b16_subset_old": b16 <= set(old),
        "b373_exact_old_minus_16": b373 == set(old) - b16,
        "b373_count_373": len(b373) == 373,
        "c43_count_43": len(c43) == 43,
        "b16_subset_c43": b16 <= c43,
        "extra27_count_27": len(extra27) == 27,
        "c346_exact": len(c346) == 346,
        "c346_equals_b373_minus_extra27": c346 == b373 - extra27,
        "all_27_modules_present": all(Path(v["path"]).is_file() for v in modules.values()),
        "all_27_have_new_radius": all(v["has_new_radius"] for v in modules.values()),
        "all_27_module_sources_clean": not any(v["forbidden"] for v in modules.values()),
        "bridge_imports_c346": "EnergyTerminalResidualCensusRefine346" in bridge,
        "bridge_has_main_consumer": "main_of_residual346_radius_certificates_and_seven_classes" in bridge,
        "bridge_has_full_disk_consumer": "full_disk_bound_of_residual346_packet_producers_and_seven_classes" in bridge,
        "bridge_source_clean": not bool(FORBIDDEN.search(bridge)),
        "bridge_target_once": targets.count("N11Formalization.LaneBResidual346Bridge") == 1,
    }
    if not all(checks.values()):
        raise SystemExit(json.dumps({k: v for k, v in checks.items() if not v}))
    report = {
        "scope": "exact source-ID reduction audit; no Lean elaboration or kernel credit",
        "source_sha256": {
            "residual373-conditional-census.json": sha(B373),
            "residual389-census.json": sha(C389),
            "verify_census_346.py": sha(C346_AUDIT),
            "LaneBResidual346Bridge.lean": sha(BRIDGE),
            "TARGETS.txt": sha(TARGETS),
        },
        "counts": {
            "b373": len(b373),
            "c346": len(c346),
            "extra_green_refinements": len(extra27),
        },
        "extra27": sorted(extra27),
        "c346_ids_sha256": hashlib.sha256(
            ",".join(map(str, sorted(c346))).encode()).hexdigest().upper(),
        "checks": checks,
        "modules": modules,
        "ok": True,
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"ok": True, "counts": report["counts"],
                      "report_sha256": sha(OUT)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
