#!/usr/bin/env python3
"""Exact static inventory of residual ids with restored Lean refinements.

This proves no additional bridge can be emitted by consuming an already
restored `EnergyRefineN` module. It does not elaborate Lean and is not a
mathematical or kernel payment.
"""
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
FORMAL = ROOT / "lean" / "N11Formalization"
CENSUS = HERE / "residual389-census.json"
OUT = HERE / "residual-bridge-inventory.json"
MODULE = FORMAL / "EnergyTerminalResidualCensusRefine340.lean"

sys.path.insert(0, str(HERE))
import verify_census_340 as current


def main() -> None:
    doc = json.loads(CENSUS.read_text())
    census = doc["residual_ids"]
    removed = current.REMOVED
    residual = set(census) - removed
    assert len(census) == 389
    assert len(removed) == 49
    assert len(residual) == 340

    restored = {}
    for path in FORMAL.glob("EnergyRefineN*.lean"):
        match = re.fullmatch(r"EnergyRefineN(\d+)\.lean", path.name)
        if match:
            restored[int(match.group(1))] = hashlib.sha256(
                path.read_bytes()).hexdigest()

    assert set(restored) == removed
    candidates = sorted(set(restored) & residual)
    assert not candidates

    module_text = MODULE.read_text()
    assert "refinedResidualIDs.card = 340" in module_text
    payload = {
        "scope": ("exact membership/filesystem inventory only; no Lean "
                  "elaboration, kernel check, or mathematical payment"),
        "census_count": len(census),
        "cumulative_removed_count": len(removed),
        "residual_count": len(residual),
        "restored_refinement_count": len(restored),
        "unconsumed_restored_ids": candidates,
        "bridge_candidates_from_restored_modules": 0,
        "census_sha256": hashlib.sha256(CENSUS.read_bytes()).hexdigest(),
        "frontier_module_sha256": hashlib.sha256(MODULE.read_bytes()).hexdigest(),
    }
    OUT.write_text(json.dumps(payload, indent=1) + "\n")
    print(json.dumps(payload, sort_keys=True))


if __name__ == "__main__":
    main()
