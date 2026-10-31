#!/usr/bin/env python3
"""Exact conditional residual census after the sixteen-refinement repair.

The Lean reduction is intentionally conditional: `RefineSixteenRepair` is not
CI green yet, so this script does not call either new id paid. It verifies
that all sixteen ids in the repaired paid set are in the frozen 389 census
and outputs the conditional 373-id remainder, preserving the unconditional
census as a separate input.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
BASE = HERE / "residual389-census.json"
REPAIR = ROOT / "n11-work/lean/N11Formalization/EnergyTerminalBatchB13RefineSixteenRepair.lean"
OUT = HERE / "residual373-conditional-census.json"
REMOVED_IDS = [
    37, 2337, 2341, 2965, 3040, 3112, 3116, 3431,
    3440, 3573, 3589, 3623, 3633, 3777, 3792, 3853,
]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def main():
    base = json.loads(BASE.read_text())
    residual = set(base["residual_ids"])
    assert base["counts"]["residual"] == 389
    assert len(residual) == 389
    assert len(REMOVED_IDS) == 16 and len(set(REMOVED_IDS)) == 16
    assert all(node in residual for node in REMOVED_IDS)
    text = REPAIR.read_text()
    assert "theorem paid_count : paidIDs.card = 2013" in text
    assert "theorem remaining_of" in text
    for node in REMOVED_IDS:
        source = ROOT / "n11-work/lean/N11Formalization" / f"EnergyRefineN{node:04d}.lean"
        assert source.is_file() and f"{node}" in source.read_text()

    reduced = sorted(residual - set(REMOVED_IDS))
    assert len(reduced) == 373
    result = {
        "scope": ("conditional complement assuming RefineSixteenRepair is "
                  "kernel-checked; no id is claimed paid by this host script"),
        "status": "CI pending for the Lean sixteen-refinement repair",
        "source_sha256": {
            "residual389-census.json": sha256(BASE),
            "EnergyTerminalBatchB13RefineSixteenRepair.lean": sha256(REPAIR),
        },
        "removed_ids": REMOVED_IDS,
        "counts": {"unconditional_residual": 389, "removed": 16,
                   "conditional_residual": 373},
        "residual_ids": reduced,
        "residual_ids_sha256": hashlib.sha256(
            ",".join(map(str, reduced)).encode()).hexdigest().upper(),
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "residual_ids"},
                     indent=2))


if __name__ == "__main__":
    main()
