#!/usr/bin/env python3
"""Exact set and static source audit for the 373-id residual interface."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean"
MODULE = LEAN / "N11Formalization" / "EnergyTerminalResidualCensusRefine373.lean"
CENSUS = HERE / "residual389-census.json"
TARGETS = HERE / "TARGETS.txt"
REMOVED = [
    37, 3112, 3149, 3853, 3116, 3431, 3573, 3777, 2337, 2341, 3633,
    3841, 3792, 3496, 3794, 3795,
]
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|implemented_by)\b|"
    r"\bLean\.ofReduceBool\b|\bmaxHeartbeats\s+0\b"
)


def main() -> None:
    data = json.loads(CENSUS.read_text())
    ids = data["residual_ids"]
    assert len(ids) == 389, len(ids)
    assert hashlib.sha256(",".join(map(str, ids)).encode()).hexdigest().upper() == \
        data["residual_ids_sha256"]
    assert len(set(ids) - set(REMOVED)) == 373

    source = MODULE.read_bytes()
    text = source.decode()
    assert not FORBIDDEN.search(text)
    assert "def newRefineIDs : Finset (Fin 5011) := {3794, 3795}" in text
    assert "refinedResidualIDs.card = 373" in text
    assert "b13_remaining_of_residual373" in text
    assert "not_paid_3794" in text and "not_paid_3795" in text

    targets = [line.strip() for line in TARGETS.read_text().splitlines()
               if line.strip() and not line.startswith("#")]
    target = "N11Formalization.EnergyTerminalResidualCensusRefine373"
    assert targets.count(target) == 1
    assert len(targets) == len(set(targets))
    for dependency in (
        "N11Formalization.EnergyTerminalResidualCensusRefine375",
        "N11Formalization.EnergyTerminalBatchB13Refine3794",
        "N11Formalization.EnergyTerminalBatchB13Refine3795",
    ):
        assert targets.index(dependency) < targets.index(target)

    print(json.dumps({
        "census_count": len(ids),
        "removed_count": len(REMOVED),
        "refined_count": len(set(ids) - set(REMOVED)),
        "target_count": len(targets),
        "module_sha256": hashlib.sha256(source).hexdigest(),
        "static_checks": "PASS",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
