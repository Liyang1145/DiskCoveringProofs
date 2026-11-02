#!/usr/bin/env python3
"""Exact set and static source audit for the 354-id residual interface."""
from pathlib import Path
import hashlib
import json
import py_compile
import re

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean"
MODULE = LEAN / "N11Formalization" / "EnergyTerminalResidualCensusRefine354.lean"
CENSUS = HERE / "residual389-census.json"
REMOVED = {
    37, 3112, 3149, 3853, 3116, 3431, 3573, 3777, 2337, 2341, 3633,
    3841, 3792, 3496, 3794, 3795, 3800, 3803, 3979, 3865, 4684,
    4650, 4244, 3778, 4313, 3522, 3783, 3808, 3821, 3851, 4162, 2965, 3040,
    3440, 3520,
}
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|implemented_by)\b|"
    r"\bLean\.ofReduceBool\b|\bmaxHeartbeats\s+0\b"
)


def main() -> None:
    data = json.loads(CENSUS.read_text())
    ids = data["residual_ids"]
    assert len(ids) == 389
    assert hashlib.sha256(",".join(map(str, ids)).encode()).hexdigest().upper() == \
        data["residual_ids_sha256"]
    assert len(REMOVED) == 35
    assert REMOVED <= set(ids)
    assert len(set(ids) - REMOVED) == 354

    source = MODULE.read_bytes()
    text = source.decode()
    assert not FORBIDDEN.search(text)
    assert "def newRefineIDs : Finset (Fin 5011) := {3440, 3520}" in text
    assert "refinedResidualIDs.card = 354" in text
    assert "b13_remaining_of_residual354" in text
    assert "EnergyTerminalResidualCensusRefine356.b13_remaining_of_residual356" in text
    assert "not_paid_3440" in text and "not_paid_3520" in text

    targets = [line.strip() for line in (HERE / "TARGETS.txt").read_text().splitlines()
               if line.strip() and not line.startswith("#")]
    target = "N11Formalization.EnergyTerminalResidualCensusRefine354"
    assert targets.count(target) == 1
    assert len(targets) == len(set(targets))
    for dependency in (
        "N11Formalization.EnergyTerminalResidualCensusRefine356",
        "N11Formalization.EnergyTerminalBatchB13Refine3440",
        "N11Formalization.EnergyTerminalBatchB13Refine3520",
    ):
        assert targets.index(dependency) < targets.index(target)

    py_compile.compile(__file__, doraise=True)
    print(json.dumps({
        "census_count": len(ids),
        "removed_count": len(REMOVED),
        "refined_count": len(set(ids) - REMOVED),
        "module_sha256": hashlib.sha256(source).hexdigest(),
        "static_checks": "PASS",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
