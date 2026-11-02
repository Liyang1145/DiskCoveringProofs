#!/usr/bin/env python3
"""Static/exact-set audit for the conditional 344-id residual bridge."""
from pathlib import Path
import hashlib
import json
import py_compile
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean"
FORMAL = LEAN / "N11Formalization"
CENSUS = HERE / "residual389-census.json"
MODULE = FORMAL / "EnergyTerminalResidualCensusRefine344.lean"
IDS = (3825, 3854)
PREVIOUS = {
    37, 3112, 3149, 3853, 3116, 3431, 3573, 3777, 2337, 2341, 3633,
    3841, 3792, 3496, 3794, 3795, 3800, 3803, 3979, 3865, 4684,
    4650, 4244, 3778, 4313, 3522, 3783, 3808, 3821, 3851, 4162, 2965, 3040,
    3440, 3520, 3589, 3623, 3802, 3807, 3810, 3863, 39, 40,
}
REMOVED = PREVIOUS | set(IDS)
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|implemented_by)\b|"
    r"\bLean\.ofReduceBool\b|\bmaxHeartbeats\s+0\b"
)
sys.path.insert(0, str(HERE))
import repair_census_membership_chains as chains


def archive_source(node: int) -> bytes:
    rel = f"ci-n11/drafts/energy/N11Formalization/EnergyRefineN{node:04d}.lean"
    raw = subprocess.check_output(
        ["git", "show", f"origin/ci/n11-build:{rel}"], cwd=HERE.parents[3])
    directive = b"set_option maxHeartbeats 0\n"
    assert raw.count(directive) == 1, node
    return raw.replace(directive, b"", 1)


def main() -> None:
    data = json.loads(CENSUS.read_text())
    ids = data["residual_ids"]
    assert len(ids) == 389
    assert hashlib.sha256(",".join(map(str, ids)).encode()).hexdigest().upper() == \
        data["residual_ids_sha256"]
    assert len(PREVIOUS) == 43
    assert set(IDS).isdisjoint(PREVIOUS)
    assert REMOVED <= set(ids)
    assert len(set(ids) - REMOVED) == 344

    source = MODULE.read_bytes()
    text = source.decode()
    assert not FORBIDDEN.search(text)
    assert "def newRefineIDs : Finset (Fin 5011) := {3825, 3854}" in text
    assert "refinedResidualIDs.card = 344" in text
    assert "b13_remaining_of_residual344" in text
    assert "EnergyTerminalResidualCensusRefine346.b13_remaining_of_residual346" in text
    chains.check_chain(text, MODULE)

    for node in IDS:
        path = FORMAL / f"EnergyRefineN{node}.lean"
        restored = path.read_bytes()
        assert restored == archive_source(node), node
        assert not FORBIDDEN.search(restored.decode()), node
        wrapper = (FORMAL / f"EnergyTerminalBatchB13Refine{node}.lean").read_text()
        main_wrapper = (FORMAL /
                        f"EnergyTerminalBatchB13Refine{node}Main.lean").read_text()
        assert f"EnergyRefineN{node}.newIDs" in wrapper
        assert "theorem paid_count : paidIDs.card = 1998" in wrapper
        assert f"main_of_energy_refine{node}_and_seven_classes" in main_wrapper
        assert not FORBIDDEN.search(wrapper + main_wrapper)

    targets = [line.strip() for line in (HERE / "TARGETS.txt").read_text().splitlines()
               if line.strip() and not line.startswith("#")]
    target = "N11Formalization.EnergyTerminalResidualCensusRefine344"
    assert targets.count(target) == 1
    assert len(targets) == len(set(targets))
    for dependency in (
        "N11Formalization.EnergyTerminalResidualCensusRefine346",
        "N11Formalization.EnergyTerminalBatchB13Refine3825",
        "N11Formalization.EnergyTerminalBatchB13Refine3854",
    ):
        assert targets.index(dependency) < targets.index(target), dependency

    py_compile.compile(__file__, doraise=True)
    print(json.dumps({
        "census_count": len(ids),
        "removed_count": len(REMOVED),
        "refined_count": len(set(ids) - REMOVED),
        "module_sha256": hashlib.sha256(source).hexdigest(),
        "restored_sha256": {
            str(node): hashlib.sha256((FORMAL /
                f"EnergyRefineN{node}.lean").read_bytes()).hexdigest()
            for node in IDS
        },
        "static_checks": "PASS",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
