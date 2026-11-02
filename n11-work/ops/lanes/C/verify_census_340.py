#!/usr/bin/env python3
"""Static/exact-set audit for the conditional 340-id residual bridge."""
from pathlib import Path
import hashlib
import json
import py_compile
import sys

import emit_census_340 as emitter
import verify_census_342 as prior342

HERE = Path(__file__).resolve().parent
FORMAL = HERE.parents[2] / "lean" / "N11Formalization"
CENSUS = HERE / "residual389-census.json"
MODULE = FORMAL / "EnergyTerminalResidualCensusRefine340.lean"
IDS = (3432, 3550)
REMOVED = prior342.REMOVED | set(IDS)
sys.path.insert(0, str(HERE))
import repair_census_membership_chains as chains


def main() -> None:
    data = json.loads(CENSUS.read_text())
    ids = data["residual_ids"]
    assert len(ids) == 389
    assert hashlib.sha256(",".join(map(str, ids)).encode()).hexdigest().upper() == \
        data["residual_ids_sha256"]
    assert len(prior342.REMOVED) == 47
    assert set(IDS).isdisjoint(prior342.REMOVED)
    assert REMOVED <= set(ids)
    assert len(set(ids) - REMOVED) == 340

    source = MODULE.read_bytes()
    text = source.decode()
    assert not emitter.FORBIDDEN.search(text)
    assert "def newRefineIDs : Finset (Fin 5011) := {3432, 3550}" in text
    assert "refinedResidualIDs.card = 340" in text
    assert "b13_remaining_of_residual340" in text
    assert "EnergyTerminalResidualCensusRefine342.b13_remaining_of_residual342" in text
    chains.check_chain(text, MODULE)

    for node in IDS:
        path = FORMAL / f"EnergyRefineN{node}.lean"
        restored = path.read_bytes()
        assert restored == emitter.prior.prior.archive_source(node), node
        assert not emitter.FORBIDDEN.search(restored.decode()), node
        wrapper = (FORMAL / f"EnergyTerminalBatchB13Refine{node}.lean").read_text()
        main_wrapper = (FORMAL /
                        f"EnergyTerminalBatchB13Refine{node}Main.lean").read_text()
        assert f"EnergyRefineN{node}.newIDs" in wrapper
        assert "theorem paid_count : paidIDs.card = 1998" in wrapper
        assert f"main_of_energy_refine{node}_and_seven_classes" in main_wrapper
        assert not emitter.FORBIDDEN.search(wrapper + main_wrapper)

    targets = [line.strip() for line in (HERE / "TARGETS.txt").read_text().splitlines()
               if line.strip() and not line.startswith("#")]
    target = "N11Formalization.EnergyTerminalResidualCensusRefine340"
    assert targets.count(target) == 1
    assert len(targets) == len(set(targets))
    for dependency in (
        "N11Formalization.EnergyTerminalResidualCensusRefine342",
        "N11Formalization.EnergyTerminalBatchB13Refine3432",
        "N11Formalization.EnergyTerminalBatchB13Refine3550",
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
