#!/usr/bin/env python3
"""Static/exact-set audit for the conditional 336-id residual bridge."""
from pathlib import Path
import hashlib
import json
import py_compile
import sys

import emit_census_336 as emitter
import verify_census_338 as prior338

HERE = Path(__file__).resolve().parent
FORMAL = HERE.parents[2] / "lean" / "N11Formalization"
CENSUS = HERE / "residual389-census.json"
MODULE = FORMAL / "EnergyTerminalResidualCensusRefine336.lean"
IDS = (3564, 3569)
REMOVED = prior338.REMOVED | set(IDS)
sys.path.insert(0, str(HERE))
import repair_census_membership_chains as chains


def main() -> None:
    data = json.loads(CENSUS.read_text())
    ids = data["residual_ids"]
    assert len(ids) == 389
    assert hashlib.sha256(",".join(map(str, ids)).encode()).hexdigest().upper() == \
        data["residual_ids_sha256"]
    assert len(prior338.REMOVED) == 51
    assert set(IDS).isdisjoint(prior338.REMOVED)
    assert REMOVED <= set(ids)
    assert len(set(ids) - REMOVED) == 336

    text = MODULE.read_text()
    assert not emitter.prior.FORBIDDEN.search(text)
    assert "import N11Formalization.EnergyTerminalResidualCensusRefine338" in text
    assert "def newRefineIDs : Finset (Fin 5011) := {3564, 3569}" in text
    assert "refinedResidualIDs.card = 336" in text
    assert "b13_remaining_of_residual336" in text
    chains.check_chain(text, MODULE)

    for node in IDS:
        path = FORMAL / f"EnergyRefineN{node:04d}.lean"
        assert path.read_bytes() == emitter.archive.archive_source(node), node
        wrapper = (FORMAL / f"EnergyTerminalBatchB13Refine{node}.lean").read_text()
        main_wrapper = (FORMAL / f"EnergyTerminalBatchB13Refine{node}Main.lean").read_text()
        assert f"EnergyRefineN{node:04d}.newIDs" in wrapper
        assert "theorem paid_count : paidIDs.card = 1998" in wrapper
        assert f"main_of_energy_refine{node}_and_seven_classes" in main_wrapper
        assert not emitter.prior.FORBIDDEN.search(wrapper + main_wrapper)

    targets = [line.strip() for line in (HERE / "TARGETS.txt").read_text().splitlines()
               if line.strip() and not line.startswith("#")]
    target = "N11Formalization.EnergyTerminalResidualCensusRefine336"
    assert targets.count(target) == 1
    for dependency in (
        "N11Formalization.EnergyTerminalResidualCensusRefine338",
        "N11Formalization.EnergyTerminalBatchB13Refine3564",
        "N11Formalization.EnergyTerminalBatchB13Refine3569",
    ):
        assert targets.index(dependency) < targets.index(target), dependency

    py_compile.compile(__file__, doraise=True)
    print(json.dumps({
        "census_count": len(ids), "removed_count": len(REMOVED),
        "refined_count": len(set(ids) - REMOVED), "static_checks": "PASS",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
