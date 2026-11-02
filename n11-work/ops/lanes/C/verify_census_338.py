#!/usr/bin/env python3
"""Static/exact-set audit for the conditional 338-id residual bridge."""
from pathlib import Path
import hashlib
import json
import py_compile
import sys

import emit_census_338 as emitter
import verify_census_340 as prior340

HERE = Path(__file__).resolve().parent
FORMAL = HERE.parents[2] / "lean" / "N11Formalization"
CENSUS = HERE / "residual389-census.json"
MODULE = FORMAL / "EnergyTerminalResidualCensusRefine338.lean"
IDS = (38, 3781)
REMOVED = prior340.REMOVED | set(IDS)
sys.path.insert(0, str(HERE))
import repair_census_membership_chains as chains


def restored_name(node: int) -> str:
    return f"EnergyRefineN{node:04d}.lean"


def main() -> None:
    data = json.loads(CENSUS.read_text())
    ids = data["residual_ids"]
    assert len(ids) == 389
    assert hashlib.sha256(",".join(map(str, ids)).encode()).hexdigest().upper() == \
        data["residual_ids_sha256"]
    assert len(prior340.REMOVED) == 49
    assert set(IDS).isdisjoint(prior340.REMOVED)
    assert REMOVED <= set(ids)
    assert len(set(ids) - REMOVED) == 338

    source = MODULE.read_bytes()
    text = source.decode()
    assert not emitter.FORBIDDEN.search(text)
    assert "def newRefineIDs : Finset (Fin 5011) := {38, 3781}" in text
    assert "refinedResidualIDs.card = 338" in text
    assert "b13_remaining_of_residual338" in text
    assert "EnergyTerminalResidualCensusRefine340.b13_remaining_of_residual340" in text
    chains.check_chain(text, MODULE)

    for node in IDS:
        path = FORMAL / restored_name(node)
        restored = path.read_bytes()
        assert restored == emitter.prior.prior.prior.archive_source(node), node
        assert not emitter.FORBIDDEN.search(restored.decode()), node
        wrapper = (FORMAL / f"EnergyTerminalBatchB13Refine{node}.lean").read_text()
        main_wrapper = (FORMAL /
                        f"EnergyTerminalBatchB13Refine{node}Main.lean").read_text()
        source_module = f"EnergyRefineN{node:04d}"
        assert f"{source_module}.newIDs" in wrapper
        assert "theorem paid_count : paidIDs.card = 1998" in wrapper
        assert f"main_of_energy_refine{node}_and_seven_classes" in main_wrapper
        assert not emitter.FORBIDDEN.search(wrapper + main_wrapper)

    targets = [line.strip() for line in (HERE / "TARGETS.txt").read_text().splitlines()
               if line.strip() and not line.startswith("#")]
    target = "N11Formalization.EnergyTerminalResidualCensusRefine338"
    assert targets.count(target) == 1
    assert len(targets) == len(set(targets))
    for dependency in (
        "N11Formalization.EnergyTerminalResidualCensusRefine340",
        "N11Formalization.EnergyTerminalBatchB13Refine38",
        "N11Formalization.EnergyTerminalBatchB13Refine3781",
    ):
        assert targets.index(dependency) < targets.index(target), dependency

    py_compile.compile(__file__, doraise=True)
    print(json.dumps({
        "census_count": len(ids),
        "removed_count": len(REMOVED),
        "refined_count": len(set(ids) - REMOVED),
        "module_sha256": hashlib.sha256(source).hexdigest(),
        "restored_sha256": {
            str(node): hashlib.sha256((FORMAL / restored_name(node)).read_bytes()).hexdigest()
            for node in IDS
        },
        "static_checks": "PASS",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
