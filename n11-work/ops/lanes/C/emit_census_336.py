#!/usr/bin/env python3
"""Restore archive drafts 3564/3569 and emit the 338 -> 336 bridge."""
from pathlib import Path
import hashlib

import emit_census_338 as prior
import emit_census_344 as archive

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"
IDS = (3564, 3569)


def bridge_text() -> str:
    text = prior.TEXT
    text = text.replace("b13_remaining_of_residual338", "b13_remaining_of_residual336")
    text = text.replace("b13_remaining_of_residual340", "b13_remaining_of_residual338")
    text = text.replace("EnergyTerminalResidualCensusRefine340", "PARENT_CENSUS")
    text = text.replace("EnergyTerminalResidualCensusRefine338",
                        "EnergyTerminalResidualCensusRefine336")
    text = text.replace("PARENT_CENSUS", "EnergyTerminalResidualCensusRefine338")
    text = text.replace("mem_340_", "mem_338_").replace("subset_340", "subset_338")
    text = text.replace("refinedResidualIDs.card = 338", "refinedResidualIDs.card = 336")
    text = text.replace("Remove archive draft refinements 38 and 3781 from the 340-id residual\ninterface, leaving an exact conditional residual of 338 ids.",
                        "Remove archive draft refinements 3564 and 3569 from the 338-id residual\ninterface, leaving an exact conditional residual of 336 ids.")
    text = text.replace("EnergyTerminalBatchB13Refine38\n", "EnergyTerminalBatchB13Refine3564\n")
    text = text.replace("EnergyTerminalBatchB13Refine3781\n", "EnergyTerminalBatchB13Refine3569\n")
    text = text.replace("refinements 38 and 3781", "refinements 3564 and 3569")
    text = text.replace("{38, 3781}", "{3564, 3569}")
    text = text.replace("not_sharp_38", "not_sharp_3564")
    text = text.replace("not_sharp_3781", "not_sharp_3569")
    text = text.replace("mem_338_38", "mem_338_3564")
    text = text.replace("mem_338_3781", "mem_338_3569")
    text = text.replace("(38 : Fin 5011)", "(3564 : Fin 5011)")
    text = text.replace("(3781 : Fin 5011)", "(3569 : Fin 5011)")
    text = text.replace("EnergyRefineN0038", "EnergyRefineN3564")
    text = text.replace("EnergyRefineN3781", "EnergyRefineN3569")
    text = text.replace("EnergyTerminalBatchB13Refine38.not_paid_38",
                        "EnergyTerminalBatchB13Refine3564.not_paid_3564")
    text = text.replace("EnergyTerminalBatchB13Refine3781.not_paid_3781",
                        "EnergyTerminalBatchB13Refine3569.not_paid_3569")
    text = text.replace("n ≠ 38 ∧ n ≠ 3781", "n ≠ 3564 ∧ n ≠ 3569")
    text = text.replace("n = 38", "n = 3564").replace("n = 3781", "n = 3569")
    text = text.replace("new_radius 38", "new_radius 3564")
    text = text.replace("new_radius 3781", "new_radius 3569")
    text = text.replace("hn38", "hn3564").replace("hn3781", "hn3569")
    chain_start = ("    EnergyTerminalResidualCensusRefine338.mem_refinedResidualIDs_iff,\n"
                   "    EnergyTerminalResidualCensusRefine342.mem_refinedResidualIDs_iff")
    chain_fixed = ("    EnergyTerminalResidualCensusRefine338.mem_refinedResidualIDs_iff,\n"
                   "    EnergyTerminalResidualCensusRefine340.mem_refinedResidualIDs_iff,\n"
                   "    EnergyTerminalResidualCensusRefine342.mem_refinedResidualIDs_iff")
    assert text.count(chain_start) == 2
    text = text.replace(chain_start, chain_fixed)
    assert "resolve" not in text
    assert "Remove archive draft refinements 3564 and 3569" in text
    assert "refinedResidualIDs.card = 336" in text
    assert "Refine338.refinedResidualIDs" in text
    assert "import N11Formalization.EnergyTerminalResidualCensusRefine338" in text
    assert not prior.FORBIDDEN.search(text)
    return text


def main() -> None:
    for node in IDS:
        source = archive.archive_source(node)
        path = LEAN / f"EnergyRefineN{node:04d}.lean"
        path.write_bytes(source)
        print(node, len(source), hashlib.sha256(source).hexdigest())
        archive.wrapper_files(node)
    output = LEAN / "EnergyTerminalResidualCensusRefine336.lean"
    output.write_text(bridge_text())
    print(output, hashlib.sha256(output.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
