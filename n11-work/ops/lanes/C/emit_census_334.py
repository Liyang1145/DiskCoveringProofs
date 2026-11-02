#!/usr/bin/env python3
"""Restore archive drafts 3578/3738 and emit the 336 -> 334 bridge."""
from pathlib import Path
import hashlib

import emit_census_336 as prior
import emit_census_344 as archive

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"
IDS = (3578, 3738)


def bridge_text() -> str:
    text = prior.bridge_text()
    text = text.replace("Refine336", "Refine334")
    text = text.replace("Refine338", "Refine336")
    text = text.replace("refinements 3564 and 3569", "refinements 3578 and 3738")
    text = text.replace("338-id residual", "336-id residual")
    text = text.replace("residual of 336 ids", "residual of 334 ids")
    text = text.replace("{3564, 3569}", "{3578, 3738}")
    text = text.replace("not_sharp_3564", "not_sharp_3578")
    text = text.replace("not_sharp_3569", "not_sharp_3738")
    text = text.replace("mem_338_3564", "mem_336_3578")
    text = text.replace("mem_338_3569", "mem_336_3738")
    text = text.replace("newRefineIDs_subset_338", "newRefineIDs_subset_336")
    text = text.replace("(3564 : Fin 5011)", "(3578 : Fin 5011)")
    text = text.replace("(3569 : Fin 5011)", "(3738 : Fin 5011)")
    text = text.replace("n ≠ 3564 ∧ n ≠ 3569", "n ≠ 3578 ∧ n ≠ 3738")
    text = text.replace("EnergyRefineN3564", "EnergyRefineN3578")
    text = text.replace("EnergyRefineN3569", "EnergyRefineN3738")
    text = text.replace("BatchB13Refine3564", "BatchB13Refine3578")
    text = text.replace("BatchB13Refine3569", "BatchB13Refine3738")
    text = text.replace("hn3564", "hn3578").replace("hn3569", "hn3738")
    text = text.replace("card = 336", "card = 334")
    text = text.replace("b13_remaining_of_residual336", "b13_remaining_of_residual334")
    text = text.replace(".b13_remaining_of_residual338", ".b13_remaining_of_residual336")
    text = text.replace("3564", "3578").replace("3569", "3738")
    assert "3564" not in text and "3569" not in text
    assert "card = 334" in text and "import N11Formalization.EnergyTerminalResidualCensusRefine336" in text
    assert not archive.FORBIDDEN.search(text)
    return text


def main() -> None:
    for node in IDS:
        source = archive.archive_source(node)
        path = LEAN / f"EnergyRefineN{node:04d}.lean"
        path.write_bytes(source)
        print(node, len(source), hashlib.sha256(source).hexdigest())
        archive.wrapper_files(node)
    output = LEAN / "EnergyTerminalResidualCensusRefine334.lean"
    output.write_text(bridge_text())
    print(output, hashlib.sha256(output.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
