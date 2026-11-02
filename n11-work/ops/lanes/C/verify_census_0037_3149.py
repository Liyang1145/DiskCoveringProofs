#!/usr/bin/env python3
"""Static and exact membership audit for the narrowed residual censuses."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"
MODULE = LEAN / "EnergyTerminalResidualCensusRefine0037Refine3149.lean"
MODULE_TRIPLE = LEAN / "EnergyTerminalResidualCensusRefineTriple.lean"
MODULE_385 = LEAN / "EnergyTerminalResidualCensusRefine385.lean"
CENSUS = HERE / "residual389-census.json"
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
    assert 37 in ids and 3149 in ids and 3853 in ids
    assert len(set(ids) - {37, 3149}) == 387
    assert len(set(ids) - {37, 3149, 3853}) == 386
    assert len(set(ids) - {37, 3112, 3149, 3853}) == 385

    source = MODULE.read_bytes()
    text = source.decode()
    assert not FORBIDDEN.search(text)
    assert "def newRefineIDs : Finset (Fin 5011) := {37, 3149}" in text
    assert "refinedResidualIDs.card = 387" in text
    assert "not_sharp_0037" in text and "not_sharp_3149" in text

    triple_source = MODULE_TRIPLE.read_bytes()
    triple_text = triple_source.decode()
    assert not FORBIDDEN.search(triple_text)
    assert "def newRefineIDs : Finset (Fin 5011) := {37, 3149, 3853}" in triple_text
    assert "refinedResidualIDs.card = 386" in triple_text
    assert "not_sharp_3853" in triple_text

    source_385 = MODULE_385.read_bytes()
    text_385 = source_385.decode()
    assert not FORBIDDEN.search(text_385)
    assert "refinedResidualIDs.card = 385" in text_385
    assert "not_sharp_3112" in text_385
    print(json.dumps({
        "census_count": len(ids),
        "refined_387_count": len(set(ids) - {37, 3149}),
        "refined_386_count": len(set(ids) - {37, 3149, 3853}),
        "refined_385_count": len(set(ids) - {37, 3112, 3149, 3853}),
        "module_sha256": hashlib.sha256(source).hexdigest(),
        "triple_module_sha256": hashlib.sha256(triple_source).hexdigest(),
        "module_385_sha256": hashlib.sha256(source_385).hexdigest(),
        "static_checks": "PASS",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
