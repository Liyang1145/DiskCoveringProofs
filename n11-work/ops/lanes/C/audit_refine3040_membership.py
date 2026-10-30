#!/usr/bin/env python3
"""Audit the literal Next1182 inventory used by the 3040 refinement wrapper."""

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3] / "lean" / "N11Formalization"


def main() -> None:
    components: dict[str, set[int]] = {}
    for part in range(1, 9):
        path = ROOT / f"Paid16GeneralNext1182S0{part}.lean"
        text = path.read_text(encoding="utf-8")
        pattern = r"^def (ids\d+) : Finset \(Fin 5011\) := \{([^}]*)\}"
        for match in re.finditer(pattern, text, re.MULTILINE):
            name, body = match.groups()
            components[f"S0{part}.{name}"] = {
                int(value) for value in re.findall(r"\d+", body)
            }

    union = set().union(*components.values())
    containing = [name for name, ids in components.items() if 3040 in ids]
    largest = max((len(ids), name) for name, ids in components.items())

    print(f"components={len(components)} union_card={len(union)}")
    print(f"3040_containing={containing}")
    print(f"largest_component={largest[0]} ({largest[1]})")
    assert len(components) == 57
    assert len(union) == 1182
    assert not containing
    assert largest[0] <= 21


if __name__ == "__main__":
    main()
