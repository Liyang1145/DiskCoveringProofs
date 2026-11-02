#!/usr/bin/env python3
"""Repair or check parent-to-root rewrites in the refined residual census.

Each `mem_refinedResidualIDs_iff` theorem unfolds exactly one subtraction.  A
membership proof for an id must therefore rewrite through every intervening
module down to `RefineTriple`; skipping a module leaves an unmatched set
expression.  This script normalises those literal rewrite blocks and checks
that every block is the contiguous suffix of the known module chain.
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"

ORDER = [
    "336", "338", "340", "342", "344", "346", "348", "350", "352", "354", "356",
    "358", "360", "362", "364", "366", "368", "371", "373", "375", "376",
    "377", "378", "385", "Triple",
]
MODULES = ["336", "346", "348", "350", "352", "354", "356", "358", "360", "362"]
CHAIN_RE = re.compile(
    r"rw \[\s*(?P<chain>EnergyTerminalResidualCensusRefine(?:\d+|Triple)"
    r"\.mem_refinedResidualIDs_iff(?:,\s*EnergyTerminalResidualCensusRefine"
    r"(?:\d+|Triple)\.mem_refinedResidualIDs_iff)*)\]",
    re.S,
)


def module_path(number: str) -> Path:
    return LEAN / f"EnergyTerminalResidualCensusRefine{number}.lean"


def expected_chain(text: str, path: Path) -> str:
    match = CHAIN_RE.search(text)
    if match is None:
        raise AssertionError(f"no membership rewrite block in {path.name}")
    first = re.search(r"Refine(\d+|Triple)\.mem_refinedResidualIDs_iff",
                      match.group("chain"))
    assert first is not None
    start = ORDER.index(first.group(1))
    if start >= len(ORDER) - 1:
        raise AssertionError(f"rewrite already starts at root in {path.name}")
    lines = [
        f"    EnergyTerminalResidualCensusRefine{number}.mem_refinedResidualIDs_iff"
        for number in ORDER[start:]
    ]
    return "rw [\n" + ",\n".join(lines) + "]"


def repair(text: str, path: Path) -> str:
    blocks = [match for match in CHAIN_RE.finditer(text)
              if "RefineTriple.mem_refinedResidualIDs_iff" in match.group("chain")]
    assert len(blocks) == 2, (path.name, len(blocks))
    for match in reversed(blocks):
        replacement = expected_chain(match.group(0), path)
        text = text[:match.start()] + replacement + text[match.end():]
    return text


def check_chain(text: str, path: Path) -> None:
    blocks = [match for match in CHAIN_RE.finditer(text)
              if "RefineTriple.mem_refinedResidualIDs_iff" in match.group("chain")]
    assert len(blocks) == 2, (path.name, len(blocks))
    for match in blocks:
        names = re.findall(
            r"EnergyTerminalResidualCensusRefine(\d+|Triple)"
            r"\.mem_refinedResidualIDs_iff",
            match.group("chain"),
        )
        start = ORDER.index(names[0])
        assert names == ORDER[start:], (path.name, names, ORDER[start:])
        assert names[-1] == "Triple", path.name


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    changed: list[str] = []
    for number in MODULES:
        path = module_path(number)
        text = path.read_text()
        if args.check:
            check_chain(text, path)
            continue
        fixed = repair(text, path)
        check_chain(fixed, path)
        if fixed != text:
            path.write_text(fixed)
            changed.append(path.name)
    print({"mode": "check" if args.check else "repair", "changed": changed})


if __name__ == "__main__":
    main()
