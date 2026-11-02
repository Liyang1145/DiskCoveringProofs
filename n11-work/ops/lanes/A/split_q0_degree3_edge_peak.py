#!/usr/bin/env python3
"""Split the q0 degree-three edge-peak checks into bounded Lean modules.

The pre-split source is read from its frozen commit so this emitter is
deterministic after the assembler replaces the working-tree file.  Proof blocks
are moved byte-for-byte; only module headers and the assembler are emitted.
"""
from __future__ import annotations

import argparse
import hashlib
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
REL = "n11-work/lean/N11Formalization/SevenClassQ0Deg3UpperReductionUnimodal.lean"
DEFAULT_REV = "a0f0f971"
SOURCE_SHA256 = "69e6eabf59a15a034a8c3bb8b53b665a85f785a7191227960b8d2533ab92c367"
NS = "N11Formalization.SevenClassQ0Deg3UpperReductionUnimodal"
GROUPS = (
    ("SevenClassQ0Deg3UpperReductionUnimodalPeaks0To6", range(0, 7)),
    ("SevenClassQ0Deg3UpperReductionUnimodalPeaks7To13", range(7, 14)),
    ("SevenClassQ0Deg3UpperReductionUnimodalPeaks14To20", range(14, 21)),
)
ROW_MODULE = "SevenClassQ0Deg3UpperReductionUnimodalPeak{:02d}"
ROWS = tuple((ROW_MODULE.format(i), i) for i in range(21))


def read_source(rev: str, source_file: Path | None) -> str:
    if source_file is not None:
        data = source_file.read_bytes()
    else:
        data = subprocess.check_output(["git", "show", f"{rev}:{REL}"], cwd=ROOT)
    digest = hashlib.sha256(data).hexdigest()
    if digest != SOURCE_SHA256:
        raise ValueError(f"pre-split source hash {digest} != {SOURCE_SHA256}")
    return data.decode("utf-8")


def proof_blocks(source: str) -> dict[int, str]:
    pattern = re.compile(
        r"(?m)^theorem edgePeakValid_(\d+) : EdgePeakValid \1 := by\n"
        r"(?:  [^\n]*\n|    [^\n]*\n)+"
    )
    blocks = {int(match.group(1)): match.group(0).rstrip("\n") for match in pattern.finditer(source)}
    if sorted(blocks) != list(range(21)):
        raise ValueError(f"expected edgePeakValid_0..20, got {sorted(blocks)}")
    return blocks


def emit() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-rev", default=DEFAULT_REV)
    parser.add_argument("--source-file", type=Path)
    args = parser.parse_args()
    source = read_source(args.source_rev, args.source_file)
    marker = "\n/-- The 21 peak comparisons recorded by the exact rational audit"
    base = source[: source.index(marker)].rstrip("\n") + "\n"
    old_coeff = "    fin_cases i <;> norm_num [edgeCoeff, tableEdges, mu]\n"
    new_coeff = "    fin_cases i <;> norm_num [edgeCoeff, tableEdges, mu] <;> decide +kernel\n"
    if base.count(old_coeff) != 1:
        raise ValueError("expected one exact edge-coefficient proof block")
    base = base.replace(old_coeff, new_coeff, 1)
    base += f"\nend {NS}\n"
    lean = ROOT / "n11-work/lean/N11Formalization"
    (lean / "SevenClassQ0Deg3UpperReductionUnimodalBase.lean").write_text(base, encoding="utf-8")

    blocks = proof_blocks(source)
    for module, index in ROWS:
        header = (
            "import N11Formalization.SevenClassQ0Deg3UpperReductionUnimodalBase\n\n"
            f"/-! Bounded edge-peak check {index}. -/\n"
            "set_option autoImplicit false\nnoncomputable section\n"
            f"namespace {NS}\n\n"
            "open MetricAreaRationalCertificate\nopen SevenClassQ0Deg3UpperTables\n\n"
            "attribute [local simp] edgeUpper nodeQ edgeCoeff tableEdges\n\n"
        )
        body = blocks[index]
        text = header + body + f"\n\nend {NS}\n"
        (lean / f"{module}.lean").write_text(text, encoding="utf-8")

    for module, indices in GROUPS:
        imports = "\n".join(
            [f"import N11Formalization.{ROW_MODULE.format(i)}" for i in indices]
        )
        text = (
            imports
            + f"\n\n/-! Assembler for bounded edge-peak checks {indices.start}--{indices.stop - 1}. -/\n"
        )
        (lean / f"{module}.lean").write_text(text, encoding="utf-8")

    imports = "\n".join(
        ["import N11Formalization.SevenClassQ0Deg3UpperReductionUnimodalBase"]
        + [f"import N11Formalization.{module}" for module, _ in GROUPS]
    )
    first, last = source.index("/-- All 21 peaks"), source.index("\nend " + NS)
    assembler = (
        imports
        + "\n\n/-! Lane A: thin assembler for the bounded q0 edge-peak modules. -/\n"
        + "set_option autoImplicit false\nnoncomputable section\n"
        + f"namespace {NS}\n\n"
        + source[first:last].rstrip("\n")
        + "\n\nend "
        + NS
        + "\n"
        + f"#check @{NS}.edgeValid_of_unimodal\n"
        + f"#check @{NS}.edgeValid_of_monotone\n"
        + f"#print axioms {NS}.edgeValid_of_unimodal\n"
        + f"#print axioms {NS}.edgePeakValid_all\n"
    )
    (lean / "SevenClassQ0Deg3UpperReductionUnimodal.lean").write_text(assembler, encoding="utf-8")


if __name__ == "__main__":
    try:
        emit()
    except Exception as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
