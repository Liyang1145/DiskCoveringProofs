#!/usr/bin/env python3
"""Repair the lane-C low-id refinement wrappers for source terminals 39 and 40.

The terminal certificates themselves are unchanged.  N39's false terminal
branches now eliminate `False`; both B13 batches factor Next505 nonmembership
through 25 literal blocks of 21 ids, and N40 uses its emitted namespace.
"""
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"


def next505_helpers(i: int) -> str:
    name = f"0039" if i == 39 else "40"
    parts = "\n".join(
        f"private theorem not_next505_part{k:02d} :\n"
        f"    ({i} : Fin 5011) ∉ Paid16GeneralNext505.ids{k:02d} := by\n"
        f"  decide +kernel"
        for k in range(25)
    )
    tuple_lines = ",\n    ".join(
        f"not_next505_part{k:02d}" for k in range(25)
    )
    return f"""{parts}
private theorem not_next505 :
    ({i} : Fin 5011) ∉ Paid16GeneralNext505.newIDs := by
  rw [Paid16GeneralNext505.new_mem]
  push_neg
  exact ⟨{tuple_lines}⟩

"""


def patch_batch(path: Path, source_id: int, paid_name: str,
                old_name: str, new_name: str) -> None:
    text = path.read_text()
    text = text.replace(old_name, new_name)
    marker = f"theorem {paid_name} :"
    if paid_name in text and text.count(marker) != 1:
        raise SystemExit(f"unexpected not_paid marker in {path}")
    if "theorem not_next505 :" not in text:
        text = text.replace(marker, next505_helpers(source_id) + marker, 1)
    old_branch = (
        "    · have hlt := EnergyTerminalBatchB13Next505Bounds.next505_lt "
        f"({source_id} : Fin 5011) h505\n"
        "      omega\n"
    )
    if old_branch in text:
        if text.count(old_branch) != 1:
            raise SystemExit(f"unexpected Next505 branch in {path}")
        text = text.replace(old_branch, "    · exact not_next505 h505\n", 1)
    elif "    · exact not_next505 h505\n" not in text:
        raise SystemExit(f"missing Next505 branch in {path}")
    path.write_text(text)


def patch_39() -> None:
    path = LEAN / "EnergyRefineN0039Repair.lean"
    text = path.read_text()
    old = "  · exact Bool.false_ne_true hl\n"
    if text.count(old) not in (0, 6):
        raise SystemExit("unexpected N39 false-branch count")
    text = text.replace(old, "  · exact False.elim (Bool.false_ne_true hl)\n")
    path.write_text(text)


def main() -> None:
    patch_39()
    patch_batch(
        LEAN / "EnergyTerminalBatchB13Refine0039.lean",
        39,
        "not_paid_0039",
        "EnergyRefineN0039",
        "EnergyRefineN0039",
    )
    patch_batch(
        LEAN / "EnergyTerminalBatchB13Refine40.lean",
        40,
        "not_paid_40",
        "EnergyRefineN40",
        "EnergyRefineN0040",
    )


if __name__ == "__main__":
    main()
