#!/usr/bin/env python3
"""Portable source audit of the 25-step C450 telescope.

This is a lane-local wrapper around the frozen ``verify_telescope.py`` logic.
It checks source shape only; kernel acceptance remains a CI obligation.
"""

import hashlib
import re
from pathlib import Path


REPO = Path(__file__).resolve().parents[4]
BASE = REPO / "n11-work" / "lean" / "N11Formalization"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    violations: list[tuple[int, object]] = []
    print("S -> name / conclusion / own-paid / predecessor-import / body-uses-paid")
    for segment in range(12, 37):
        path = BASE / f"C450Source{segment}Segment.lean"
        if not path.exists():
            violations.append((segment, "MISSING FILE"))
            print(f"{segment:2d}  MISSING FILE")
            continue
        text = path.read_text(encoding="utf-8")
        predecessor = segment - 1
        checks = {
            "name": f"theorem source{predecessor}_remaining_of_remaining" in text,
            "conclusion": (
                f"C450Source{predecessor}Segment.RemainingSourceObligation" in text
            ),
            "paid": f"source{segment}_paid" in text,
            "import": (
                f"import N11Formalization.C450Source{predecessor}Segment" in text
            ),
        }
        body = re.search(
            rf"theorem source{predecessor}_remaining_of_remaining.*?"
            r"(?=\ntheorem |\nend )",
            text,
            re.S,
        )
        checks["body"] = bool(body) and f"source{segment}_paid" in body.group(0)
        if not all(checks.values()):
            violations.append((segment, checks))
        flags = " / ".join(str(int(checks[key])) for key in (
            "name", "conclusion", "paid", "import", "body"
        ))
        print(f"{segment:2d}  {flags}  {'OK' if all(checks.values()) else 'BAD'}")

    source11 = (BASE / "C450Source11Segment.lean").read_text(encoding="utf-8")
    source36 = (BASE / "C450Source36Segment.lean").read_text(encoding="utf-8")
    terminal = {
        "source11_defines_interface": "def RemainingSourceObligation" in source11,
        "source11_remaining_25": "remainingSegs.length = 25" in source11,
        "source36_drop_36": "c450Segs.drop 36" in source36,
        "source36_remaining_0": "remainingSegs.length = 0" in source36,
        "source36_has_paid": "source36_paid" in source36,
    }
    arithmetic: list[tuple[int, int, int]] = []
    for segment in range(11, 37):
        text = (BASE / f"C450Source{segment}Segment.lean").read_text(encoding="utf-8")
        drop_match = re.search(r"c450Segs\.drop (\d+)", text)
        count_match = re.search(
            r"remaining_count\s*:\s*remainingSegs\.length = (\d+)", text
        )
        if not drop_match or not count_match:
            violations.append((segment, "UNPARSED DROP/COUNT"))
            continue
        drop, count = int(drop_match.group(1)), int(count_match.group(1))
        if drop + count != 36:
            violations.append((segment, f"drop {drop} + count {count} != 36"))
        arithmetic.append((segment, drop, count))

    print("\nterminal facts")
    for name, ok in terminal.items():
        print(f"  {name}: {ok}")
        if not ok:
            violations.append((11 if "source11" in name else 36, name))
    print(f"arithmetic rows checked: {len(arithmetic)}/26")
    print(f"source modules checked: {len(list(BASE.glob('C450Source*Segment.lean')))}")
    print(f"violations: {len(violations)}")
    for violation in violations:
        print(" ", violation)
    for path in (
        BASE / "C450ChainCompletion.lean",
        BASE / "C450ChainCompletionMain.lean",
    ):
        print(f"sha256 {path.name}: {digest(path)}")
    return 1 if violations else 0


if __name__ == "__main__":
    raise SystemExit(main())
