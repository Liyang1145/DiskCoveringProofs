#!/usr/bin/env python3
"""Compare the seven frozen survey failures with the public canonical payloads.

This is an exact-rational audit. It does not elaborate Lean or establish
kernel credit.
"""
from __future__ import annotations

import hashlib
import json
import re
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SURVEY = ROOT / "n11-work/evidence-20261028/inputs/paid16-general-next512.json"
CORE = ROOT / "n11-work/lean/N11Formalization/FrozenCapRationalCore.lean"
OUT = HERE / "audit_1409_canonical_record-report.json"
SURVEY_SHA256 = "F49F06FC57A818E464D8DCBDAACE2E4D57A3C2E84CEA27FE86C4551363F3DD16"
PUBLIC_IDS = (1409, 2337, 2341, 2356, 2360, 2368, 2370)
T2 = Q(1899919265599193545242591, 5000000000000000000000000) ** 2


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def lean_fraction(text: str) -> Q:
    if re.search(r"\(0\s*:\s*ℚ\)", text):
        return Q(0)
    values = re.findall(r"(-?\d+)\s*:\s*ℚ\)\s*/\s*(\d+)", text)
    if len(values) != 1:
        raise ValueError(f"expected one Lean rational, got {text!r}")
    return Q(int(values[0][0]), int(values[0][1]))


def payload(core: str, node: int) -> tuple[Q, list[Q]]:
    f0_match = re.search(rf"def F0_{node} : ℚ := (.*)", core)
    g_match = re.search(rf"def G_{node} : Fin 9 → ℚ := (.*)", core)
    if f0_match is None or g_match is None:
        raise ValueError(f"canonical payload {node} not found")
    g = [lean_fraction(item) for item in g_match.group(1).split(",")]
    if len(g) != 9:
        raise ValueError(f"node {node}: expected nine canonical g entries, got {len(g)}")
    return lean_fraction(f0_match.group(1)), g


def main() -> int:
    if sha256(SURVEY) != SURVEY_SHA256:
        raise SystemExit("frozen survey hash changed")
    survey = json.loads(SURVEY.read_text(encoding="utf-8-sig"))
    failures = sorted(r["id"] for r in survey["records"] if r["pass"] is False)
    if failures != list(PUBLIC_IDS):
        raise SystemExit(f"unexpected survey failure set: {failures}")
    core = CORE.read_text(encoding="utf-8")
    checked = []
    for node in PUBLIC_IDS:
        record = next(r for r in survey["records"] if r["id"] == node)
        f0, g = payload(core, node)
        gap = Q(record["lower"]) - T2
        item = {
            "id": node,
            "survey_pass": record["pass"],
            "f0_matches_public_canonical": Q(record["f0Lo"]) == f0,
            "g_matches_public_canonical": [Q(x) for x in record["g"]] == g,
            "lower_identity_holds": Q(record["lower"])
            == Q(record["f0Lo"]) - Q(record["lamB"]) + Q(record["rmin"]),
            "lower_minus_T_squared": str(gap),
            "lower_minus_T_squared_negative": gap < 0,
        }
        if not all(
            (
                not item["survey_pass"],
                item["f0_matches_public_canonical"],
                item["g_matches_public_canonical"],
                item["lower_identity_holds"],
                item["lower_minus_T_squared_negative"],
            )
        ):
            raise SystemExit(json.dumps(item, indent=2))
        checked.append(item)
    report = {
        "scope": "exact Python source audit; not Lean elaboration or kernel credit",
        "survey_sha256": sha256(SURVEY),
        "core_sha256": sha256(CORE),
        "survey_records": len(survey["records"]),
        "survey_failure_ids": failures,
        "public_ids": list(PUBLIC_IDS),
        "all_failures_are_public_and_canonical": True,
        "records": checked,
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
