#!/usr/bin/env python3
"""Static closure and API audit for the conditional B13 main wrapper.

This checks names and imports in source; it does not elaborate Lean and is not
proof credit.  B13Main remains outside TARGETS until B13 itself is CI green.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
LEAN = ROOT / "n11-work" / "lean"
MAIN = LEAN / "N11Formalization" / "EnergyTerminalBatchB13Main.lean"
CENSUS = LEAN / "N11Formalization" / "EnergyTerminalResidualCensus.lean"
TARGETS = Path(__file__).with_name("TARGETS.txt")
REPORT = Path(__file__).with_name("audit_b13main-report.json")
IMPORT = re.compile(r"^import\s+(N11Formalization(?:\.\w+)+)\s*$", re.MULTILINE)
BANNED = ("sorry", "admit", "native_decide", "ofReduceBool", "implemented_by",
          "maxHeartbeats 0", "maxRecDepth")


def module_path(module: str) -> Path:
    return LEAN.joinpath(*module.split(".")).with_suffix(".lean")


def main() -> None:
    text = MAIN.read_text()
    targets = [line.strip() for line in TARGETS.read_text().splitlines()
               if line.strip() and not line.lstrip().startswith("#")]
    missing: list[dict[str, str]] = []
    imports = IMPORT.findall(text)
    for module in imports:
        path = module_path(module)
        if not path.is_file():
            missing.append({"module": module,
                            "expected": str(path.relative_to(ROOT))})

    forbidden = [token for token in BANNED
                 if re.search(r"(?<![\w.])" + re.escape(token) + r"(?![\w])", text)]
    required_names = [
        "C450ChainCompletionMain.main_of_energy_and_seven_classes",
        "EnergyTerminalBatchB12.remaining_of_b12",
        "EnergyTerminalBatchB13.remaining_of_b13",
        "EnergyTerminalResidualCensus.remaining_iff_b13",
        "main_of_energy_b13_and_seven_classes",
        "main_of_energy_literal_and_seven_classes",
        "full_disk_bound_of_energy_b13_and_seven_classes",
        "full_disk_bound_of_energy_literal_and_seven_classes",
    ]
    missing_names = [name for name in required_names if name not in text]
    census_text = CENSUS.read_text()
    census_api = ["remaining_iff_b13" in census_text,
                  "remaining_of_b13" in text]
    result = {
        "root": str(MAIN.relative_to(ROOT)),
        "direct_imports": len(imports),
        "missing_imports": missing,
        "forbidden_main": forbidden,
        "missing_required_names": missing_names,
        "census_api_present": all(census_api),
        "in_targets": "N11Formalization.EnergyTerminalBatchB13Main" in targets,
        "scope": "static source/import/API audit only; no Lean elaboration",
        "ok": not missing and not forbidden and not missing_names and all(census_api),
    }
    REPORT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, sort_keys=True))
    raise SystemExit(0 if result["ok"] else 1)


if __name__ == "__main__":
    main()
