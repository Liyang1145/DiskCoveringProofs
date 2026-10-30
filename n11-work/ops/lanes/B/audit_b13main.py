#!/usr/bin/env python3
"""Static closure and API audit for the core conditional B13 main wrapper.

This checks names and imports in source; it does not elaborate Lean and is not
proof credit.  B13Main is queued in TARGETS behind B13; it remains unpaid until
CI builds both modules.  The optional literal-census wrapper is deliberately
separate because its lane-C source is not a B13Main prerequisite.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
LEAN = ROOT / "n11-work" / "lean"
MAIN = LEAN / "N11Formalization" / "EnergyTerminalBatchB13Main.lean"
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
        "main_of_energy_b13_and_seven_classes",
        "full_disk_bound_of_energy_b13_and_seven_classes",
    ]
    missing_names = [name for name in required_names if name not in text]
    result = {
        "root": str(MAIN.relative_to(ROOT)),
        "direct_imports": len(imports),
        "missing_imports": missing,
        "forbidden_main": forbidden,
        "missing_required_names": missing_names,
        "census_dependency_absent": "EnergyTerminalResidualCensus" not in text,
        "in_targets": "N11Formalization.EnergyTerminalBatchB13Main" in targets,
        "scope": "static source/import/API audit only; no Lean elaboration",
        "ok": (not missing and not forbidden and not missing_names
               and "EnergyTerminalResidualCensus" not in text),
    }
    REPORT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, sort_keys=True))
    raise SystemExit(0 if result["ok"] else 1)


if __name__ == "__main__":
    main()
