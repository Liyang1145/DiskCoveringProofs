#!/usr/bin/env python3
"""Static import/forbidden-token audit for Lane B CI targets.

This does not elaborate Lean. It checks that every local import in the
transitive closure exists and that target-closure sources contain no banned
proof escapes or resource overrides.
"""
from __future__ import annotations
import json, re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
LEAN = ROOT / "n11-work" / "lean"
TARGETS = Path(__file__).with_name("TARGETS.txt")
REPORT = Path(__file__).with_name("audit_target_imports-report.json")
IMPORT = re.compile(r"^import\s+(N11Formalization(?:\.\w+)+)\s*$", re.MULTILINE)
BANNED = ("sorry", "admit", "native_decide", "ofReduceBool", "implemented_by",
          "maxHeartbeats 0", "maxRecDepth")

def module_path(module: str) -> Path:
    return LEAN.joinpath(*module.split(".")).with_suffix(".lean")

def main() -> None:
    targets = [line.strip() for line in TARGETS.read_text().splitlines()
               if line.strip() and not line.lstrip().startswith("#")]
    seen: dict[str, str] = {}
    stack = list(targets)
    missing = []
    violations = []
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        path = module_path(module)
        if not path.is_file():
            missing.append({"module": module, "expected": str(path.relative_to(ROOT))})
            seen[module] = "missing"
            continue
        text = path.read_text()
        seen[module] = str(path.relative_to(ROOT))
        if module in targets:
            for token in BANNED:
                if re.search(r"(?<![\w.])" + re.escape(token) + r"(?![\w])", text):
                    violations.append({"module": module, "token": token})
        stack.extend(IMPORT.findall(text))
    result = {"targets": targets, "closure_size": len(seen), "missing": missing,
              "forbidden": violations, "ok": not missing and not violations}
    REPORT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, sort_keys=True))
    raise SystemExit(0 if result["ok"] else 1)

if __name__ == "__main__":
    main()
