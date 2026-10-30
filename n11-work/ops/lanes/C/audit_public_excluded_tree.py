#!/usr/bin/env python3
"""Static dependency audit for FrozenCapPublicExcludedTree.

This is not a Lean build.  It verifies that the replacement exclusion module
uses all seven small per-node cap certificates and does not import either the
red bulk row-cap module or the currently red B13 aggregate.
"""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
MODULES = ROOT / "n11-work/lean/N11Formalization"
TARGET = "N11Formalization.FrozenCapPublicExcludedTree"
PUBLIC = (1409, 2337, 2341, 2356, 2360, 2368, 2370)
REQUIRED = {
    "N11Formalization.DBMSourceTreeData",
    "N11Formalization.FrozenCapRowCapTreeBridges",
    "N11Formalization.FrozenCapWideFieldWitnesses",
    "N11Formalization.PaidCellCertificateMCap",
    *{f"N11Formalization.FrozenCapRowCap{node}" for node in PUBLIC},
}
FORBIDDEN_MODULES = {
    "N11Formalization.FrozenCapWideFieldRowCaps",
    "N11Formalization.EnergyTerminalBatchB13",
}
FORBIDDEN_TOKENS = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|implemented_by)\b|"
    r"\bLean\.ofReduceBool\b|\bmaxHeartbeats\s+0\b"
)


def source(module):
    rel = module.removeprefix("N11Formalization").lstrip(".")
    path = (MODULES / Path(*rel.split("."))).with_suffix(".lean")
    return path, path.read_text(encoding="utf-8") if path.is_file() else None


def closure(start):
    seen, missing, pending = set(), [], [start]
    while pending:
        module = pending.pop()
        if module in seen or not module.startswith("N11Formalization"):
            continue
        path, text = source(module)
        if text is None:
            missing.append((module, str(path)))
            continue
        seen.add(module)
        pending.extend(re.findall(r"^import\s+(\S+)", text, re.MULTILINE))
    return seen, missing


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


target_path, target_text = source(TARGET)
modules, missing = closure(TARGET)
theorem_ids = tuple(sorted(int(x) for x in re.findall(
    r"^theorem excluded_(\d+)_tree\b", target_text or "", re.MULTILINE)))
checks = {
    "target_exists": target_text is not None,
    "closure_complete": not missing,
    "required_modules_in_closure": REQUIRED <= modules,
    "forbidden_modules_absent": not (FORBIDDEN_MODULES & modules),
    "seven_theorems_exact": theorem_ids == PUBLIC,
    "no_forbidden_tokens": FORBIDDEN_TOKENS.search(target_text or "") is None,
}
report = {
    "target": TARGET,
    "target_sha256": sha256(target_path),
    "closure_size": len(modules),
    "missing_imports": missing,
    "forbidden_modules_present": sorted(FORBIDDEN_MODULES & modules),
    "theorem_ids": theorem_ids,
    "checks": checks,
    "all_checks_pass": all(checks.values()),
    "scope": "static import/source audit only; not a kernel proof",
}
(HERE / "public-excluded-tree-audit.json").write_text(
    json.dumps(report, indent=2) + "\n", encoding="utf-8"
)
print(json.dumps(report, indent=2))
raise SystemExit(0 if report["all_checks_pass"] else 1)
