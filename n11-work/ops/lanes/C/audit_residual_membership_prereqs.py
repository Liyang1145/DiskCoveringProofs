#!/usr/bin/env python3
"""Static prerequisite audit for FrozenCapResidualMembership.

This does not build Lean.  It verifies that the consumer's local import
closure resolves, that the repaired B13 dependency and its key declarations
are present, and that the seven public residual ids are exactly the ids named
by the consumer.
"""
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
MODULES = ROOT / "n11-work/lean/N11Formalization"
TARGET = "N11Formalization.FrozenCapResidualMembership"
PUBLIC = (1409, 2337, 2341, 2356, 2360, 2368, 2370)
REQUIRED = {
    "N11Formalization.EnergyTerminalBatchB13",
    "N11Formalization.EnergyTerminalBatchB13DescentBounds",
    "N11Formalization.EnergyTerminalBatchB11",
    "N11Formalization.Paid16GeneralNext1182",
}
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|implemented_by)\b|"
    r"\bLean\.ofReduceBool\b|\bmaxHeartbeats\s+0\b"
)


def source(module):
    rel = module.removeprefix("N11Formalization").lstrip(".")
    path = (MODULES / Path(*rel.split("."))).with_suffix(".lean") if rel else ROOT / "n11-work/lean/N11Formalization.lean"
    return path, path.read_text(encoding="utf-8") if path.is_file() else None


def closure(start):
    seen, missing, pending = set(), [], [start]
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        if not module.startswith("N11Formalization"):
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
consumer_ids = tuple(sorted(int(x) for x in re.findall(r"^theorem mem_(\d+)\b", target_text, re.M)))
checks = {
    "target_exists": target_text is not None,
    "closure_complete": not missing,
    "required_modules_in_closure": REQUIRED <= modules,
    "consumer_ids_exact": consumer_ids == PUBLIC,
    "no_forbidden_tokens": FORBIDDEN.search(target_text) is None,
}
report = {
    "target": TARGET,
    "target_sha256": sha256(target_path),
    "closure_size": len(modules),
    "missing_imports": missing,
    "consumer_ids": consumer_ids,
    "checks": checks,
    "all_checks_pass": all(checks.values()),
}
(HERE / "residual-membership-prereq-audit.json").write_text(
    json.dumps(report, indent=2) + "\n", encoding="utf-8"
)
print(json.dumps(report, indent=2))
raise SystemExit(0 if report["all_checks_pass"] else 1)
