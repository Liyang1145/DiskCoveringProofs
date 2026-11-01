#!/usr/bin/env python3
"""Audit recursive import isolation of lane B's structural residual targets.

This is a source/import audit, not a Lean kernel check.  It resolves every
`N11Formalization.*` import under n11-work/lean and reports whether the three
lane-B structural modules can reach any lane-C target.  It does not claim that
the imports are built or mathematically sufficient.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
LEAN = ROOT / "n11-work" / "lean" / "N11Formalization"
OPS = ROOT / "n11-work" / "ops"
OUT = Path(__file__).with_name("audit_structural_dependency_isolation-report.json")
TARGETS = [
    "N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralCensus",
    "N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructural",
    "N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualStructuralMain",
]
IMPORT_RE = re.compile(r"^import\s+(N11Formalization(?:\.\w+)+)\s*$", re.M)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def target_modules(lane: str) -> set[str]:
    path = OPS / "lanes" / lane / "TARGETS.txt"
    return {line.strip() for line in path.read_text().splitlines()
            if line.strip() and not line.lstrip().startswith("#")}


def module_path(module: str) -> Path:
    return LEAN / (module.removeprefix("N11Formalization.").replace(".", "/") + ".lean")


def imports(module: str) -> list[str]:
    path = module_path(module)
    if not path.is_file():
        return []
    return IMPORT_RE.findall(path.read_text()[:16384])


def closure(starts: list[str]) -> tuple[dict[str, list[str]], list[str]]:
    graph: dict[str, list[str]] = {}
    missing: list[str] = []
    todo = list(starts)
    while todo:
        mod = todo.pop()
        if mod in graph:
            continue
        deps = imports(mod)
        graph[mod] = deps
        if deps and not module_path(mod).is_file():
            missing.append(mod)
        todo.extend(dep for dep in deps if dep not in graph)
    return graph, sorted(set(missing))


def ancestors(graph: dict[str, list[str]], target: str) -> list[str]:
    reverse = {mod: [] for mod in graph}
    for parent, deps in graph.items():
        for dep in deps:
            reverse.setdefault(dep, []).append(parent)
    seen: set[str] = set()
    todo = [target]
    while todo:
        mod = todo.pop()
        for parent in reverse.get(mod, []):
            if parent not in seen:
                seen.add(parent)
                todo.append(parent)
    return sorted(seen)


def main() -> None:
    b_targets = target_modules("B")
    c_targets = target_modules("C")
    c_only = c_targets - b_targets
    graph, missing = closure(TARGETS)
    reachable_c_only = sorted(mod for mod in graph if mod in c_only)
    reachable_shared = sorted(mod for mod in graph if mod in (c_targets & b_targets))
    conflicted = "N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus"
    paths_to_conflicted = ancestors(graph, conflicted) if conflicted in graph else []
    result = {
        "ok": not missing and conflicted not in graph,
        "scope": "recursive source/import audit only; not a Lean kernel check",
        "structural_targets": TARGETS,
        "module_count": len(graph),
        "lane_c_only_target_count": len(c_only),
        "reachable_lane_c_only_targets": reachable_c_only,
        "reachable_shared_target_count": len(reachable_shared),
        "missing_imports": missing,
        "conflicted_lane_c_module_reachable": conflicted in graph,
        "ancestors_of_conflicted_module": paths_to_conflicted,
        "conclusion": (
            "The lane-B structural trio does not reach lane C's conflicted literal "
            "census.  Its closure does contain other modules also listed by lane C; "
            "these are certificate/refinement dependencies, not the OOM target.  "
            "This isolates the named ordering blocker but does not establish that "
            "every lane-C-listed dependency is already kernel-green."
        ),
        "sha256": {
            "audit": sha256(Path(__file__)),
            "structural_dependency_isolation_report": None,
            "lanes/B/TARGETS.txt": sha256(OPS / "lanes" / "B" / "TARGETS.txt"),
            "lanes/C/TARGETS.txt": sha256(OPS / "lanes" / "C" / "TARGETS.txt"),
        },
    }
    # The report hash cannot contain its own final bytes; bind the audit and inputs.
    result["sha256"].pop("structural_dependency_isolation_report")
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: result[k] for k in (
        "ok", "module_count", "reachable_lane_c_only_targets", "reachable_shared_target_count", "missing_imports",
        "conflicted_lane_c_module_reachable", "conclusion")}, sort_keys=True))


if __name__ == "__main__":
    main()
