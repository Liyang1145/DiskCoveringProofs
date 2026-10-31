#!/usr/bin/env python3
"""Check explicit q0-degree3 module references against import closures.

Lean does not require a direct import when a dependency is already imported
transitively, but an explicit ``Module.name`` reference can otherwise fail
after an import graph refactor.  This gate reports any such reference whose
module is not reachable from the referring module.
"""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[4]
LEAN_DIR = ROOT / "n11-work" / "lean" / "N11Formalization"
MODULE_PREFIX = "N11Formalization."
Q0_PREFIX = "SevenClassQ0Deg3"


def strip_comments(source: str) -> str:
    source = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    return re.sub(r"--[^\n]*", "", source)


def module_imports(path: Path) -> tuple[str, set[str]]:
    source = strip_comments(path.read_text())
    module = MODULE_PREFIX + path.stem
    imports = {
        match.group(1)
        for match in re.finditer(r"^import\s+(\S+)", source, flags=re.MULTILINE)
    }
    return module, imports


def main() -> int:
    paths = sorted(LEAN_DIR.glob(f"{Q0_PREFIX}*.lean"))
    graph = {module: imports for module, imports in map(module_imports, paths)}

    def closure(module: str) -> set[str]:
        seen: set[str] = set()
        todo = list(graph.get(module, ()))
        while todo:
            imported = todo.pop()
            if imported in seen:
                continue
            seen.add(imported)
            todo.extend(graph.get(imported, ()))
        return seen

    failures: list[str] = []
    checked = 0
    for path in paths:
        module = MODULE_PREFIX + path.stem
        source = strip_comments(path.read_text())
        names = set(
            re.findall(rf"N11Formalization\.({Q0_PREFIX}[A-Za-z0-9_]*)", source)
        )
        names.update(
            re.findall(rf"(?<![A-Za-z0-9_.])({Q0_PREFIX}[A-Za-z0-9_]*)\.", source)
        )
        reachable = closure(module)
        for name in sorted(names):
            dependency = MODULE_PREFIX + name
            if dependency == module or dependency not in graph:
                continue
            checked += 1
            if dependency not in reachable:
                failures.append(f"{path.name}: {name} is not in the import closure")

    for failure in failures:
        print(f"FAIL {failure}")
    if failures:
        return 1
    print(f"PASS checked {checked} explicit q0-degree3 references across {len(paths)} modules")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
