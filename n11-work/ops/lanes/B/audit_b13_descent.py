#!/usr/bin/env python3
"""Static block audit for the B13 descent-bound module.

This verifies the source hierarchy and forbidden-token absence.  It is not a
Lean elaboration check and provides no proof credit.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

LANE = Path(__file__).resolve().parent
ROOT = LANE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization"
MODULE = LEAN / "EnergyTerminalBatchB13DescentBounds.lean"
B13 = LEAN / "EnergyTerminalBatchB13.lean"
REPORT = LANE / "audit_b13_descent-report.json"
BANNED = ("sorry", "admit", "native_decide", "ofReduceBool", "implemented_by",
          "maxHeartbeats 0")


def import_closure(module: str) -> set[str]:
    """Return the transitive local imports of a module, including itself."""
    seen: set[str] = set()
    pending = [module]
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        source = LEAN / f"{name.replace('.', '/')}.lean"
        if source.is_file():
            pending.extend(re.findall(
                r"^import N11Formalization\.(\S+)$",
                source.read_text(encoding="utf-8"), re.MULTILINE,
            ))
    return seen


def main() -> None:
    text = MODULE.read_text(encoding="utf-8")
    b13 = B13.read_text(encoding="utf-8")
    before_emit = MODULE.read_bytes()
    subprocess.run(
        [sys.executable, str(LANE / "emit_b13_descent_bounds.py")],
        cwd=ROOT, check=True, capture_output=True,
    )
    emitter_matches = before_emit == MODULE.read_bytes()
    groups = re.findall(r"private theorem g(\d{2})_lt ", text)
    high_match = re.search(
        r"def b09HighIDs : Finset \(Fin 5011\) := \{([0-9,]+)\}", text)
    source_high_ids = set(map(int, high_match.group(1).split(","))) if high_match else set()
    literal_ids: set[int] = set()
    literal_blocks = 0
    for path in sorted(LEAN.glob("Paid16GeneralNext1182S*.lean")):
        for body in re.findall(
                r"^def ids\d+ : Finset \(Fin 5011\) := \{([0-9,]+)\}",
                path.read_text(encoding="utf-8"), re.MULTILINE):
            literal_ids.update(map(int, body.split(",")))
            literal_blocks += 1
    packet_ids: set[int] = set()
    for name in ("Lambda0Batch7Packet", "Lambda0TangentChordC01Packet",
                 "CuttingPlaneBatch7Packet", "Paid16Batch22Packet"):
        packet_text = (LEAN / f"{name}.lean").read_text(encoding="utf-8")
        body = re.search(
            r"^def nodeID : Case → Fin 5011 := !\[([0-9,]+)\]",
            packet_text, re.MULTILINE,
        )
        if body:
            packet_ids.update(map(int, body.group(1).split(",")))
    b09_ids = packet_ids | {284, 562, 4348, 984, 1112, 2166, 2162,
                             3436, 4265, 4179, 4267}
    b09_high_ids = {i for i in b09_ids if i >= 2565}
    direct_imports = re.findall(
        r"^import N11Formalization\.(\S+)$", text, re.MULTILINE)
    missing_import_files = [
        name for name in direct_imports
        if not (LEAN / f"{name.replace('.', '/')}.lean").is_file()
    ]
    # Resolve every local qualified identifier against the declaration in the
    # module named by its longest matching namespace prefix.  This catches the
    # class of failure that stopped the first CI run (a valid symbol whose
    # defining module was not imported) before spending CI time on elaboration.
    qualified = set(re.findall(
        r"\b(?:[A-Z][A-Za-z0-9_]*\.)+[A-Za-z0-9_]+", text))
    unresolved_cross_references: list[str] = []
    referenced_modules: set[str] = set()
    for name in sorted(qualified):
        parts = name.split(".")
        for cut in range(len(parts) - 1, 0, -1):
            module = ".".join(parts[:cut])
            source = LEAN / f"{module.replace('.', '/')}.lean"
            if not source.is_file():
                continue
            symbol = parts[cut]
            declaration = re.compile(
                rf"^\s*(?:private\s+)?(?:noncomputable\s+)?"
                rf"(?:def|theorem|abbrev|lemma)\s+{re.escape(symbol)}\b",
                re.MULTILINE,
            )
            if not declaration.search(source.read_text(encoding="utf-8")):
                unresolved_cross_references.append(name)
            referenced_modules.add(module)
            break
    local_module = MODULE.stem
    closure = import_closure(local_module)
    unimported_reference_modules = sorted(referenced_modules - closure)
    checks = {
        "twelve_group_blocks": groups == [f"{i:02d}" for i in range(1, 13)],
        "twelve_group_norm_num_decodes":
            len(re.findall(
                r"fin_cases i <;> norm_num \[Paid16GeneralG\d{2}\.nodeID\]",
                text)) == 12,
        "no_kernel_decisions": "decide +kernel" not in text,
        "structural_image_decodes": text.count("rcases Finset.mem_image.mp hn") == 16,
        "b09_layered_classification": text.count("private theorem b") == 9,
        "b09_high_classification":
            "theorem b09_bound (n : Fin 5011)" in text and
            "def b09HighIDs : Finset (Fin 5011) :=" in text,
        "high_ids_excluded": "theorem high_not_next" in text,
        "high_ids_27": len(source_high_ids) == 27,
        "reconstructed_b09_58": len(b09_ids) == 58,
        "high_ids_match_reconstructed_b09": source_high_ids == b09_high_ids,
        "next1182_literals_57x1182":
            literal_blocks == 57 and len(literal_ids) == 1182,
        "high_ids_absent_from_next1182": not (source_high_ids & literal_ids),
        "emitter_reproduces_module": emitter_matches,
        "first42_two_image_layers": "exact g01_lt n hn" in text and "exact g02_lt n hn" in text,
        "remaining210_no_direct_decode":
            "∀ m ∈ Paid16GeneralRemaining210.newIDs, m.val < 2565" not in text,
        "b13_imports_module": "import N11Formalization.EnergyTerminalBatchB13DescentBounds" in b13,
        "descent_imports_b11": "import N11Formalization.EnergyTerminalBatchB11" in text,
        "descent_imports_next1182": "import N11Formalization.Paid16GeneralNext1182" in text,
        "direct_imports_resolve": not missing_import_files,
        "cross_references_resolve": not unresolved_cross_references,
        "cross_reference_modules_imported": not unimported_reference_modules,
        "b13_uses_b11_bound": "EnergyTerminalBatchB13DescentBounds.b11_bound n hn" in b13,
        "b13_uses_high_exclusion": "EnergyTerminalBatchB13DescentBounds.high_not_next a" in b13,
        "no_forbidden_tokens": not any(
            re.search(r"(?<![\w.])" + re.escape(t) + r"(?![\w])", text + b13)
            for t in BANNED
        ),
    }
    result = {
        "module": str(MODULE.relative_to(ROOT)),
        "group_blocks": len(groups),
        "kernel_decisions": text.count("decide +kernel"),
        "structural_image_decodes": text.count("rcases Finset.mem_image.mp hn"),
        "b09_descent_layers": text.count("private theorem b"),
        "high_ids": len(source_high_ids),
        "reconstructed_b09_ids": len(b09_ids),
        "reconstructed_b09_high_ids": len(b09_high_ids),
        "direct_imports": len(direct_imports),
        "missing_import_files": missing_import_files,
        "referenced_local_modules": len(referenced_modules),
        "transitive_import_closure_modules": len(closure),
        "unresolved_cross_references": unresolved_cross_references,
        "unimported_reference_modules": unimported_reference_modules,
        "next1182_literal_blocks": literal_blocks,
        "next1182_literal_ids": len(literal_ids),
        "checks": checks,
        "scope": "static source hierarchy only; Lean elaboration is CI-pending",
        "ok": all(checks.values()),
    }
    REPORT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, sort_keys=True))
    raise SystemExit(0 if result["ok"] else 1)


if __name__ == "__main__":
    main()
