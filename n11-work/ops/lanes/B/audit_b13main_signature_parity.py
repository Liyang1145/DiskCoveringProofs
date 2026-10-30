#!/usr/bin/env python3
"""Check that B13Main only weakens the B12Main energy premise.

This is a static text/import audit.  It does not elaborate Lean and is not a
root-CI or proof-credit verdict.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
LEAN = ROOT / "n11-work" / "lean" / "N11Formalization"
B12 = LEAN / "EnergyTerminalBatchB12Main.lean"
B13 = LEAN / "EnergyTerminalBatchB13Main.lean"
REPORT = Path(__file__).with_name("audit_b13main_signature_parity-report.json")


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def theorem_blocks(text: str) -> dict[str, str]:
    blocks: dict[str, str] = {}
    current: list[str] = []
    name: str | None = None
    for line in text.splitlines():
        if line.startswith("theorem "):
            if name is not None:
                blocks[name] = "\n".join(current)
            name = line.split()[1]
            current = [line]
        elif name is not None:
            if line.startswith("end"):
                blocks[name] = "\n".join(current)
                name = None
                current = []
            else:
                current.append(line)
    if name is not None:
        blocks[name] = "\n".join(current)
    return blocks


def normalize_batch(text: str, old: str, new: str) -> str:
    return text.replace(old, new)


def main() -> None:
    b12 = B12.read_text(encoding="utf-8")
    b13 = B13.read_text(encoding="utf-8")
    b12_blocks = theorem_blocks(b12)
    b13_blocks = theorem_blocks(b13)
    pairs = {
        "main": (
            "main_of_energy_b12_and_seven_classes",
            "main_of_energy_b13_and_seven_classes",
        ),
        "full_disk": (
            "full_disk_bound_of_energy_b12_and_seven_classes",
            "full_disk_bound_of_energy_b13_and_seven_classes",
        ),
    }
    normalized = {
        key: normalize_batch(b12_blocks[old], "EnergyTerminalBatchB12Main",
                             "EnergyTerminalBatchB13Main").replace(
                                 "EnergyTerminalBatchB12.RemainingTerminalRadius",
                                 "EnergyTerminalBatchB13.RemainingTerminalRadius").replace(
                                 "EnergyTerminalBatchB12.remaining_of_b12 henergy",
                                 "EnergyTerminalBatchB12.remaining_of_b12\n      (EnergyTerminalBatchB13.remaining_of_b13 henergy)")
        for key, (old, _) in pairs.items()
    }
    # The theorem names are intentionally batch-specific, including calls in
    # the full-disk wrapper proof.
    for key in pairs:
        for old, new in pairs.values():
            normalized[key] = normalized[key].replace(old, new)

    result = {
        "b12main": str(B12),
        "b12main_sha256": sha(B12),
        "b13main": str(B13),
        "b13main_sha256": sha(B13),
        "checks": {
            "two_root_facing_theorems_each": len(b12_blocks) == 2 and len(b13_blocks) == 2,
            "same_full_disk_quantifier": (
                "∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → "
                "SourceExactRoot.sourceRadius ≤ r" in b12_blocks[pairs["full_disk"][0]]
                and "∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → "
                "SourceExactRoot.sourceRadius ≤ r" in b13_blocks[pairs["full_disk"][1]]
            ),
            "same_main_result": (
                "N11MainStatement SourceExactRoot.sourceRadius"
                in b12_blocks[pairs["main"][0]]
                and "N11MainStatement SourceExactRoot.sourceRadius"
                in b13_blocks[pairs["main"][1]]
            ),
            "b13_uses_explicit_residual_transfer": (
                "EnergyTerminalBatchB12.remaining_of_b12\n      "
                "(EnergyTerminalBatchB13.remaining_of_b13 henergy)"
                in b13_blocks[pairs["main"][1]]
            ),
            "only_energy_premise_changed": all(
                normalized[key] == b13_blocks[pairs[key][1]] for key in pairs
            ),
        },
        "scope": "static source signature parity only; no Lean elaboration or root CI verdict",
    }
    REPORT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n",
                      encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))
    raise SystemExit(0 if all(result["checks"].values()) else 1)


if __name__ == "__main__":
    main()
