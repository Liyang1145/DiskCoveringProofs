#!/usr/bin/env python3
"""Independent inventory audit for the lane-B B13 closure.

This script does not emit or rewrite Lean.  It reconstructs the B11/B12/B13
paid sets from the checked-in packet definitions and verifies the literal
389-element census against the semantic residual.  It is an inventory check,
not a Lean kernel verdict.
"""
from pathlib import Path
import json
import re

LANE = Path(__file__).resolve().parent
ROOT = LANE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization"
EVIDENCE = ROOT / "n11-work/evidence-20261028/evidence"


def array_ids(module: str, name: str, element: str) -> set[int]:
    text = (LEAN / f"{module}.lean").read_text(encoding="utf-8")
    match = re.search(
        rf"^def {name}\s*:\s*{element}\s*:=\s*!\[([^\]]+)\]",
        text,
        re.MULTILINE,
    )
    if match is None:
        raise SystemExit(f"missing {name} array in {module}")
    return {int(x) for x in re.findall(r"\d+", match.group(1))}


def literal_set(module: str, name: str) -> set[int]:
    text = (LEAN / f"{module}.lean").read_text(encoding="utf-8")
    match = re.search(
        rf"^def {name}\s*:\s*Finset \(Fin 5011\)\s*:=\s*\{{([^}}]*)\}}",
        text,
        re.MULTILINE,
    )
    if match is None:
        raise SystemExit(f"missing {name} in {module}")
    return {int(x) for x in re.findall(r"\d+", match.group(1))}


def terminals() -> set[int]:
    text = (LEAN / "DBMSourceTreeData.lean").read_text(encoding="utf-8")
    pattern = re.compile(
        r"def node(\d+) : Node 5011 where(.*?)(?=\ndef node\d+ : Node 5011 where|\ndef data)",
        re.DOTALL,
    )
    return {int(m.group(1)) for m in pattern.finditer(text)
            if "terminal := true" in m.group(2)}


component_modules = {
    "lambda7": "Lambda0Batch7Packet",
    "tangent": "Lambda0TangentChordC01Packet",
    "cutting": "CuttingPlaneBatch7Packet",
    "batch22": "Paid16Batch22Packet",
    **{f"G{i:02}": f"Paid16GeneralG{i:02}" for i in range(1, 13)},
}
components = {
    name: array_ids(module, "nodeID", "Case → Fin 5011")
    for name, module in component_modules.items()
}
b11 = (
    {284, 562, 4348, 984, 1112, 2166, 2162, 3436, 4179, 4265, 4267}
    | set().union(*(components.values()))
)

next505: set[int] = set()
for i in range(25):
    next505 |= literal_set("Paid16GeneralNext505", f"ids{i:02d}")

rest = set(json.loads(
    (EVIDENCE / "rest1182-emission-manifest.json").read_text(encoding="utf-8-sig")
)["ids"])
term = terminals()
sharp = array_ids("Patch120DomainPacket", "patchID", "Fin 120 → Fin 5011")
b12 = b11 | next505
b13 = b12 | rest
residual = term - sharp - b13

literal_census: set[int] = set()
for i in range(4):
    literal_census |= literal_set("EnergyTerminalResidualCensusBase", f"chunk{i}")

checks = {
    "b11_count_310": len(b11) == 310,
    "b12_count_815": len(b12) == 815,
    "next1182_count": len(rest) == 1182,
    "b13_count_1997": len(b13) == 1997,
    "b12_next1182_disjoint": b12.isdisjoint(rest),
    "terminal_count_2506": len(term) == 2506,
    "sharp_count_120": len(sharp) == 120,
    "paid_terminal_subset": b13 <= term,
    "sharp_terminal_subset": sharp <= term,
    "paid_sharp_disjoint": b13.isdisjoint(sharp),
    "residual_count_389": len(residual) == 389,
    "literal_census_equals_residual": literal_census == residual,
    "literal_census_is_sorted_chunks": all(
        literal_set("EnergyTerminalResidualCensusBase", f"chunk{i}") ==
        set(sorted(residual)[i * 100:(i + 1) * 100 if i < 3 else len(residual)])
        for i in range(4)
    ),
}
failed = [name for name, ok in checks.items() if not ok]
report = {
    "counts": {
        "b11": len(b11), "b12": len(b12), "next1182": len(rest), "b13": len(b13),
        "terminals": len(term), "sharp": len(sharp), "residual": len(residual),
    },
    "checks": checks,
    "digest": {
        "b13_ids_sha256": __import__("hashlib").sha256(
            ",".join(map(str, sorted(b13))).encode()
        ).hexdigest().upper(),
        "residual_ids_sha256": __import__("hashlib").sha256(
            ",".join(map(str, sorted(residual))).encode()
        ).hexdigest().upper(),
    },
    "scope": "inventory equality only; Lean elaboration is CI-pending",
}
(LANE / "audit_b13_closure-report.json").write_text(
    json.dumps(report, indent=2) + "\n", encoding="utf-8"
)
if failed:
    raise SystemExit("FAILED: " + ", ".join(failed))
print(json.dumps(report["counts"], sort_keys=True))
print("all 13 inventory checks passed")
