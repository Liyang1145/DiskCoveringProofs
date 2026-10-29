#!/usr/bin/env python3
"""Emit a literal, kernel-countable census of the B13 residual terminals.

The source of truth is the checked-in Lean table and the checked-in packet
definitions/manifests.  No manifest count is trusted: the script reconstructs
B11, B12 and B13 from their component ID arrays and asserts every set relation
before emitting Lean modules.  The census is split into four source-index
blocks and a small assembly module so no single elaboration walks all 5011
source indices.
"""
from pathlib import Path
import hashlib
import json
import re

LANE = Path(__file__).resolve().parent
ROOT = LANE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization"
EVIDENCE = ROOT / "n11-work/evidence-20261028/evidence"
OUT = LEAN / "EnergyTerminalResidualCensus.lean"
BASE = LEAN / "EnergyTerminalResidualCensusBase.lean"
PARTS = [LEAN / f"EnergyTerminalResidualCensusC{i:02d}.lean" for i in range(1, 5)]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def node_ids(module: str) -> set[int]:
    text = (LEAN / f"{module}.lean").read_text(encoding="utf-8")
    match = re.search(
        r"^def nodeID\s*:\s*Case\s*→\s*Fin\s*5011\s*:=\s*!\[([^\]]+)\]",
        text,
        re.MULTILINE,
    )
    if match is None:
        raise SystemExit(f"missing nodeID array in {module}")
    return {int(x) for x in re.findall(r"\d+", match.group(1))}


def literal_ids(module: str, name: str) -> set[int]:
    text = (LEAN / f"{module}.lean").read_text(encoding="utf-8")
    match = re.search(
        rf"^def {name}\s*:\s*Finset \(Fin 5011\)\s*:=\s*\{{([^}}]*)\}}",
        text,
        re.MULTILINE,
    )
    if match is None:
        raise SystemExit(f"missing {name} in {module}")
    return {int(x) for x in re.findall(r"\d+", match.group(1))}


def terminal_ids() -> set[int]:
    text = (LEAN / "DBMSourceTreeData.lean").read_text(encoding="utf-8")
    pattern = re.compile(
        r"def node(\d+) : Node 5011 where(.*?)(?=\ndef node\d+ : Node 5011 where|\ndef data)",
        re.DOTALL,
    )
    ids = {int(m.group(1)) for m in pattern.finditer(text) if "terminal := true" in m.group(2)}
    if len(ids) != 2506:
        raise SystemExit(f"terminal census mismatch: {len(ids)} != 2506")
    return ids


def patch_ids() -> set[int]:
    text = (LEAN / "Patch120DomainPacket.lean").read_text(encoding="utf-8")
    match = re.search(
        r"^def patchID\s*:\s*Fin 120\s*→\s*Fin 5011\s*:=\s*!\[([^\]]+)\]",
        text,
        re.MULTILINE,
    )
    if match is None:
        raise SystemExit("missing patchID array")
    return {int(x) for x in re.findall(r"\d+", match.group(1))}


components = {
    name: node_ids(module)
    for name, module in {
        "lambda7": "Lambda0Batch7Packet",
        "tangent": "Lambda0TangentChordC01Packet",
        "cutting": "CuttingPlaneBatch7Packet",
        "batch22": "Paid16Batch22Packet",
        **{f"G{i:02}": f"Paid16GeneralG{i:02}" for i in range(1, 13)},
    }.items()
}

b11 = (
    {284, 562, 4348, 984, 1112, 2166, 2162, 3436, 4179, 4265, 4267}
    | components["lambda7"]
    | components["tangent"]
    | components["cutting"]
    | components["batch22"]
    | set().union(*(components[f"G{i:02}"] for i in range(1, 13)))
)

next505_text = (LEAN / "Paid16GeneralNext505.lean").read_text(encoding="utf-8")
next505: set[int] = set()
for match in re.finditer(
    r"^def ids(\d\d) : Finset \(Fin 5011\) := \{([^}]*)\}",
    next505_text,
    re.MULTILINE,
):
    next505 |= {int(x) for x in re.findall(r"\d+", match.group(2))}

rest = set(
    json.loads((EVIDENCE / "rest1182-emission-manifest.json").read_text(encoding="utf-8-sig"))["ids"]
)
terminals = terminal_ids()
sharp = patch_ids()
b12 = b11 | next505
b13 = b12 | rest
residual = terminals - sharp - b13

assert (len(b11), len(b12), len(b13)) == (310, 815, 1997)
assert (len(sharp), len(residual)) == (120, 389)
assert b11.isdisjoint(next505) and b12.isdisjoint(rest)
assert b13 <= terminals and sharp <= terminals and b13.isdisjoint(sharp)
assert residual == terminals - sharp - b13

residual_sorted = sorted(residual)
chunks = [residual_sorted[i:i + 100] for i in range(0, len(residual_sorted), 100)]
assert [len(c) for c in chunks] == [100, 100, 100, 89]


def finset(ids: list[int]) -> str:
    return "{" + ",".join(map(str, ids)) + "}"


block_size = 100
block_count = (5011 + block_size - 1) // block_size
base_lines = [f"""import N11Formalization.EnergyTerminalBatchB13

/-! Shared literal chunks for the {len(residual)}-element B13 residual census.
The source-index equality proofs are split across four census parts. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensus
open Finset
noncomputable section
"""]
for i, chunk in enumerate(chunks):
    base_lines.append(f"def chunk{i} : Finset (Fin 5011) := {finset(chunk)}")
    base_lines.append(f"theorem chunk{i}_card : chunk{i}.card = {len(chunk)} := by decide +kernel")
base_lines.append("def residualIDs : Finset (Fin 5011) := chunk0 ∪ (chunk1 ∪ (chunk2 ∪ chunk3))")
base_lines.append("end")
base_lines.append("end N11Formalization.EnergyTerminalResidualCensus")
for i in range(4):
    base_lines.append(f"#print axioms N11Formalization.EnergyTerminalResidualCensus.chunk{i}_card")
BASE.write_text("\n".join(base_lines) + "\n", encoding="utf-8")

part_outputs: list[Path] = []
for part_index, out in enumerate(PARTS):
    lines = [f"""import N11Formalization.EnergyTerminalResidualCensusBase

/-! Census part {part_index + 1}/4: source-index equivalence blocks congruent to
{part_index} modulo 4.  Every kernel decision below covers at most 100 source
indices. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensus
open Finset
noncomputable section
"""]
    for i in range(part_index, block_count, len(PARTS)):
        lo = i * block_size
        hi = min((i + 1) * block_size, 5011)
        lines.append(f"theorem mem_iff_block{i:02d} (n : Fin 5011)")
        if i == 0:
            lines.append(f"    (hlo : 0 ≤ n.val) (hhi : n.val < {hi}) :")
        else:
            lines.append(f"    (hlo : {lo} ≤ n.val) (hhi : n.val < {hi}) :")
        lines.append("    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by")
        lines.append("  rcases n with ⟨k, hk⟩")
        lines.append("  interval_cases k <;>")
        lines.append("    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel")
        lines.append("")
    lines.append("end")
    lines.append("end N11Formalization.EnergyTerminalResidualCensus")
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")
    part_outputs.append(out)

lines = [f"""import N11Formalization.EnergyTerminalResidualCensusC01
import N11Formalization.EnergyTerminalResidualCensusC02
import N11Formalization.EnergyTerminalResidualCensusC03
import N11Formalization.EnergyTerminalResidualCensusC04

/-! Assembly of the {len(residual)}-element B13 residual census from four
source-index parts.  No single kernel decision covers more than 101 literals. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensus
open Finset
noncomputable section
"""]
for i in range(4):
    for j in range(i + 1, 4):
        lines.append(
            f"private theorem chunk{i}_disjoint_chunk{j} : "
            f"Disjoint chunk{i} chunk{j} := by decide +kernel"
        )
lines.append("private theorem chunk0_disjoint : "
             "Disjoint chunk0 (chunk1 ∪ (chunk2 ∪ chunk3)) := by")
lines.append("  rw [Finset.disjoint_union_right]")
lines.append("  exact ⟨chunk0_disjoint_chunk1, by")
lines.append("    rw [Finset.disjoint_union_right]")
lines.append("    exact ⟨chunk0_disjoint_chunk2, chunk0_disjoint_chunk3⟩⟩")
lines.append("private theorem chunk1_disjoint : Disjoint chunk1 (chunk2 ∪ chunk3) := by")
lines.append("  rw [Finset.disjoint_union_right]")
lines.append("  exact ⟨chunk1_disjoint_chunk2, chunk1_disjoint_chunk3⟩")
lines.append("private theorem chunk2_disjoint : Disjoint chunk2 chunk3 := chunk2_disjoint_chunk3")

lines.append("theorem residualIDs_card : residualIDs.card = 389 := by")
lines.append("  rw [residualIDs, Finset.card_union_of_disjoint chunk0_disjoint, chunk0_card]")
lines.append("  rw [Finset.card_union_of_disjoint chunk1_disjoint, chunk1_card]")
lines.append("  rw [Finset.card_union_of_disjoint chunk2_disjoint, chunk2_card]")
lines.append("  rw [chunk3_card]")
lines.append("  norm_num")
lines.append("theorem residualIDs_eq :")
lines.append("    residualIDs = EnergyTerminalBatchB13.residualIDs := by")
lines.append("  ext n")
cover = ["n.val < 100"]
for i in range(1, block_count - 1):
    cover.append(f"({i * block_size} ≤ n.val ∧ n.val < {(i + 1) * block_size})")
cover.append(f"{(block_count - 1) * block_size} ≤ n.val")
lines.append("  have hcover : " + " ∨ ".join(cover) + " := by omega")
lines.append("  rcases hcover with " + " | ".join(f"h{i}" for i in range(block_count)))
for i in range(block_count):
    if i == 0:
        proof = "mem_iff_block00 n (Nat.zero_le _) h0"
    elif i == block_count - 1:
        proof = f"mem_iff_block{i:02d} n h{i} n.isLt"
    else:
        proof = f"mem_iff_block{i:02d} n h{i}.1 h{i}.2"
    lines.append(f"  · exact {proof}")
lines.append("")
lines.append("theorem b13_residualIDs_card :")
lines.append("    EnergyTerminalBatchB13.residualIDs.card = 389 := by")
lines.append("  rw [← residualIDs_eq, residualIDs_card]")
lines.append("")
lines.append("theorem residualIDs_sound :")
lines.append("    ∀ n ∈ residualIDs, (DBMSourceTree.data n).terminal = true ∧")
lines.append("      n ∉ Patch120SharpDispatch.sharpIDs ∧")
lines.append("      n ∉ EnergyTerminalBatchB13.paidIDs := by")
lines.append("  intro n hn")
lines.append("  rw [residualIDs_eq] at hn")
lines.append("  exact (EnergyTerminalBatchB13.mem_residualIDs_iff n).mp hn")
lines.append("")
lines.append("def RemainingTerminalRadius : Prop :=")
lines.append("  ∀ n : Fin 5011, n ∈ residualIDs →")
lines.append("    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →")
lines.append("      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)")
lines.append("        (FlashLeafSplit.tlift y) →")
lines.append("      ∀ (C Z : Fin 11 → Point) (r : ℝ),")
lines.append("        ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r →")
lines.append("          SourceExactRoot.sourceRadius ≤ r")
lines.append("")
lines.append("theorem remaining_iff_b13 :")
lines.append("    RemainingTerminalRadius ↔ EnergyTerminalBatchB13.RemainingTerminalRadius := by")
lines.append("  rw [EnergyTerminalBatchB13.remaining_iff]")
lines.append("  constructor")
lines.append("  · intro h n hn")
lines.append("    rw [← residualIDs_eq] at hn")
lines.append("    exact h n hn")
lines.append("  · intro h n hn")
lines.append("    rw [residualIDs_eq] at hn")
lines.append("    exact h n hn")
lines.append("end")
lines.append("end N11Formalization.EnergyTerminalResidualCensus")
lines.append("#check @N11Formalization.EnergyTerminalResidualCensus.residualIDs_card")
lines.append("#check @N11Formalization.EnergyTerminalResidualCensus.residualIDs_eq")
lines.append("#check @N11Formalization.EnergyTerminalResidualCensus.b13_residualIDs_card")
lines.append("#check @N11Formalization.EnergyTerminalResidualCensus.remaining_iff_b13")
lines.append("#print axioms N11Formalization.EnergyTerminalResidualCensus.residualIDs_card")
lines.append("#print axioms N11Formalization.EnergyTerminalResidualCensus.residualIDs_eq")
lines.append("#print axioms N11Formalization.EnergyTerminalResidualCensus.b13_residualIDs_card")

text = "\n".join(lines) + "\n"
OUT.write_text(text, encoding="utf-8")
report = {
    "module": "EnergyTerminalResidualCensus",
    "inputs": {
        name: sha256(EVIDENCE / name)
        for name in ("rest1182-emission-manifest.json",)
    },
    "terminal_count": len(terminals),
    "sharp_count": len(sharp),
    "paid_b13_count": len(b13),
    "residual_count": len(residual),
    "chunk_sizes": [len(c) for c in chunks],
    "modules": {
        out.stem: {"bytes": out.stat().st_size, "sha256": sha256(out)}
        for out in [BASE, *part_outputs]
    },
    "output_bytes": OUT.stat().st_size,
    "output_sha256": sha256(OUT),
    "scope": "source reconstruction and emitted bytes; Lean elaboration is CI-pending",
}
(LANE / "emit_residual_census-report.json").write_text(
    json.dumps(report, indent=2) + "\n", encoding="utf-8"
)
print(json.dumps(report, indent=2))
