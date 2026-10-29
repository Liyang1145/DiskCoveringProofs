#!/usr/bin/env python3
"""Emit a literal, kernel-countable census of the B13 residual terminals.

The source of truth is the checked-in Lean table and the checked-in packet
definitions/manifests.  No manifest count is trusted: the script reconstructs
B11, B12 and B13 from their component ID arrays and asserts every set relation
before emitting a Lean module.
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


lines = [f"""import N11Formalization.EnergyTerminalBatchB13

/-! Literal census of the {len(residual)} B13 residual terminal ids.

`terminal_ids` below are reconstructed from `DBMSourceTreeData.nodeN`; the
packet ids are reconstructed from their checked-in packet arrays and manifests.
The literal chunks keep every `decide +kernel` below 101 elements.  The final
equality connects the literal list to the semantic filter in B13 via 51
source-index interval lemmas, each deciding at most 100 nodes. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace N11Formalization.EnergyTerminalResidualCensus
open Finset
noncomputable section
"""]

for i, chunk in enumerate(chunks):
    lines.append(f"def chunk{i} : Finset (Fin 5011) := {finset(chunk)}")
    lines.append(f"theorem chunk{i}_card : chunk{i}.card = {len(chunk)} := by decide +kernel")

chain = "chunk3"
for i in reversed(range(3)):
    chain = f"chunk{i} ∪ ({chain})"
lines.append(f"def residualIDs : Finset (Fin 5011) := {chain}")

for i in range(3):
    tail = "chunk3"
    for j in reversed(range(i + 1, 3)):
        tail = f"chunk{j} ∪ ({tail})"
    lines.append(f"private theorem chunk{i}_disjoint : Disjoint chunk{i} ({tail}) := by decide +kernel")

lines.append("theorem residualIDs_card : residualIDs.card = 389 := by")
lines.append("  rw [residualIDs, Finset.card_union_of_disjoint chunk0_disjoint, chunk0_card]")
lines.append("  rw [Finset.card_union_of_disjoint chunk1_disjoint, chunk1_card]")
lines.append("  rw [Finset.card_union_of_disjoint chunk2_disjoint, chunk2_card]")
lines.append("  rw [chunk3_card]")
lines.append("  norm_num")
block_size = 100
block_count = (5011 + block_size - 1) // block_size
for i in range(block_count):
    lo = i * block_size
    hi = min((i + 1) * block_size, 5011)
    lines.append(f"private theorem mem_iff_block{i:02d} (n : Fin 5011)")
    if i == 0:
        lines.append(f"    (hlo : 0 ≤ n.val) (hhi : n.val < {hi}) :")
    else:
        lines.append(f"    (hlo : {lo} ≤ n.val) (hhi : n.val < {hi}) :")
    lines.append("    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by")
    lines.append("  rcases n with ⟨k, hk⟩")
    lines.append("  interval_cases k <;>")
    lines.append("    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel")
    lines.append("")

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
    "output_sha256": sha256(OUT),
    "scope": "source reconstruction and emitted bytes; Lean elaboration is CI-pending",
}
(LANE / "emit_residual_census-report.json").write_text(
    json.dumps(report, indent=2) + "\n", encoding="utf-8"
)
print(json.dumps(report, indent=2))
