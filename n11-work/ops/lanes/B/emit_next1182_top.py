#!/usr/bin/env python3
"""Emit the missing top aggregate for the 1182-packet batch.

The upstream emitter uses ``Path(o["path"]).stem`` on manifests whose paths
contain Windows separators.  That is harmless on Windows but makes every path
a single filename on Linux.  This lane-local emitter reads the already emitted
sub-aggregates and reproduces only the top module, byte-for-byte according to
the recorded manifest.
"""
from pathlib import Path
import hashlib
import json

LANE = Path(__file__).resolve().parent
ROOT = LANE.parents[3]
EVIDENCE = ROOT / "n11-work/evidence-20261028/evidence"
LEAN = ROOT / "n11-work/lean/N11Formalization"
TOP = "Paid16GeneralNext1182"
BASE = "EnergyTerminalBatchB12"
SUBS = [f"Paid16GeneralNext1182S{i:02}" for i in range(1, 9)]


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


rest = json.loads((EVIDENCE / "rest1182-emission-manifest.json").read_text(encoding="utf-8-sig"))
hier = json.loads((EVIDENCE / "Paid16GeneralNext1182-hier-manifest.json").read_text())
count = len(rest["ids"])
assert count == 1182
assert [o["module"] for o in hier["outputs"]][-1] == TOP
assert hier["subs"] == SUBS

lines = ["".join(f"import N11Formalization.{s}\n" for s in SUBS)]
lines.append(f"import N11Formalization.{BASE}\n")
lines.append(f"""/-! Top aggregate of {count} packets, assembled from {len(SUBS)} sub-aggregates.
Every `decide +kernel` here compares at most 168-element literal sets, so the
kernel never walks a >168-deep insert chain. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace N11Formalization.{TOP}
open Finset
noncomputable section
""")
chain = SUBS[-1] + ".newIDs"
for s in SUBS[-2::-1]:
    chain = f"{s}.newIDs ∪ ({chain})"
lines.append(f"def newIDs : Finset (Fin 5011) := {chain}")
lines.append("theorem new_mem (n : Fin 5011) : n ∈ newIDs ↔ " +
             " ∨ ".join(f"n ∈ {s}.newIDs" for s in SUBS) + " := by")
lines.append("  simp only [newIDs, Finset.mem_union]")
lines.append(f"theorem new_count : newIDs.card = {count} := by")
for i, s in enumerate(SUBS[:-1]):
    expr = SUBS[i + 1] + ".newIDs"
    for tail in SUBS[i + 2:]:
        expr = f"{tail}.newIDs ∪ ({expr})"
    lines.append(f"  have d{i} : Disjoint {s}.newIDs ({expr}) := by decide +kernel")
lines.append("  rw [newIDs]")
for i, s in enumerate(SUBS[:-1]):
    lines.append(f"  rw [Finset.card_union_of_disjoint d{i}, {s}.new_count]")
lines.append(f"  rw [{SUBS[-1]}.new_count]")
lines.append("  norm_num")
lines.append("""theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases (new_mem n).mp hn with """ + " | ".join("h" for _ in SUBS))
for s in SUBS:
    lines.append(f"  · exact {s}.new_terminal n h")
lines.append("""theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases (new_mem n).mp hn with """ + " | ".join("h" for _ in SUBS))
for s in SUBS:
    lines.append(f"  · exact {s}.new_radius n h y hy0 hy1 hc C Z r hf")
lines.append("theorem disjoint_sharp : Disjoint newIDs Patch120SharpDispatch.sharpIDs := by")
lines.append("  rw [Finset.disjoint_left]")
lines.append("  intro a ha hb")
lines.append("  rcases (new_mem a).mp ha with " + " | ".join("h" for _ in SUBS))
for s in SUBS:
    lines.append(f"  · exact (Finset.disjoint_left.mp {s}.disjoint_sharp) a h hb")
lines.append("end")
lines.append(f"end N11Formalization.{TOP}")
lines.append(f"#check @N11Formalization.{TOP}.new_count")
lines.append(f"#print axioms N11Formalization.{TOP}.new_count")
lines.append(f"#print axioms N11Formalization.{TOP}.new_radius")
lines.append(f"#print axioms N11Formalization.{TOP}.new_terminal")
text = "\n".join(lines) + "\n"
data = text.encode("utf-8")
expected = hier["outputs"][-1]
# The upstream manifest records len(text), not UTF-8 byte length.
assert len(text) == expected["bytes"], (len(text), expected["bytes"])
assert sha256(data) == expected["sha256"], (sha256(data), expected["sha256"])

out = LEAN / f"{TOP}.lean"
out.write_bytes(data)
print(f"wrote {out} ({len(data)} bytes, sha256 {sha256(data)})")
