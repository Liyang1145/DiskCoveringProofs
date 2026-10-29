#!/usr/bin/env python3
"""Emit the missing top aggregate for the 1182-packet batch.

The upstream emitter uses ``Path(o["path"]).stem`` on manifests whose paths
contain Windows separators.  That is harmless on Windows but makes every path
a single filename on Linux.  This lane-local emitter reads the already emitted
sub-aggregates and preserves the upstream packet inventory.  It fixes the
generated `Disjoint` eliminations (Lean `⦃a⦄` binders cannot be supplied
positionally as `f a h`) and aggregates the eight parts with
`Finset.univ.biUnion`, avoiding the upstream's kernel-heavy nested-union
disjointness checks.  The eight parts are consecutive id intervals, so their
pairwise disjointness is proved from two small `Finset.all` interval checks per
part plus `omega`, rather than by intersecting every pair of 168-element sets
in the kernel.
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
ids = rest["ids"]
chunks = [ids[i * 168:(i + 1) * 168] for i in range(7)] + [ids[7 * 168:]]
assert [len(c) for c in chunks] == [168] * 7 + [6]
bounds = [(min(c), max(c)) for c in chunks]
assert all(bounds[i][1] < bounds[i + 1][0] for i in range(7))

lines = ["".join(f"import N11Formalization.{s}\n" for s in SUBS)]
lines.append(f"import N11Formalization.{BASE}\n")
lines.append(f"""/-! Top aggregate of {count} packets, assembled from {len(SUBS)} sub-aggregates.
Every `decide +kernel` here compares at most 168-element literal sets, so the
kernel never walks a >168-deep insert chain. -/
set_option autoImplicit false
namespace N11Formalization.{TOP}
open Finset
noncomputable section
""")
lines.append("def part : Fin 8 → Finset (Fin 5011)")
for i, s in enumerate(SUBS):
    lines.append(f"  | {i} => {s}.newIDs")
lines.append("def newIDs : Finset (Fin 5011) := Finset.univ.biUnion part")
lines.append("theorem new_mem (n : Fin 5011) : n ∈ newIDs ↔ " +
             " ∨ ".join(f"n ∈ {s}.newIDs" for s in SUBS) + " := by")
lines.append("  simp only [newIDs, Finset.mem_biUnion, Finset.mem_univ, true_and]")
lines.append("  constructor")
lines.append("  · rintro ⟨i, hi⟩")
lines.append("    fin_cases i <;> simp_all [part]")
lines.append("  · rintro (" + " | ".join(f"h{i}" for i in range(len(SUBS))) + ")")
for i, s in enumerate(SUBS):
    lines.append(f"    · exact ⟨{i}, by simpa [part] using h{i}⟩")
lines.append("""private theorem of_all_le {s : Finset (Fin 5011)} {hi : ℕ}
    (h : (s.all fun n => n.val ≤ hi) = true) :
    ∀ n, n ∈ s → n.val ≤ hi := by
  intro n hn
  exact (Finset.all_eq_true.mp h) n hn
private theorem of_all_ge {s : Finset (Fin 5011)} {lo : ℕ}
    (h : (s.all fun n => lo ≤ n.val) = true) :
    ∀ n, n ∈ s → lo ≤ n.val := by
  intro n hn
  exact (Finset.all_eq_true.mp h) n hn""")
for i, (lo, hi) in enumerate(bounds, 1):
    lines.append(f"""private theorem s{i:02}_bounds : ∀ n, n ∈ {SUBS[i-1]}.newIDs →
    {lo} ≤ n.val ∧ n.val ≤ {hi} := by
  intro n hn
  exact ⟨of_all_ge (s := {SUBS[i-1]}.newIDs) (by decide +kernel) n hn,
    of_all_le (s := {SUBS[i-1]}.newIDs) (by decide +kernel) n hn⟩""")
pair_names = []
for i in range(8):
    for j in range(i + 1, 8):
        name = f"disjoint_s{i+1:02}_s{j+1:02}"
        pair_names.append(name)
        lines.append(f"""private theorem {name} : Disjoint {SUBS[i]}.newIDs {SUBS[j]}.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have bi := s{i+1:02}_bounds n hi
  have bj := s{j+1:02}_bounds n hj
  omega""")
lines.append(f"theorem new_count : newIDs.card = {count} := by")
lines.append("  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 8)) part := by")
lines.append("    intro i _ j _ hij")
lines.append(f"    fin_cases i <;> fin_cases j <;> simp_all [part, {', '.join(pair_names)}]")
lines.append("  rw [newIDs, Finset.card_biUnion hdisj]")
lines.append("  simp only [Fin.sum_univ_eight, part,")
lines.append("      " + ",\n      ".join(f"{s}.new_count" for s in SUBS) + "]")
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
    lines.append(f"  · exact (Finset.disjoint_left.mp {s}.disjoint_sharp) (a := a) h hb")
lines.append("end")
lines.append(f"end N11Formalization.{TOP}")
lines.append(f"#check @N11Formalization.{TOP}.new_count")
lines.append(f"#print axioms N11Formalization.{TOP}.new_count")
lines.append(f"#print axioms N11Formalization.{TOP}.new_radius")
lines.append(f"#print axioms N11Formalization.{TOP}.new_terminal")
text = "\n".join(lines) + "\n"
data = text.encode("utf-8")
expected = hier["outputs"][-1]
# The output intentionally differs from the frozen upstream bytes: the latter
# contains a kernel-heavy first disjointness check and the `⦃a⦄` call bug.  The
# upstream record remains the provenance anchor for the 1182-member inventory.
assert expected["module"] == TOP
assert count == 1182

out = LEAN / f"{TOP}.lean"
out.write_bytes(data)
report = {
    "module": TOP,
    "upstream_manifest": "Paid16GeneralNext1182-hier-manifest.json",
    "upstream_chars": expected["bytes"],
    "upstream_sha256": expected["sha256"],
    "corrections": [
        "supply implicit Disjoint.left element with (a := a)",
        "use Finset.univ.biUnion over Fin 8 and pass card_biUnion's disjointness hypothesis explicitly",
        "prove part disjointness from manifest interval bounds plus omega, with 16 set-local kernel checks instead of 28 pairwise set intersections",
        "replace the final kernel numeral evaluation by norm_num",
        "remove maxRecDepth 10000",
    ],
    "corrected_chars": len(text),
    "corrected_utf8_bytes": len(data),
    "corrected_sha256": sha256(data),
    "scope": "source emission and inventory only; Lean elaboration is CI-pending",
}
(LANE / "emit_next1182_top-report.json").write_text(
    json.dumps(report, indent=2) + "\n", encoding="utf-8"
)
print(f"wrote {out} ({len(data)} bytes, sha256 {sha256(data)})")
