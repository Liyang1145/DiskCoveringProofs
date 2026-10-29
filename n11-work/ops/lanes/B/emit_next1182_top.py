#!/usr/bin/env python3
"""Emit the missing top aggregate for the 1182-packet batch.

The upstream emitter uses ``Path(o["path"]).stem`` on manifests whose paths
contain Windows separators.  That is harmless on Windows but makes every path
a single filename on Linux.  This lane-local emitter reads the already emitted
sub-aggregates and preserves the upstream packet inventory.  It fixes the
generated `Disjoint` eliminations (Lean `⦃a⦄` binders cannot be supplied
positionally as `f a h`) and aggregates the eight parts with
`Finset.univ.biUnion`, avoiding the upstream's kernel-heavy nested-union
disjointness checks.  The eight parts are consecutive id intervals.  Their
bounds are assembled from 57 small literal-block lemmas (at most 21 ids each),
using each block's already-proved membership disjunction and literal `norm_num`
rather than kernel-reducing the set.
"""
from pathlib import Path
import hashlib
import json
import re

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

# Recover the literal `idsNN` blocks from the imported sub-aggregates.  The
# top-level disjointness proofs use only these integer bounds; they do not ask
# the kernel to compare two 168-element `Finset` values.
part_blocks = []
for i, sub in enumerate(SUBS):
    source = (LEAN / f"{sub}.lean").read_text()
    blocks = [(int(k), [int(x) for x in vals.split(",")])
              for k, vals in re.findall(
                  r"def ids(\d+) : Finset \(Fin 5011\) := \{([^}]*)\}", source)]
    assert blocks, sub
    assert len(blocks) * 21 >= len(chunks[i]) > (len(blocks) - 1) * 21
    assert [x for _, vals in blocks for x in vals] == chunks[i], sub
    part_blocks.append(blocks)

lines = ["".join(f"import N11Formalization.{s}\n" for s in SUBS)]
lines.append(f"import N11Formalization.{BASE}\n")
lines.append(f"""/-! Top aggregate of {count} packets, assembled from {len(SUBS)} sub-aggregates.
The eight parts are consecutive integer intervals.  Their pairwise
disjointness is proved from literal membership bounds, not by kernel-reducing
168-element `Finset` values. -/
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
block_names = []
for i, (sub, blocks) in enumerate(zip(SUBS, part_blocks)):
    names = []
    for k, (idx, vals) in enumerate(blocks):
        name = f"block_s{i+1:02}_{k:02}_bounds"
        names.append(name)
        lo, hi = min(vals), max(vals)
        lines.append(f"private theorem {name} (n : Fin 5011)")
        lines.append(f"    (h : n ∈ {sub}.ids{idx:02}) : {lo} ≤ n.val ∧ n.val ≤ {hi} := by")
        lines.append(f"  rcases ({sub}.mem_ids{idx:02} n).mp h with " +
                     " | ".join("rfl" for _ in vals))
        lines.append("  all_goals norm_num")
    block_names.append(names)
for i, (sub, blocks) in enumerate(zip(SUBS, part_blocks)):
    lo, hi = bounds[i]
    lines.append(f"private theorem part_s{i+1:02}_bounds (n : Fin 5011)")
    lines.append(f"    (h : n ∈ {sub}.newIDs) : {lo} ≤ n.val ∧ n.val ≤ {hi} := by")
    lines.append(f"  rcases ({sub}.new_mem n).mp h with " +
                 " | ".join(f"h{k}" for k in range(len(blocks))))
    for k, (idx, vals) in enumerate(blocks):
        b = f"block_s{i+1:02}_{k:02}_bounds n h{k}"
        lines.append(f"  · have hb := {b}")
        lines.append("    constructor <;> omega")
pair_names = []
for i in range(8):
    for j in range(i + 1, 8):
        name = f"disjoint_s{i+1:02}_s{j+1:02}"
        pair_names.append(name)
        lines.append(f"private theorem {name} : Disjoint {SUBS[i]}.newIDs {SUBS[j]}.newIDs := by")
        lines.append("  rw [Finset.disjoint_left]")
        lines.append("  intro n hi hj")
        lines.append(f"  have hi := part_s{i+1:02}_bounds n hi")
        lines.append(f"  have hj := part_s{j+1:02}_bounds n hj")
        lines.append("  omega")
lines.append("theorem lower_bound (n : Fin 5011) (hn : n ∈ newIDs) : 2565 ≤ n.val := by")
lines.append("  rcases (new_mem n).mp hn with " + " | ".join("h" for _ in SUBS))
for i, sub in enumerate(SUBS):
    lines.append(f"  · have hb := (part_s{i+1:02}_bounds n h).1")
    lines.append("    omega")
lines.append(f"theorem new_count : newIDs.card = {count} := by")
lines.append("  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 8)) part := by")
lines.append("    intro i _ j _ hij")
lines.append("    change Disjoint (part i) (part j)")
lines.append("    fin_cases i")
for i in range(8):
    lines.append("    · fin_cases j")
    for j in range(8):
        if i == j:
            lines.append("      · exact (hij rfl).elim")
        else:
            thm = (f"disjoint_s{i+1:02}_s{j+1:02}" if i < j
                   else f"disjoint_s{j+1:02}_s{i+1:02}.symm")
            left = f"Paid16GeneralNext1182S{i+1:02}.newIDs"
            right = f"Paid16GeneralNext1182S{j+1:02}.newIDs"
            lines.append("      · first")
            lines.append(f"          | (change Disjoint {left} {right}; exact {thm})")
            lines.append(f"          | (simpa [part, Function.onFun] using {thm})")
lines.append("  rw [newIDs, Finset.card_biUnion hdisj]")
lines.append("  simp [Fin.sum_univ_succ, part,")
lines.append("      " + ",\n      ".join(f"{s}.new_count" for s in SUBS) + "]")
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
lines.append(f"#print axioms N11Formalization.{TOP}.lower_bound")
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
        "prove part disjointness from literal membership bounds (consecutive intervals)",
        "prove each literal-block bound from its existing membership disjunction with literal norm_num, then assemble parts from the block conjunction using omega",
        "lift each part-local lower bound to the global lower bound by transitivity with omega",
        "dispatch the 64 ordered PairwiseDisjoint cases explicitly instead of relying on simp_all",
        "unfold Function.onFun to expose Disjoint (part i) (part j) before the 64-case dispatch",
        "expand the eight-term Fin sum recursively with Fin.sum_univ_succ",
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
