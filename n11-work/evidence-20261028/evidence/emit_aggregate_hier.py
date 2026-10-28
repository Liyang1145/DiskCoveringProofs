"""Hierarchical (memory-safe) aggregate for a large emitted packet batch.

Measured constraint: `decide +kernel` on a `Finset` literal whose insert chain is
>~600 deep either exceeds the kernel's default recursion limit (1182 raised
`(kernel) deep recursion detected`) or, with `maxRecDepth 10000`, thrashes
(7.3 GB RSS, ~15% CPU, no progress in 5 min). 505 elements are fine.

So the batch is aggregated in two levels:
  * sub-aggregates of `--sub` packet modules each: literal ids, `simp` membership,
    21-way `sub` dispatches, a <=168-literal `decide +kernel` cardinality, an
    n-way terminal/radius dispatch, and a `Disjoint ... sharpIDs` check;
  * a top aggregate that only ever compares <=168-element sets, assembling
    `newIDs` as a right-nested union and summing the sub-cardinalities through
    `Finset.card_union_of_disjoint`.

Run with:  python emit_aggregate_hier.py --manifest=... --top=... --tag=...
           --base=... --count=1182 --sub=8
"""
from pathlib import Path
import hashlib
import json
import sys

SPEC = {"sub": 8, "base": "EnergyTerminalBatchB12"}
for a in sys.argv[1:]:
    if a.startswith("--") and "=" in a:
        k, v = a[2:].split("=", 1)
        SPEC[k] = int(v) if v.isdigit() else v
assert "manifest" in SPEC and "top" in SPEC and "count" in SPEC, SPEC

here = Path(__file__).resolve().parent
proj = here.parents[1]
lean = proj / "lean" / "N11Formalization"
man = json.loads((here / SPEC["manifest"]).read_text(encoding="utf-8-sig"))
mods = [Path(o["path"]).stem for o in man["outputs"]
        if Path(o["path"]).stem.startswith("Paid16GeneralH")]
ids = man["ids"]
blocks = [ids[i:i + 21] for i in range(0, len(ids), 21)]
assert len(blocks) == len(mods) and sum(len(b) for b in blocks) == SPEC["count"] == len(ids)
SUB = SPEC["sub"]
groups = [list(range(i, min(i + SUB, len(blocks)))) for i in range(0, len(blocks), SUB)]
print(f"{len(mods)} packet modules -> {len(groups)} sub-aggregates of <= {SUB}")

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest().upper()

def emit(name, text):
    p = lean / (name + ".lean")
    if p.exists():
        p.unlink()
    with p.open("x", encoding="utf-8", newline="\n") as f:
        f.write(text)
    return {"module": name, "sha256": sha(p), "bytes": len(text)}

def block_defs(k):
    """literal ids{k}, mem_ids{k}, sub{k} for global block index k."""
    m, b = mods[k], blocks[k]
    kk = f"{k:02}"
    disj = " ∨ ".join(f"n = {x}" for x in b)
    out = [f"def ids{kk} : Finset (Fin 5011) := " + "{" + ",".join(map(str, b)) + "}",
           f"theorem mem_ids{kk} (n : Fin 5011) : n ∈ ids{kk} ↔ {disj} := by",
           f"  simp only [ids{kk}, Finset.mem_insert, Finset.mem_singleton]",
           f"theorem ids{kk}_card : ids{kk}.card = {len(b)} := by decide +kernel",
           f"theorem sub{kk} (n : Fin 5011) (hn : n ∈ ids{kk}) : n ∈ {m}.newIDs := by",
           f"  rcases (mem_ids{kk} n).mp hn with " + " | ".join("rfl" for _ in b)]
    for i in range(len(b)):
        out.append(f"  · exact Finset.mem_image.mpr ⟨{i}, Finset.mem_univ _, rfl⟩")
    return out

outputs = []
subs = []
for gi, g in enumerate(groups):
    sname = f"{SPEC['top']}S{gi + 1:02}"
    subs.append((sname, g))
    n = sum(len(blocks[k]) for k in g)
    L = ["".join(f"import N11Formalization.{mods[k]}\n" for k in g),
         f"""/-! Sub-aggregate {gi + 1}/{len(groups)}: {len(g)} packet modules, {n} ids.
Cardinality is kernel-checked on <= {SUB * 21}-element literal sets only. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace N11Formalization.{sname}
open Finset
noncomputable section
"""]
    for k in g:
        L += block_defs(k)
    chain = f"ids{g[-1]:02}"
    for k in g[-2::-1]:
        chain = f"ids{k:02} ∪ ({chain})"
    L.append(f"def newIDs : Finset (Fin 5011) := {chain}")
    L.append("theorem new_mem (n : Fin 5011) : n ∈ newIDs ↔ " +
             " ∨ ".join(f"n ∈ ids{k:02}" for k in g) + " := by")
    L.append("  simp only [newIDs, Finset.mem_union]")
    L.append(f"theorem new_count : newIDs.card = {n} := by decide +kernel")
    L.append("""theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases (new_mem n).mp hn with """ + " | ".join("h" for _ in g))
    for k in g:
        L.append(f"  · exact {mods[k]}.new_terminal n (sub{k:02} n h)")
    L.append("""theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases (new_mem n).mp hn with """ + " | ".join("h" for _ in g))
    for k in g:
        L.append(f"  · exact {mods[k]}.new_radius n (sub{k:02} n h) y hy0 hy1 hc C Z r hf")
    L.append("theorem disjoint_sharp : Disjoint newIDs Patch120SharpDispatch.sharpIDs := by decide +kernel")
    L.append("end")
    L.append(f"end N11Formalization.{sname}")
    L.append(f"#print axioms N11Formalization.{sname}.new_count")
    L.append(f"#print axioms N11Formalization.{sname}.new_radius")
    outputs.append(emit(sname, "\n".join(L) + "\n"))

# ---- top ---------------------------------------------------------------
L = ["".join(f"import N11Formalization.{s}\n" for s, _ in subs)]
if SPEC["base"] != "EnergyTerminalBatchB11":
    L.append("import N11Formalization." + SPEC["base"] + "\n")
L.append(f"""/-! Top aggregate of {len(ids)} packets, assembled from {len(subs)} sub-aggregates.
Every `decide +kernel` here compares at most {SUB * 21}-element literal sets, so the
kernel never walks a >{SUB * 21}-deep insert chain. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace N11Formalization.{SPEC['top']}
open Finset
noncomputable section
""")
chain = subs[-1][0] + ".newIDs"
for s, _ in subs[-2::-1]:
    chain = f"{s}.newIDs ∪ ({chain})"
L.append(f"def newIDs : Finset (Fin 5011) := {chain}")
L.append("theorem new_mem (n : Fin 5011) : n ∈ newIDs ↔ " +
         " ∨ ".join(f"n ∈ {s}.newIDs" for s, _ in subs) + " := by")
L.append("  simp only [newIDs, Finset.mem_union]")
# cardinality: peel sub-aggregates one at a time
L.append(f"theorem new_count : newIDs.card = {len(ids)} := by")
for i, (s, _) in enumerate(subs[:-1]):
    expr = subs[i + 1][0] + ".newIDs"
    for tt, _ in subs[i + 2:]:
        expr = f"{tt}.newIDs ∪ ({expr})"
    L.append(f"  have d{i} : Disjoint {s}.newIDs ({expr}) := by decide +kernel")
L.append("  rw [newIDs]")
for i, (s, _) in enumerate(subs[:-1]):
    L.append(f"  rw [Finset.card_union_of_disjoint d{i}, {s}.new_count]")
L.append(f"  rw [{subs[-1][0]}.new_count]")
L.append("  norm_num")
L.append("""theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases (new_mem n).mp hn with """ + " | ".join("h" for _ in subs))
for s, _ in subs:
    L.append(f"  · exact {s}.new_terminal n h")
L.append("""theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases (new_mem n).mp hn with """ + " | ".join("h" for _ in subs))
for s, _ in subs:
    L.append(f"  · exact {s}.new_radius n h y hy0 hy1 hc C Z r hf")
L.append("theorem disjoint_sharp : Disjoint newIDs Patch120SharpDispatch.sharpIDs := by")
L.append("  rw [Finset.disjoint_left]")
L.append("  intro a ha hb")
L.append("  rcases (new_mem a).mp ha with " + " | ".join("h" for _ in subs))
for s, _ in subs:
    L.append(f"  · exact (Finset.disjoint_left.mp {s}.disjoint_sharp) a h hb")
L.append("end")
L.append(f"end N11Formalization.{SPEC['top']}")
L.append(f"#check @N11Formalization.{SPEC['top']}.new_count")
L.append(f"#print axioms N11Formalization.{SPEC['top']}.new_count")
L.append(f"#print axioms N11Formalization.{SPEC['top']}.new_radius")
L.append(f"#print axioms N11Formalization.{SPEC['top']}.new_terminal")
outputs.append(emit(SPEC["top"], "\n".join(L) + "\n"))

mf = here / (SPEC["top"] + "-hier-manifest.json")
mf.write_text(json.dumps({"spec": SPEC, "subs": [s for s, _ in subs],
                          "outputs": outputs}, indent=2), encoding="utf-8")
print("emitted", len(outputs), "modules ->", mf.name)
