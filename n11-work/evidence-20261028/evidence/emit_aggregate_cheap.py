"""Emit a CHEAP aggregate for an emitted packet batch.

Why this exists: the first aggregate design put `newIDs` at the union of 25
`Finset.univ.image nodeID` sets and asked `decide +kernel` for its cardinality.
That reduction unfolds `univ : Finset (Fin 5011)` once per module and then
de-duplicates a 505-element set: observed 7.5 GB RSS / 12% CPU / >11 min wall,
i.e. memory-thrashing rather than progress, and 1182 ids would be far worse.

This emitter avoids `univ` completely:
  * `ids{k}` is a LITERAL Finset per module, `mem_ids{k}` is a `simp` fact, and
    `sub{k} : ids{k} ⊆ H{k}.newIDs` is a 21-way literal dispatch;
  * `newIDs` is the union of the literals, so `new_mem` is `Finset.mem_union`
    and `new_count` is a kernel de-duplication of 505 literals with no `univ`;
  * `new_terminal` / `new_radius` are 25-way (resp. 57-way) dispatches through
    `sub{k}`, i.e. no large case bash and no kernel search.

Everything is still `Valid packet`-backed in the H modules; this module only
assembles them.
"""
from pathlib import Path
import hashlib
import json
import sys

SPEC = {
    "tag": "rest1182",
    "aggregate": "Paid16GeneralNext1182",
    "modules": None,          # filled from manifest
    # base module used for the disjointness fact
    "base": "EnergyTerminalBatchB12",
    "count": 1182,
}
for a in sys.argv[1:]:
    if a.startswith("--") and "=" in a:
        k, v = a[2:].split("=", 1)
        SPEC[k] = int(v) if v.isdigit() else v

here = Path(__file__).resolve().parent
proj = here.parents[1]
lean = proj / "lean" / "N11Formalization"

manifest = json.loads((here / SPEC["manifest"]).read_text(encoding="utf-8-sig"))
mods = []
for out in manifest["outputs"]:
    name = Path(out["path"]).stem
    if name.startswith("Paid16GeneralH"):
        mods.append(name)
ids = manifest["ids"]
spec = manifest.get("spec", {})
assert len(mods) * 21 >= len(ids), (len(mods), len(ids))

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest().upper()

# split the ordered id list exactly as the emitter grouped it
blocks = [ids[i:i + 21] for i in range(0, len(ids), 21)]
assert len(blocks) == len(mods)
assert sum(len(b) for b in blocks) == SPEC["count"] == len(ids)

L = []
L.append("".join(f"import N11Formalization.{m}\n" for m in mods))
if SPEC["base"] != "EnergyTerminalBatchB11":
    L.append("import N11Formalization." + SPEC["base"] + "\n")
L.append(f"""/-! CHEAP aggregate of the {len(ids)} packets emitted for `{SPEC['tag']}`.

`newIDs` is a union of LITERAL finsets (`ids{k}`), one per packet module, and
`sub{k} : ids{k} ⊆ {mods[0]}.newIDs`-style facts route each literal back to the
`Valid packet`-backed theorem of its own module. No `Finset.univ` is unfolded
and no large set is kernel-searched. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace N11Formalization.{SPEC['aggregate']}
open Finset
noncomputable section
""")

for k, (m, b) in enumerate(zip(mods, blocks)):
    kk = f"{k:02}"
    L.append(f"def ids{kk} : Finset (Fin 5011) := " + "{" + ",".join(str(x) for x in b) + "}")
    disj = " ∨ ".join(f"n = {x}" for x in b)
    L.append(f"theorem mem_ids{kk} (n : Fin 5011) : n ∈ ids{kk} ↔ {disj} := by")
    L.append(f"  simp [ids{kk}]")
    L.append(f"theorem ids{kk}_card : ids{kk}.card = {len(b)} := by decide +kernel")
    L.append(f"theorem sub{kk} (n : Fin 5011) (hn : n ∈ ids{kk}) : n ∈ {m}.newIDs := by")
    L.append(f"  rcases (mem_ids{kk} n).mp hn with " + " | ".join("rfl" for _ in b))
    for i in range(len(b)):
        L.append(f"  · exact Finset.mem_image.mpr ⟨{i}, Finset.mem_univ _, rfl⟩")

# newIDs = RIGHT-nested union, so `Finset.mem_union` yields the flat ∨ chain
chain = f"ids{len(mods) - 1:02}"
for k in range(len(mods) - 2, -1, -1):
    chain = f"ids{k:02} ∪ ({chain})"
L.append(f"def newIDs : Finset (Fin 5011) := {chain}")
mems = " ∨ ".join(f"n ∈ ids{k:02}" for k in range(len(mods)))
L.append(f"theorem new_mem (n : Fin 5011) : n ∈ newIDs ↔ {mems} := by")
L.append("  simp only [newIDs, Finset.mem_union]")
L.append(f"theorem new_count : newIDs.card = {len(ids)} := by decide +kernel")

L.append(f"""theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases (new_mem n).mp hn with """ + " | ".join("h" for _ in mods))
for k, m in enumerate(mods):
    L.append(f"  · exact {m}.new_terminal n (sub{k:02} n h)")

L.append(f"""theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases (new_mem n).mp hn with """ + " | ".join("h" for _ in mods))
for k, m in enumerate(mods):
    L.append(f"  · exact {m}.new_radius n (sub{k:02} n h) y hy0 hy1 hc C Z r hf")

L.append(f"""theorem disjoint_paid : Disjoint {SPEC['base']}.paidIDs newIDs := by decide +kernel
theorem disjoint_sharp : Disjoint newIDs Patch120SharpDispatch.sharpIDs := by decide +kernel
end
end N11Formalization.{SPEC['aggregate']}
#check @N11Formalization.{SPEC['aggregate']}.new_count
#check @N11Formalization.{SPEC['aggregate']}.new_radius
#print axioms N11Formalization.{SPEC['aggregate']}.new_radius
#print axioms N11Formalization.{SPEC['aggregate']}.new_count
#print axioms N11Formalization.{SPEC['aggregate']}.new_terminal
""")

text = "\n".join(L) + "\n"
path = lean / (SPEC["aggregate"] + ".lean")
if path.exists():
    path.unlink()
with path.open("x", encoding="utf-8", newline="\n") as f:
    f.write(text)
print("wrote", path.name, len(text), "bytes;", len(mods), "blocks;", len(ids), "ids")
print("sha256", sha(path))
