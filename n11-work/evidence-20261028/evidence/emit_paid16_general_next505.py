"""Emit Lean packet modules for the 505 HOST-passing `next512` own-cells.

Input : evidence/codex-handoff/paid16-general-next512.json  (HOST PROPOSAL ONLY)
Output: lean/N11Formalization/PaidBlock.lean              (Block union algebra)
        lean/N11Formalization/Paid16GeneralH{k}.lean      (<=21 packets each)
        lean/N11Formalization/Paid16GeneralNext505.lean   (aggregate, 505 ids)
        lean/N11Formalization/EnergyTerminalBatchB12.lean (dispatch, 815 paid)
        lean/N11Formalization/EnergyTerminalBatchB12Main.lean (conditional main)

CREDIT RULE: generation is DRAFT ONLY. A packet counts only after
 (a) its module builds, (b) `Valid packet` is kernel-checked by `decide +kernel`,
 (c) the aggregate + dispatch + root import probe are green.
Nothing here changes any paid count.

The `Packet` literal / `Valid` proof text is byte-compatible with
`evidence/codex-handoff/emit_paid16_general_first42.py` (the emitter that paid
G01/G02, extended by `emit_paid16_general_remaining210.py` to G03..G12).
Only the proposal file, the slice, the module names and the aggregation
(the `PaidBlock.Block` union algebra instead of hand-written n-ary rcases)
differ.

Usage:
  python emit_paid16_general_next505.py --pilot   # PaidBlock + Paid16GeneralH01
  python emit_paid16_general_next505.py --all     # every module
"""
from pathlib import Path
import hashlib
import json
import sys

here = Path(__file__).resolve()
proj = here.parents[2]                       # ...\n11-formalization
lean = proj / "lean" / "N11Formalization"
hand = proj / "evidence" / "codex-handoff"

PILOT = "--pilot" in sys.argv
ALL = "--all" in sys.argv
assert PILOT != ALL, "give exactly one of --pilot / --all"

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest().upper()

def guard(p, want):
    got = sha(p)
    assert got == want, f"HASH GUARD {Path(p).name}: {got} != {want}"

# ---- frozen inputs -------------------------------------------------------
PROPOSAL = hand / "paid16-general-next512.json"
guard(PROPOSAL, "F49F06FC57A818E464D8DCBDAACE2E4D57A3C2E84CEA27FE86C4551363F3DD16")
guard(lean / "Paid16CellCertificate.lean",
      "897FBF8D2CFE4F2C51E6142C03F068BA240D6474964B026E1C81EDF9A019CA58")
guard(lean / "EnergyTerminalBatchB11.lean",
      "F291ABB5BBCFB20F9221678A22A40D4D3E53C224C410126B65024237C66E634A")
guard(proj / "lean" / "N11Formalization.lean",
      "4F5FE148D74B36DC77A7D69F80C7D3BD816AA0F069768E8A98B98D08EEF179BC")

doc = json.loads(PROPOSAL.read_text(encoding="utf-8-sig"))
assert doc["level"].startswith("HOST PROPOSAL ONLY")
records = [r for r in doc["records"] if r["pass"]]
assert len(records) == 505, len(records)
assert len({r["id"] for r in records}) == 505
for r in records:
    assert len(r["beta"]) == 16 and len(r["packets"]) == 36, r["id"]
    assert 1 <= len(r["lam"]) <= 7 and len(r["row_from"]) == len(r["lam"]), r["id"]

# ---- emission helpers (identical to the accepted emitter) ----------------
def ql(v):
    s = str(v)
    if "/" in s:
        n, d = s.split("/")
        return f"(({n} : ℚ)/{d})"
    return f"({s} : ℚ)"

def vec(xs):
    return "![" + ",".join(xs) + "]"

def line(p):
    return "⟨" + ",".join([ql(p[k]) for k in ("a", "b", "s", "c", "t", "e")] +
                          [f"({p['shift']} : ℤ)", "." + p["rule"]]) + "⟩"

def new(path, text):
    path = Path(path)
    data = text.encode("utf-8")
    if path.exists():
        assert path.read_bytes() == data, f"existing file differs: {path}"
        return {"path": str(path.relative_to(proj)), "sha256": sha(path), "reused": True}
    with path.open("x", encoding="utf-8", newline="\n") as f:
        f.write(text)
    return {"path": str(path.relative_to(proj)), "sha256": sha(path), "reused": False}

# ---- block algebra -------------------------------------------------------
BLOCK = r"""import N11Formalization.EnergyTerminalBatchB11

/-! Union algebra for concretely paid terminal blocks. A `Block` carries exactly
the three facts a dispatch module consumes: the id set, terminality of every id,
and the strict radius bound for every id on the closed simplex. `union` is
proof-only assembly: it adds no hypothesis and assumes no terminal. -/
set_option autoImplicit false
namespace N11Formalization.PaidBlock
open N11Formalization SourceChartIsometry ResumeNetwork
noncomputable section

structure Block where
  ids : Finset (Fin 5011)
  terminal : ∀ n, n ∈ ids → (DBMSourceTree.data n).terminal = true
  radius : ∀ n, n ∈ ids →
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        Feasible (chartAnchors y) C Z r → SourceExactRoot.sourceRadius < r

def Block.union (A B : Block) : Block where
  ids := A.ids ∪ B.ids
  terminal := by
    intro n hn
    rcases Finset.mem_union.mp hn with h | h
    · exact A.terminal n h
    · exact B.terminal n h
  radius := by
    intro n hn y hy0 hy1 hc C Z r hf
    rcases Finset.mem_union.mp hn with h | h
    · exact A.radius n h y hy0 hy1 hc C Z r hf
    · exact B.radius n h y hy0 hy1 hc C Z r hf

end
end N11Formalization.PaidBlock
#check @N11Formalization.PaidBlock.Block
#check @N11Formalization.PaidBlock.Block.union
#print axioms N11Formalization.PaidBlock.Block.union
"""

GROUP = 21
groups = [records[i:i + GROUP] for i in range(0, len(records), GROUP)]
assert sum(len(g) for g in groups) == 505
names = [f"Paid16GeneralH{k + 1:02}" for k in range(len(groups))]
outputs = []

def emit_group(subset, ns):
    n = len(subset)
    text = f"""import N11Formalization.PaidBlock
/-! Actual{n} OWN-cell packets from the HOST `next512` survey. `Valid` is paid
row-by-row by `decide +kernel`; no solver input is trusted. -/
set_option autoImplicit false
namespace N11Formalization.{ns}
open Finset Paid16CellCertificate
noncomputable section
set_option maxRecDepth 10000
abbrev Case := Fin {n}
"""
    text += "def nodeID : Case → Fin 5011 := " + vec([str(r["id"]) for r in subset]) + "\n"
    for i, r in enumerate(subset):
        pad = 7 - len(r["lam"])
        values = [str(r["id"]), vec([ql(v) for v in r["beta"]]),
                  vec([line(p) for p in r["packets"]]),
                  vec([str(v) for v in r["row_from"]] + ["0"] * pad),
                  vec([str(v) for v in r["row_to"]] + ["0"] * pad),
                  vec([ql(v) for v in r["lam"]] + ["(0 : ℚ)"] * pad), ql(r["rmin"])]
        text += "def packet%d : Packet := ⟨" % i + ",".join(values) + "⟩\n"
        text += f"""theorem valid{i} : Valid packet{i} := by
  constructor <;> decide +kernel
"""
    text += "def packet : Case → Packet := " + vec([f"packet{i}" for i in range(n)]) + "\n"
    text += "theorem all_valid (i : Case) : Valid (packet i) := by\n  fin_cases i\n"
    text += "".join(f"  · exact valid{i}\n" for i in range(n))
    text += """theorem node_binding (i : Case) : (packet i).nodeID = nodeID i := by
  fin_cases i <;> rfl
theorem terminal (i : Case) : (DBMSourceTree.data (nodeID i)).terminal = true := by
  simpa only [node_binding] using (all_valid i).terminal
theorem oracle_gt (i : Case) (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (nodeID i))
      (FlashLeafSplit.tlift y)) :
    (FlashCosineLeaf284Bridge.T : ℝ)^2 <
      ResumeNetwork.V2 (SourceChartIsometry.chartAnchors y) :=
  Paid16CellCertificate.oracle_gt (packet i) (all_valid i) y hy0 hy1
    (by simpa only [node_binding] using hc)
theorem common_chart_radius (i : Case) (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (nodeID i))
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r :=
  Paid16CellCertificate.common_chart_radius (packet i) (all_valid i) y hy0 hy1
    (by simpa only [node_binding] using hc) C Z r hf
def newIDs : Finset (Fin 5011) := univ.image nodeID
theorem new_count : newIDs.card = """ + str(n) + """ := by decide +kernel
theorem node_injective : Function.Injective nodeID := by
  unfold Function.Injective
  decide +kernel
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
  exact terminal i
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
  exact common_chart_radius i y hy0 hy1 hc C Z r hf
def block : PaidBlock.Block := ⟨newIDs, new_terminal, new_radius⟩
end
"""
    text += f"end N11Formalization.{ns}\n"
    text += "".join(f"#check @N11Formalization.{ns}.{name}\n" for name in
                    ("all_valid", "common_chart_radius", "new_count", "new_radius", "block"))
    text += "".join(f"#print axioms N11Formalization.{ns}.{name}\n" for name in
                    ("all_valid", "common_chart_radius", "new_radius"))
    return new(lean / (ns + ".lean"), text)

if PILOT:
    outputs.append(new(lean / "PaidBlock.lean", BLOCK))
    outputs.append(emit_group(groups[0], names[0]))
    for o in outputs:
        print("PILOT emitted", o["path"], o["sha256"])
    raise SystemExit(0)

outputs.append(new(lean / "PaidBlock.lean", BLOCK))
for g, ns in zip(groups, names):
    outputs.append(emit_group(g, ns))

# ---- aggregate ------------------------------------------------------------
chain = names[0] + ".block"
for c in names[1:]:
    chain = f"({chain}).union {c}.block"
imp = "".join(f"import N11Formalization.{c}\n" for c in names)
text = imp + f"""/-! Aggregate of all {len(records)} emitted HOST `next512` packets.
Assembly is `PaidBlock.Block.union` only: no new hypothesis, no assumed terminal. -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralNext505
open Finset
noncomputable section
def block : PaidBlock.Block := {chain}
def newIDs : Finset (Fin 5011) := block.ids
theorem new_count : newIDs.card = {len(records)} := by decide +kernel
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := block.terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := block.radius n hn y hy0 hy1 hc C Z r hf
theorem disjoint_paid : Disjoint EnergyTerminalBatchB11.paidIDs newIDs := by decide +kernel
theorem disjoint_sharp : Disjoint newIDs Patch120SharpDispatch.sharpIDs := by decide +kernel
end
end N11Formalization.Paid16GeneralNext505
#check @N11Formalization.Paid16GeneralNext505.new_count
#check @N11Formalization.Paid16GeneralNext505.new_radius
#print axioms N11Formalization.Paid16GeneralNext505.new_radius
#print axioms N11Formalization.Paid16GeneralNext505.new_count
"""
outputs.append(new(lean / "Paid16GeneralNext505.lean", text))

# ---- dispatch B12 ---------------------------------------------------------
text = f"""import N11Formalization.EnergyTerminalBatchB11
import N11Formalization.Paid16GeneralNext505

/-! Eight hundred fifteen actual energy terminals on the SAME closed truechart:
the 310 previously paid plus the {len(records)} `next512` HOST packets.
`RemainingTerminalRadius` is still explicit and UNPROVED, but it now quantifies
over {2076 - len(records)} terminals instead of 2076. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB12
open N11Formalization SourceChartIsometry ResumeNetwork
noncomputable section

def paidIDs : Finset (Fin 5011) :=
  EnergyTerminalBatchB11.paidIDs ∪ Paid16GeneralNext505.newIDs
theorem paid_count : paidIDs.card = {310 + len(records)} := by
  rw [paidIDs, Finset.card_union_of_disjoint Paid16GeneralNext505.disjoint_paid,
    EnergyTerminalBatchB11.paid_count, Paid16GeneralNext505.new_count]
  norm_num
theorem new_disjoint_old :
    Disjoint EnergyTerminalBatchB11.paidIDs Paid16GeneralNext505.newIDs :=
  Paid16GeneralNext505.disjoint_paid
theorem paid_not_sharp : Disjoint paidIDs Patch120SharpDispatch.sharpIDs := by
  rw [paidIDs]
  exact Finset.disjoint_union_left.mpr
    ⟨EnergyTerminalBatchB11.paid_not_sharp, Paid16GeneralNext505.disjoint_sharp⟩
theorem paid_terminal (n : Fin 5011) (hn : n∈paidIDs) :
    (DBMSourceTree.data n).terminal=true := by
  have h : n∈EnergyTerminalBatchB11.paidIDs ∨ n∈Paid16GeneralNext505.newIDs := by
    simpa only [paidIDs,Finset.mem_union] using hn
  rcases h with h | h
  · exact EnergyTerminalBatchB11.paid_terminal n h
  · exact Paid16GeneralNext505.new_terminal n h
theorem paid_radius (n : Fin 5011) (hn : n∈paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : Feasible (chartAnchors y) C Z r) : SourceExactRoot.sourceRadius < r := by
  have h : n∈EnergyTerminalBatchB11.paidIDs ∨ n∈Paid16GeneralNext505.newIDs := by
    simpa only [paidIDs,Finset.mem_union] using hn
  rcases h with h | h
  · exact EnergyTerminalBatchB11.paid_radius n h y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralNext505.new_radius n h y hy0 hy1 hc C Z r hf

def RemainingTerminalRadius : Prop :=
  ∀ n : Fin 5011,(DBMSourceTree.data n).terminal=true →
    n∉Patch120SharpDispatch.sharpIDs → n∉paidIDs →
    ∀ (y : Fin 9 → ℝ),(∀ q,0 ≤ y q) → (∑ q,y q=1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        Feasible (chartAnchors y) C Z r → SourceExactRoot.sourceRadius ≤ r
theorem chart_radius_of_remaining (hremaining : RemainingTerminalRadius)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q) (hy1 : ∑ q,y q=1)
    (C Z : Fin 11 → Point) (r : ℝ) (hf : Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius ≤ r := by
  obtain ⟨n,ht,hc⟩ := DBMTreeChartConsumer.chart9_terminal_cover y hy0 hy1
  by_cases hs : n∈Patch120SharpDispatch.sharpIDs
  · exact Patch120SharpDispatch.sharp_radius n hs y hc C Z r hf
  · by_cases he : n∈paidIDs
    · exact (paid_radius n he y hy0 hy1 hc C Z r hf).le
    · exact hremaining n ht hs he y hy0 hy1 hc C Z r hf

/-- Credit transfer: a B12 residual pays the B11 residual. -/
theorem remaining_of_b12 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB11.RemainingTerminalRadius := by
  intro n ht hs he y hy0 hy1 hc C Z r hf
  by_cases hp : n∈paidIDs
  · exact (paid_radius n hp y hy0 hy1 hc C Z r hf).le
  · exact h n ht hs hp y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalBatchB12
#check @N11Formalization.EnergyTerminalBatchB12.paid_count
#check @N11Formalization.EnergyTerminalBatchB12.paid_radius
#check @N11Formalization.EnergyTerminalBatchB12.chart_radius_of_remaining
#check @N11Formalization.EnergyTerminalBatchB12.remaining_of_b12
#print axioms N11Formalization.EnergyTerminalBatchB12.paid_radius
#print axioms N11Formalization.EnergyTerminalBatchB12.remaining_of_b12
"""
outputs.append(new(lean / "EnergyTerminalBatchB12.lean", text))

# ---- conditional main consumer -------------------------------------------
text = """import N11Formalization.C450ChainCompletionMain
import N11Formalization.EnergyTerminalBatchB12
import N11Formalization.ActualMetricClassReduction

/-! The conditional main statement with the energy premise weakened from
`EnergyTerminalBatchB11.RemainingTerminalRadius` (2076 terminals) to
`EnergyTerminalBatchB12.RemainingTerminalRadius` (1571 terminals). -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB12Main
noncomputable section

theorem main_of_energy_b12_and_seven_classes
    (henergy : EnergyTerminalBatchB12.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  C450ChainCompletionMain.main_of_energy_and_seven_classes
    (EnergyTerminalBatchB12.remaining_of_b12 henergy) hclasses

theorem full_disk_bound_of_energy_b12_and_seven_classes
    (henergy : EnergyTerminalBatchB12.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main (main_of_energy_b12_and_seven_classes henergy hclasses)).bounds

end
end N11Formalization.EnergyTerminalBatchB12Main
#check @N11Formalization.EnergyTerminalBatchB12Main.main_of_energy_b12_and_seven_classes
#print axioms N11Formalization.EnergyTerminalBatchB12Main.main_of_energy_b12_and_seven_classes
"""
outputs.append(new(lean / "EnergyTerminalBatchB12Main.lean", text))

print("emitted", len(outputs), "modules")
manifest = here.parent / "next505-emission-manifest.json"
with manifest.open("x", encoding="utf-8", newline="\n") as f:
    json.dump({"level": "DRAFT ONLY; every Valid/module/root/probe gate pending",
               "proposal": PROPOSAL.name, "proposal_sha256": sha(PROPOSAL),
               "n_records": len(records), "n_groups": len(groups),
               "ids": [r["id"] for r in records],
               "outputs": outputs}, f, indent=2)
print("manifest", manifest.name)
