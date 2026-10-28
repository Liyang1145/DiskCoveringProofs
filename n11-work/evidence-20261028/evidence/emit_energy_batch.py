"""SPEC-driven emitter for a batch of HOST-proposed energy packets.

One code path, one spec per batch. Each emitted module carries
  * `Valid packet_i` closed by `decide +kernel`  (the only trusted check),
  * `block : PaidBlock.Block`                    (the dispatch interface),
and the batch closes with an aggregate, a dispatch module `B{k}` that enlarges
`paidIDs`, and a conditional main consumer.

DRAFT ONLY: nothing here changes a paid count. Credit requires module build,
aggregate build, root import, root build and a probe gate.
"""
from pathlib import Path
import hashlib
import json
import sys

SPEC = {
    # ---- inputs ---------------------------------------------------------
    "proposal": "paid16-general-rest1515.json",
    "proposal_sha": "80A6420F948F6E160915CAA08137D9EEA8B7901A4B20CFF68314CD2722B972F4",
    "expect_records": 1182,
    "base_module": "EnergyTerminalBatchB12",          # previous dispatch
    "base_sha": "A6EF5D9265BDEA72D5DA05330C3DE729E88795EF142D056AE1699FA268C435F3",
    "base_paid": 815,
    "total_terminals": 2386,
    # ---- outputs --------------------------------------------------------
    "first_index": 26,                                # H26 .. H82
    "aggregate": "Paid16GeneralNext1182",
    "dispatch": "EnergyTerminalBatchB13",
    "main": "EnergyTerminalBatchB13Main",
    "base_main": "EnergyTerminalBatchB12Main",
    "base_main_theorem": "main_of_energy_b12_and_seven_classes",
    "manifest": "rest1182-emission-manifest.json",
    "tag": "rest1182",
}
for a in sys.argv[1:]:
    if a.startswith("--") and "=" in a:
        k, v = a[2:].split("=", 1)
        SPEC[k] = int(v) if v.isdigit() else v

PILOT = "--pilot" in sys.argv
ALL = "--all" in sys.argv
assert PILOT != ALL, "give exactly one of --pilot / --all"

here = Path(__file__).resolve().parent
proj = here.parents[1]                       # ...\n11-formalization
lean = proj / "lean" / "N11Formalization"
hand = proj / "evidence" / "codex-handoff"

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest().upper()

def guard(p, want):
    got = sha(p)
    assert got == want, f"HASH GUARD {Path(p).name}: {got} != {want}"

PROPOSAL = hand / SPEC["proposal"]
guard(PROPOSAL, SPEC["proposal_sha"])
guard(lean / "Paid16CellCertificate.lean",
      "897FBF8D2CFE4F2C51E6142C03F068BA240D6474964B026E1C81EDF9A019CA58")
guard(lean / (SPEC["base_module"] + ".lean"), SPEC["base_sha"])
guard(lean / "PaidBlock.lean",
      "88A8C607A2F74E5F09E0521D30CD4BC32BB57E4FDF452D4EAFF5671370565F65")

doc = json.loads(PROPOSAL.read_text(encoding="utf-8-sig"))
assert doc["level"].startswith("HOST PROPOSAL ONLY"), doc["level"]
records = [r for r in doc["records"] if r["pass"]]
assert len(records) == SPEC["expect_records"], len(records)
assert len({r["id"] for r in records}) == len(records)
for r in records:
    assert len(r["beta"]) == 16 and len(r["packets"]) == 36, r["id"]
    assert 1 <= len(r["lam"]) <= 7 and len(r["row_from"]) == len(r["lam"]), r["id"]

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

def new(name, text):
    path = lean / name
    data = text.encode("utf-8")
    if path.exists():
        assert path.read_bytes() == data, f"existing file differs: {path}"
        return {"path": str(path.relative_to(proj)), "sha256": sha(path), "reused": True}
    with path.open("x", encoding="utf-8", newline="\n") as f:
        f.write(text)
    return {"path": str(path.relative_to(proj)), "sha256": sha(path), "reused": False}

GROUP = 21
groups = [records[i:i + GROUP] for i in range(0, len(records), GROUP)]
names = [f"Paid16GeneralH{k + SPEC['first_index']:02}" for k in range(len(groups))]
assert sum(len(g) for g in groups) == len(records)

def module_text(subset, ns, idx):
    n = len(subset)
    t = f"""import N11Formalization.PaidBlock
/-! Actual{n} OWN-cell packets from the HOST `{SPEC['tag']}` survey. `Valid` is
paid row-by-row by `decide +kernel`; no solver input is trusted. -/
set_option autoImplicit false
namespace N11Formalization.{ns}
open Finset Paid16CellCertificate
noncomputable section
set_option maxRecDepth 10000
abbrev Case := Fin {n}
"""
    t += "def nodeID : Case → Fin 5011 := " + vec([str(r["id"]) for r in subset]) + "\n"
    for i, r in enumerate(subset):
        pad = 7 - len(r["lam"])
        values = [str(r["id"]), vec([ql(v) for v in r["beta"]]),
                  vec([line(p) for p in r["packets"]]),
                  vec([str(v) for v in r["row_from"]] + ["0"] * pad),
                  vec([str(v) for v in r["row_to"]] + ["0"] * pad),
                  vec([ql(v) for v in r["lam"]] + ["(0 : ℚ)"] * pad), ql(r["rmin"])]
        t += f"def packet{i} : Packet := ⟨" + ",".join(values) + "⟩\n"
        t += f"""theorem valid{i} : Valid packet{i} := by
  constructor <;> decide +kernel
"""
    t += "def packet : Case → Packet := " + vec([f"packet{i}" for i in range(n)]) + "\n"
    t += "theorem all_valid (i : Case) : Valid (packet i) := by\n  fin_cases i\n"
    t += "".join(f"  · exact valid{i}\n" for i in range(n))
    t += """theorem node_binding (i : Case) : (packet i).nodeID = nodeID i := by
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
    t += f"end N11Formalization.{ns}\n"
    t += "".join(f"#check @N11Formalization.{ns}.{name}\n" for name in
                 ("all_valid", "common_chart_radius", "new_count", "new_radius", "block"))
    t += "".join(f"#print axioms N11Formalization.{ns}.{name}\n" for name in
                 ("all_valid", "common_chart_radius", "new_radius"))
    return t

outputs = []
if PILOT:
    outputs.append(new(names[0] + ".lean", module_text(groups[0], names[0], 0)))
    for o in outputs:
        print("PILOT emitted", o["path"], o["sha256"])
    raise SystemExit(0)

for k, (g, ns) in enumerate(zip(groups, names)):
    outputs.append(new(ns + ".lean", module_text(g, ns, k)))

AGG = SPEC["aggregate"]
DISP = SPEC["dispatch"]
MAIN = SPEC["main"]
BASE = SPEC["base_module"]
nrec = len(records)
npaid = SPEC["base_paid"] + nrec
nrem = SPEC["total_terminals"] - npaid

chain = names[0] + ".block"
for c in names[1:]:
    chain = f"({chain}).union {c}.block"
imp = "".join(f"import N11Formalization.{c}\n" for c in names)
text = imp + f"""/-! Aggregate of all {nrec} emitted HOST `{SPEC['tag']}` packets.
Assembly is `PaidBlock.Block.union` only: no new hypothesis, no assumed terminal. -/
set_option autoImplicit false
namespace N11Formalization.{AGG}
open Finset
noncomputable section
def block : PaidBlock.Block := {chain}
def newIDs : Finset (Fin 5011) := block.ids
theorem new_count : newIDs.card = {nrec} := by decide +kernel
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := block.terminal n hn
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := block.radius n hn y hy0 hy1 hc C Z r hf
theorem disjoint_paid : Disjoint {BASE}.paidIDs newIDs := by decide +kernel
theorem disjoint_sharp : Disjoint newIDs Patch120SharpDispatch.sharpIDs := by decide +kernel
end
end N11Formalization.{AGG}
#check @N11Formalization.{AGG}.new_count
#check @N11Formalization.{AGG}.new_radius
#print axioms N11Formalization.{AGG}.new_radius
#print axioms N11Formalization.{AGG}.new_count
"""
outputs.append(new(AGG + ".lean", text))

text = f"""import N11Formalization.{BASE}
import N11Formalization.{AGG}

/-! {npaid} actual energy terminals on the SAME closed truechart: the
{SPEC['base_paid']} previously paid plus the {nrec} `{SPEC['tag']}` HOST packets.
`RemainingTerminalRadius` is still explicit and UNPROVED, but it now quantifies
over {nrem} terminals instead of {SPEC['total_terminals'] - SPEC['base_paid']}. -/
set_option autoImplicit false
namespace N11Formalization.{DISP}
open N11Formalization SourceChartIsometry ResumeNetwork
noncomputable section

def paidIDs : Finset (Fin 5011) :=
  {BASE}.paidIDs ∪ {AGG}.newIDs
theorem paid_count : paidIDs.card = {npaid} := by
  rw [paidIDs, Finset.card_union_of_disjoint {AGG}.disjoint_paid,
    {BASE}.paid_count, {AGG}.new_count]
theorem new_disjoint_old :
    Disjoint {BASE}.paidIDs {AGG}.newIDs :=
  {AGG}.disjoint_paid
theorem paid_not_sharp : Disjoint paidIDs Patch120SharpDispatch.sharpIDs := by
  rw [paidIDs]
  exact Finset.disjoint_union_left.mpr
    ⟨{BASE}.paid_not_sharp, {AGG}.disjoint_sharp⟩
theorem paid_terminal (n : Fin 5011) (hn : n∈paidIDs) :
    (DBMSourceTree.data n).terminal=true := by
  have h : n∈{BASE}.paidIDs ∨ n∈{AGG}.newIDs := by
    simpa only [paidIDs,Finset.mem_union] using hn
  rcases h with h | h
  · exact {BASE}.paid_terminal n h
  · exact {AGG}.new_terminal n h
theorem paid_radius (n : Fin 5011) (hn : n∈paidIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0 ≤ y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : Feasible (chartAnchors y) C Z r) : SourceExactRoot.sourceRadius < r := by
  have h : n∈{BASE}.paidIDs ∨ n∈{AGG}.newIDs := by
    simpa only [paidIDs,Finset.mem_union] using hn
  rcases h with h | h
  · exact {BASE}.paid_radius n h y hy0 hy1 hc C Z r hf
  · exact {AGG}.new_radius n h y hy0 hy1 hc C Z r hf

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

/-- Credit transfer: a residual here pays the previous dispatch's residual. -/
theorem remaining_of : RemainingTerminalRadius → {BASE}.RemainingTerminalRadius := by
  intro h n ht hs he y hy0 hy1 hc C Z r hf
  by_cases hp : n∈paidIDs
  · exact (paid_radius n hp y hy0 hy1 hc C Z r hf).le
  · exact h n ht hs hp y hy0 hy1 hc C Z r hf

end
end N11Formalization.{DISP}
#check @N11Formalization.{DISP}.paid_count
#check @N11Formalization.{DISP}.paid_radius
#check @N11Formalization.{DISP}.chart_radius_of_remaining
#check @N11Formalization.{DISP}.remaining_of
#print axioms N11Formalization.{DISP}.paid_radius
#print axioms N11Formalization.{DISP}.remaining_of
"""
outputs.append(new(DISP + ".lean", text))

text = f"""import N11Formalization.C450ChainCompletionMain
import N11Formalization.{DISP}
import N11Formalization.ActualMetricClassReduction
import N11Formalization.{SPEC['base_main']}

/-! Conditional main statement with the energy premise weakened to
`{DISP}.RemainingTerminalRadius` ({nrem} terminals). -/
set_option autoImplicit false
namespace N11Formalization.{MAIN}
noncomputable section

theorem main_of_energy_and_seven_classes
    (henergy : {DISP}.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  {SPEC['base_main']}.{SPEC['base_main_theorem']} ({DISP}.remaining_of henergy) hclasses

theorem full_disk_bound_of_energy_and_seven_classes
    (henergy : {DISP}.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → SourceExactRoot.sourceRadius ≤ r :=
  (strongInterface_of_n11_main (main_of_energy_and_seven_classes henergy hclasses)).bounds

end
end N11Formalization.{MAIN}
#check @N11Formalization.{MAIN}.main_of_energy_and_seven_classes
#print axioms N11Formalization.{MAIN}.main_of_energy_and_seven_classes
"""
outputs.append(new(MAIN + ".lean", text))

print("emitted", len(outputs), "modules;", nrec, "packets;", npaid, "paid;", nrem, "remaining")
mf = here / SPEC["manifest"]
with mf.open("x", encoding="utf-8", newline="\n") as f:
    json.dump({"level": "DRAFT ONLY; every Valid/module/root/probe gate pending",
               "spec": SPEC, "proposal_sha256": sha(PROPOSAL),
               "n_records": nrec, "n_groups": len(groups),
               "ids": [r["id"] for r in records], "outputs": outputs}, f, indent=2)
print("manifest", mf.name)
