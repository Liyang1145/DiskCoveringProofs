"""Batch emitter: ONE C450 segment per invocation, parameterized by c450Segs index.

Derived from the VALIDATED pilot emitter (evidence/c450-emit-20261014/emit_c450_source13.py,
itself derived from evidence/codex-handoff/emit_c450_seventh_grouped.py, left byte-identical).
The emission template is identical to the pilot's, which gated green end to end.

TWO-PARAMETER CHAIN BOOKKEEPING (the pilot's own off-by-one, made structurally
impossible to repeat). For c450Segs index k:
    MODNUM    = k + 1                  module is C450Source{k+1}
    PRED_NS   = C450Source{k}Segment   predecessor in the chain
    PRED_DROP = k                      ONLY names the split theorem: source{k}_remaining_split
    OWN_DROP  = k + 1                  own remainingSegs := c450Segs.drop (k+1)
Conflating PRED_DROP with OWN_DROP aliases the predecessor's own remainingSegs and
makes the split claim FALSE (Lean refutes it via `decide`). Two separate names.

BOTH PACKET JSONS. c450-grouped-remaining8-35-host.json covers c450Segs[7..34]
(JSON segment == index+1). c450Segs[35] is ONLY in c450-grouped-pilot-packets-host.json
(JSON segment 36). A one-file driver would silently drop the last segment.

Fresh-only: every target must not exist. --index K emits exactly K's 34 files.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess

ROOT_CURRENT = "F6E3419A258B0AFC0B62CB50317661D3BCC5A9538AE5A0FA4037918366B0FCE0"

ap = argparse.ArgumentParser()
ap.add_argument("--index", type=int, required=True,
                help="c450Segs index k to emit (13..35 for the batch)")
ap.add_argument("--dry-run", action="store_true")
args = ap.parse_args()

k = args.index
assert 13 <= k <= 35, f"batch covers indices 13..35, got {k}"

here = Path(__file__).resolve().parent
project = here.parents[1]
base = project / "lean/N11Formalization"
handoff = project / "evidence/codex-handoff"

JSON_SEG = k + 1
MODNUM = k + 1
NAME = f"C450Source{MODNUM}"
PRED_NS = f"C450Source{k}Segment"
PRED_DROP = k
OWN_DROP = k + 1
REMAINING = 36 - OWN_DROP

# ---- both JSONs: pick by JSON segment ----
REMAINING_JSON = handoff / "c450-grouped-remaining8-35-host.json"
PILOT_JSON = handoff / "c450-grouped-pilot-packets-host.json"
if JSON_SEG <= 35:
    proposal, proposal_sha = REMAINING_JSON, \
        "5ABF3DC52437370016C6C1D7897639B48F03044042140A85409905DC0B908B4C"
else:
    proposal, proposal_sha = PILOT_JSON, \
        "20CE7F8F9CFCB189995B2E0EBEEC9E3EC1B0180D56A934BB171AC6AB7FD75102"

data = base / "DSHTenBoundaryData.lean"
root_file = project / "lean/N11Formalization.lean"

guards = {
    data: "7422651456707C1CCB795A744907114B8A94A7A47338DD3EF562C57C64375B84",
    base / "C450GroupedAmplitude.lean":
        "E14BC072E3DC1ABD23D03F1133EBAA477139B15B8D6662AD7BD063840ACBBB5A",
    base / "C450GroupedPacketKernel.lean":
        "CEBA292455C980C6B68F70507996D4DE8F80EBF4604DB575B1B964D49D748E44",
    base / "C450GroupedClosedAssembly.lean":
        "370BE7A47DFC346319C8EFFD593C280D84EC99E592A6335105EB6E4ABA6845A1",
    root_file: ROOT_CURRENT,
    handoff / "ACCEPTANCE-CX081.json":
        "1CD4B52DAD7E65D181E1A1BF299C0BEE09EBE3AEC1437F1EC2A63720478618EC",
    REMAINING_JSON: "5ABF3DC52437370016C6C1D7897639B48F03044042140A85409905DC0B908B4C",
    PILOT_JSON: "20CE7F8F9CFCB189995B2E0EBEEC9E3EC1B0180D56A934BB171AC6AB7FD75102",
}
for path, sha in guards.items():
    got = hashlib.sha256(path.read_bytes()).hexdigest().upper()
    assert got == sha, f"GUARD FAIL {path}\n  pinned {sha}\n  on disk {got}"
print(f"GUARDS OK ({len(guards)} pinned files match disk)", flush=True)

idle = subprocess.run(["pwsh", "-NoProfile", "-Command",
    "if (@(Get-Process lean,lake -ErrorAction SilentlyContinue).Count) {exit 1}"],
    capture_output=True)
assert idle.returncode == 0, "No emission during live Lean"

doc = json.loads(proposal.read_text(encoding="utf-8"))
row = next((r for r in doc["results"] if r["segment"] == JSON_SEG), None)
assert row is not None, f"JSON segment {JSON_SEG} absent from {proposal.name}"
assert len(row["branches"]) == 32, "expected 32 branches"
fields = {kk: Q(v) for kk, v in row["source_fields"].items()}
source_rows = re.findall(r"\{\s*eLo\s*:=.*?\}", data.read_text(encoding="utf-8"), re.S)
assert len(source_rows) == 36
for key, value in fields.items():
    match = re.search(rf"\b{key}\s*:=\s*\(\s*(-?\d+)\s*:\s*ℚ\s*\)(?:\s*/\s*(\d+))?",
                      source_rows[k])
    assert match and Q(int(match[1]), int(match[2] or "1")) == value, \
        f"source_fields mismatch for {key} at c450Segs[{k}]"
# eLo/eHi must equal row k's span
sp = re.search(r"\{\s*eLo\s*:=.*?\}", source_rows[k], re.S).group(0)
grab = lambda key: (lambda m: Q(int(m.group(1)), int(m.group(2) or "1")))(
    re.search(rf"\b{key}\s*:=\s*\(\s*(-?\d+)\s*:\s*ℚ\s*\)(?:\s*/\s*(\d+))?", sp))
assert (fields["eLo"], fields["eHi"]) == (grab("eLo"), grab("eHi")), \
    f"span mismatch: json {fields['eLo']},{fields['eHi']} vs disk {grab('eLo')},{grab('eHi')}"

names = [f"{NAME}GroupedC{i+1:02}" for i in range(32)]
targets = [base / (n + ".lean") for n in names]
targets += [base / f"{NAME}Data.lean", base / f"{NAME}Segment.lean",
            here / f"c450-source{MODNUM}-grouped-draft-manifest.json"]
missing = [p for p in targets if p.exists()]
assert not missing, f"Fresh-only emission violated: {missing[:3]}"
assert all(p.resolve().is_relative_to(project.resolve()) for p in targets)

TOTAL = row["totalPackets"]
print(f"SEG k={k} json={JSON_SEG} module={NAME} pred={PRED_NS} "
      f"predDrop={PRED_DROP} ownDrop={OWN_DROP} remaining={REMAINING} "
      f"packets={TOTAL} json_file={proposal.name}", flush=True)
if args.dry_run:
    print("DRY RUN: no files written")
    raise SystemExit(0)


def literal(value, ty="ℚ"):
    v = Q(value)
    return f"({v.numerator}:{ty})" if v.denominator == 1 else \
        f"(({v.numerator}:{ty})/{v.denominator})"


def write_new(path, text):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text)
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


source_args = ",".join(literal(fields[key]) for key in
    ("eLo", "eHi", "a0", "a1", "a2", "a3", "b0", "b1", "b2", "b3"))
text = f"""import N11Formalization.C450GroupedClosedAssembly
import N11Formalization.DSHTenBoundaryData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.{NAME}Data
def source{MODNUM} : TenSeg := ⟨{source_args}⟩
theorem source_eq : c450Segs[{k}]? = some source{MODNUM} := by decide +kernel
theorem source_mem : source{MODNUM} ∈ c450Segs := by decide +kernel
theorem nn0 : |source{MODNUM}.a1|+|source{MODNUM}.a2|+|source{MODNUM}.a3| ≤ source{MODNUM}.a0 := by decide +kernel
theorem nn1 : |source{MODNUM}.b1|+|source{MODNUM}.b2|+|source{MODNUM}.b3| ≤ source{MODNUM}.b0 := by decide +kernel
theorem eHi_le : source{MODNUM}.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.{NAME}Data
#print axioms N11Formalization.{NAME}Data.source_eq
#print axioms N11Formalization.{NAME}Data.nn0
#print axioms N11Formalization.{NAME}Data.nn1
"""
data_sha = write_new(base / f"{NAME}Data.lean", text)

outputs = []
q_end = Q(-1)
for branch, name in zip(row["branches"], names):
    j, records = branch["cell"], branch["records"]
    qlo, qhi = Q(branch["qLo"]), Q(branch["qHi"])
    assert j == len(outputs) and qlo == q_end and qhi - qlo == Q(1, 16)
    q_end = qhi
    assert len(records) == branch["count"]
    assert Q(records[0]["lo"]) == Q(31, 50) and Q(records[-1]["hi"]) == Q(69, 50)
    assert all(Q(a["hi"]) == Q(b["lo"]) for a, b in zip(records, records[1:]))
    assert all(all(p["checks"].values()) and Q(p["gap"]) > 0 for p in records)
    assert all(abs(Q(p["p0"])) <= fields["a0"] and abs(Q(p["p1"])) <= fields["b0"]
               for p in records)
    q_literal = f"⟨{literal(qlo)},{literal(qhi)}⟩"
    text = f"""import N11Formalization.{NAME}Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.{name}
open C450GroupedPacketKernel C450GroupedClosedAssembly {NAME}Data
def Qcell : RatInterval := {q_literal}
"""
    for i, p in enumerate(records):
        vals = [p["lo"], p["hi"], qlo, qhi, p["ellLo"], p["ellHi"], p["vLo"], p["vHi"],
                p["zLo"], p["zHi"], p["qt"], p["qb"], p["p0"], p["p1"]]
        text += f"""def packet{i} : Packet := ⟨{",".join(literal(v) for v in vals)}⟩
theorem valid{i} : Valid source{MODNUM} packet{i} := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf{i} :
    CellBound source{MODNUM} nn0 nn1 Qcell {literal(p["lo"])} {literal(p["hi"])} :=
  cell_of_packet source{MODNUM} nn0 nn1 packet{i} valid{i}
"""
    joins = []

    def join(lo, hi):
        if hi - lo == 1:
            return f"leaf{lo}"
        mid = (lo + hi) // 2
        left, right = join(lo, mid), join(mid, hi)
        label = f"node{lo}_{hi}"
        joins.append(f"""private theorem {label} :
    CellBound source{MODNUM} nn0 nn1 Qcell {literal(records[lo]["lo"])} {literal(records[hi-1]["hi"])} :=
  cell_join {left} {right}
""")
        return label

    label = join(0, len(records))
    text += "".join(joins)
    text += f"""theorem bound : CellBound source{MODNUM} nn0 nn1 Qcell (31/50) (69/50) := {label}
def packets : List Packet := [{",".join(f"packet{i}" for i in range(len(records)))}]
theorem packet_count : packets.length = {len(records)} := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.{name}
#check @N11Formalization.{name}.bound
"""
    text += "".join(f"#print axioms N11Formalization.{name}.valid{i}\n" for i in range(len(records)))
    text += f"""#print axioms N11Formalization.{name}.bound
#print axioms N11Formalization.{name}.endpoint_checks
"""
    sha = write_new(base / (name + ".lean"), text)
    outputs.append(dict(file=str((base / (name + ".lean")).relative_to(project)),
                        sha256=sha, cell=j, count=len(records),
                        qLo=str(qlo), qHi=str(qhi)))
assert q_end == 1

text = f"import N11Formalization.{PRED_NS}\n"
text += "".join(f"import N11Formalization.{name}\n" for name in names)
text += f"""import N11Formalization.C450FirstRadialKernel
/-! Actual source{MODNUM} full grouped closed certificate draft.
No source/root acceptance claimed by the file comment. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.{NAME}Segment
open C450GroupedPacketKernel C450GroupedClosedAssembly {NAME}Data C450NormalizedInterface
abbrev Case := Fin 32
"""
text += "def Qs : Case → RatInterval := ![" + ",".join(n + ".Qcell" for n in names) + "]\n"
text += "private def DirectionPaid (q : ℝ) : Prop := ∃ i : Case, RatInterval.Mem (Qs i) q\n"
for i, b in enumerate(row["branches"]):
    text += f"""private theorem direction{i} :
    ∀ q ∈ Set.Icc {literal(b["qLo"], "ℝ")} {literal(b["qHi"], "ℝ")}, DirectionPaid q := by
  intro q hq
  refine ⟨{i},?_⟩
  simpa [Qs,{names[i]}.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
"""
joins = []


def direction_join(lo, hi):
    if hi - lo == 1:
        return f"direction{lo}"
    mid = (lo + hi) // 2
    left, right = direction_join(lo, mid), direction_join(mid, hi)
    label = f"directions{lo}_{hi}"
    joins.append(f"""private theorem {label} :
    ∀ q ∈ Set.Icc {literal(row["branches"][lo]["qLo"], "ℝ")}
      {literal(row["branches"][hi-1]["qHi"], "ℝ")}, DirectionPaid q :=
  C450FirstRadialKernel.interval_join {left} {right}
""")
    return label


label = direction_join(0, 32)
text += "".join(joins)
text += f"""theorem directions_cover : DirectionsCover Qs := {label}
theorem cells_paid (i : Case) : CellBound source{MODNUM} nn0 nn1 (Qs i) (31/50) (69/50) := by
  fin_cases i
"""
text += "".join(f"  · exact {name}.bound\n" for name in names)
text += f"""theorem source{MODNUM}_paid : SegmentNormalized source{MODNUM} := by
  intro h0 h1
  exact normalized_of_cells source{MODNUM} h0 h1 eHi_le Qs directions_cover cells_paid
def allPackets : List Packet := """ + " ++ ".join(n + ".packets" for n in names) + "\n"
text += f"""theorem packet_count : allPackets.length = {TOTAL} := by decide +kernel
def remainingSegs : List TenSeg := c450Segs.drop {OWN_DROP}
theorem remaining_count : remainingSegs.length = {REMAINING} := by decide +kernel
theorem source{PRED_DROP}_remaining_split : {PRED_NS}.remainingSegs = source{MODNUM} :: remainingSegs := rfl
def RemainingSourceObligation : Prop := ∀ s ∈ remainingSegs, SegmentNormalized s
theorem source{PRED_DROP}_remaining_of_remaining (hr : RemainingSourceObligation) :
    {PRED_NS}.RemainingSourceObligation := by
  intro s hs
  rw [source{PRED_DROP}_remaining_split] at hs
  simp only [List.mem_cons] at hs
  rcases hs with hnext | hrest
  · rw [hnext]
    exact source{MODNUM}_paid
  · exact hr s hrest
theorem source_of_remaining (hr : RemainingSourceObligation) : SourceObligation :=
  {PRED_NS}.source_of_remaining (source{PRED_DROP}_remaining_of_remaining hr)
theorem atom_of_remaining (hr : RemainingSourceObligation) : C450Atom :=
  atom_of_source (source_of_remaining hr)
end N11Formalization.{NAME}Segment
#check @N11Formalization.{NAME}Segment.source{MODNUM}_paid
#check @N11Formalization.{NAME}Segment.atom_of_remaining
#print axioms N11Formalization.{NAME}Segment.directions_cover
#print axioms N11Formalization.{NAME}Segment.cells_paid
#print axioms N11Formalization.{NAME}Segment.source{MODNUM}_paid
#print axioms N11Formalization.{NAME}Segment.source{PRED_DROP}_remaining_of_remaining
"""
consumer_sha = write_new(base / f"{NAME}Segment.lean", text)
manifest = dict(level="DRAFT ONLY; batch emission pending root/import acceptance",
    segment_json=JSON_SEG, c450Segs_index=k, module=NAME,
    pred_ns=PRED_NS, pred_drop=PRED_DROP, own_drop=OWN_DROP, remaining=REMAINING,
    data=dict(file=f"lean/N11Formalization/{NAME}Data.lean", sha256=data_sha),
    outputs=outputs, totalPackets=TOTAL,
    proposal=proposal.name, proposalSHA256=proposal_sha,
    consumer=dict(file=f"lean/N11Formalization/{NAME}Segment.lean", sha256=consumer_sha),
    guards={str(p.relative_to(project)): s for p, s in guards.items()},
    actualSourceFields=row["source_fields"])
write_new(here / f"c450-source{MODNUM}-grouped-draft-manifest.json",
          json.dumps(manifest, indent=2))
print(f"EMITTED k={k} {NAME} data={data_sha[:16]} consumer={consumer_sha[:16]}", flush=True)
