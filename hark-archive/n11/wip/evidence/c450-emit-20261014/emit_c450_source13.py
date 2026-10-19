"""PILOT: mechanical emission of ONE C450 segment, c450Segs[12] (JSON segment 13).

Derived from evidence/codex-handoff/emit_c450_seventh_grouped.py (11072 B,
2026-10-04), which is left BYTE-IDENTICAL. This copy changes exactly two things:

  1. GUARDS. The root guard is re-pinned from the stale 1EC5D032... to the
     current root 4F470AF5...; a guard for the remaining-segments packet JSON is
     ADDED. The other four file guards are carried over UNCHANGED and are
     re-verified against disk at run time.
  2. TARGET. Segment 7 -> segment 13 (== c450Segs[12], the first unpaid one),
     with the naming convention module-number = c450Segs-index + 1, i.e.
     C450Source13{Data,GroupedC01..C32,Segment}.

`--no-repin` runs the SAME script with the ORIGINAL stale root hash, as the
negative control proving the root guard is real and the re-pin is load-bearing.

Fresh-only: every target must not exist. Nothing outside
lean/N11Formalization/C450Source13*.lean and this directory is written.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess

ROOT_STALE = "1EC5D03204874E8DE429CD1450E3F4F5A61D2D76AE55AAE71156D9AF7A61C035"
ROOT_CURRENT = "4F470AF507F320488DFBC168F9AE39645904AF569AE46B9FFB8F5E520BC5EDAF"

ap = argparse.ArgumentParser()
ap.add_argument("--no-repin", action="store_true",
                help="negative control: keep the stale root guard")
ap.add_argument("--dry-run", action="store_true")
ap.add_argument("--repair-segment", action="store_true",
                help="re-emit ONLY the Segment module (Data+32 grouped already green). "
                     "Requires the broken Segment to have been moved aside first.")
args = ap.parse_args()

here = Path(__file__).resolve().parent
project = here.parents[1]                      # ...\n11-formalization
base = project / "lean/N11Formalization"
handoff = project / "evidence/codex-handoff"

JSON_SEG = 13            # == c450Segs index 12 + 1
SEG_INDEX = 12           # c450Segs index
MODNUM = 13              # module number == c450Segs index + 1  (convention)
NAME = f"C450Source{MODNUM}"
PRED_NS = "C450Source12Segment"      # predecessor in the chain
PRED_DROP = SEG_INDEX                # only used to NAME the split theorem: source12_remaining_split
# The drop amount is SEG_INDEX + 1, NOT SEG_INDEX. Getting this wrong aliases the
# predecessor's own remainingSegs and makes the split claim FALSE:
#   drop 12 gives 24 elements == C450Source12Segment.remainingSegs, so the claim
#   "c450Segs.drop 12 = c450Segs[12] :: c450Segs.drop 12" is unsatisfiable, and
#   "remaining_count = 23" is refuted by `decide`.  (Caught by the pilot gate.)
OWN_DROP = SEG_INDEX + 1             # c450Segs.drop OWN_DROP
REMAINING = 36 - OWN_DROP            # 23

proposal = handoff / "c450-grouped-remaining8-35-host.json"
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
    root_file: ROOT_STALE if args.no_repin else ROOT_CURRENT,
    handoff / "ACCEPTANCE-CX081.json":
        "1CD4B52DAD7E65D181E1A1BF299C0BEE09EBE3AEC1437F1EC2A63720478618EC",
    proposal: "5ABF3DC52437370016C6C1D7897639B48F03044042140A85409905DC0B908B4C",
}
for path, sha in guards.items():
    got = hashlib.sha256(path.read_bytes()).hexdigest().upper()
    assert got == sha, f"GUARD FAIL {path}\n  pinned {sha}\n  on disk {got}"
print("GUARDS OK:", len(guards), "pinned files match disk")

idle = subprocess.run(["pwsh", "-NoProfile", "-Command",
    "if (@(Get-Process lean,lake -ErrorAction SilentlyContinue).Count) {exit 1}"],
    capture_output=True)
assert idle.returncode == 0, "No emission during live Lean"

doc = json.loads(proposal.read_text(encoding="utf-8"))
row = next(r for r in doc["results"] if r["segment"] == JSON_SEG)
assert len(row["branches"]) == 32
fields = {k: Q(v) for k, v in row["source_fields"].items()}
source_rows = re.findall(r"\{\s*eLo\s*:=.*?\}", data.read_text(encoding="utf-8"), re.S)
assert len(source_rows) == 36
for key, value in fields.items():
    match = re.search(rf"\b{key}\s*:=\s*\(\s*(-?\d+)\s*:\s*ℚ\s*\)(?:\s*/\s*(\d+))?",
                      source_rows[SEG_INDEX])
    assert match and Q(int(match[1]), int(match[2] or "1")) == value, key
assert (fields["eLo"], fields["eHi"]) == (Q(11, 250), Q(6, 125))

names = [f"{NAME}GroupedC{i+1:02}" for i in range(32)]
if args.repair_segment:
    # Data + 32 grouped modules are already emitted and gate GREEN; only the
    # Segment module is re-emitted (after the broken one is moved aside).
    targets = [base / f"{NAME}Segment.lean",
               here / f"c450-source{MODNUM}-grouped-repair-manifest.json"]
    assert all(not p.exists() for p in targets), "Fresh-only emission"
    assert all((base / (n + ".lean")).exists() for n in names), \
        "repair mode requires the 32 grouped modules already on disk"
    assert (base / f"{NAME}Data.lean").exists(), \
        "repair mode requires the Data module already on disk"
else:
    targets = [base / (n + ".lean") for n in names]
    targets += [base / f"{NAME}Data.lean", base / f"{NAME}Segment.lean",
                here / f"c450-source{MODNUM}-grouped-draft-manifest.json"]
assert all(not p.exists() for p in targets), "Fresh-only emission"
assert all(p.resolve().is_relative_to(project.resolve()) for p in targets)

TOTAL = row["totalPackets"]
print(f"segment json={JSON_SEG} c450Segs[{SEG_INDEX}] module={NAME} "
      f"packets={TOTAL} remaining={REMAINING}")
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
theorem source_eq : c450Segs[{SEG_INDEX}]? = some source{MODNUM} := by decide +kernel
theorem source_mem : source{MODNUM} ∈ c450Segs := by decide +kernel
theorem nn0 : |source{MODNUM}.a1|+|source{MODNUM}.a2|+|source{MODNUM}.a3| ≤ source{MODNUM}.a0 := by decide +kernel
theorem nn1 : |source{MODNUM}.b1|+|source{MODNUM}.b2|+|source{MODNUM}.b3| ≤ source{MODNUM}.b0 := by decide +kernel
theorem eHi_le : source{MODNUM}.eHi ≤ 7/50 := by decide +kernel
end N11Formalization.{NAME}Data
#print axioms N11Formalization.{NAME}Data.source_eq
#print axioms N11Formalization.{NAME}Data.nn0
#print axioms N11Formalization.{NAME}Data.nn1
"""
data_sha = write_new(base / f"{NAME}Data.lean", text) if not args.repair_segment else \
    hashlib.sha256((base / f"{NAME}Data.lean").read_bytes()).hexdigest().upper()

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
    target = base / (name + ".lean")
    if args.repair_segment:
        sha = hashlib.sha256(target.read_bytes()).hexdigest().upper()
    else:
        sha = write_new(target, text)
    outputs.append(dict(file=str(target.relative_to(project)), sha256=sha, cell=j,
                        count=len(records), qLo=str(qlo), qHi=str(qhi)))
    print(("WROTE" if not args.repair_segment else "KEPT"), name, len(records), sha, flush=True)
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
#print axioms N11Formalization.{NAME}Segment.atom_of_remaining
"""
consumer_sha = write_new(base / f"{NAME}Segment.lean", text)
_mname = (f"c450-source{MODNUM}-grouped-repair-manifest.json" if args.repair_segment
          else f"c450-source{MODNUM}-grouped-draft-manifest.json")
manifest = dict(level="DRAFT ONLY;source13/root/import acceptance pending",
    segment_json=JSON_SEG, c450Segs_index=SEG_INDEX, module=NAME,
    shared=dict(file="lean/N11Formalization/C450GroupedClosedAssembly.lean",
                sha256=guards[base / "C450GroupedClosedAssembly.lean"]),
    data=dict(file=f"lean/N11Formalization/{NAME}Data.lean", sha256=data_sha),
    outputs=outputs, totalPackets=TOTAL,
    proposalSHA256=guards[proposal],
    consumer=dict(file=f"lean/N11Formalization/{NAME}Segment.lean", sha256=consumer_sha),
    guards={str(p.relative_to(project)): s for p, s in guards.items()},
    repinned_root=dict(old=ROOT_STALE, new=ROOT_CURRENT) if not args.no_repin else None,
    actualSourceFields=row["source_fields"])
write_new(here / _mname, json.dumps(manifest, indent=2))
print("DRAFT consumer", consumer_sha)
