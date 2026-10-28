"""Generate the stage-1 probe for the next505 emission.

The probe is deliberately an `import N11Formalization` file: it can only see the
new names if the ROOT source actually imports `EnergyTerminalBatchB12Main`, so
the same file doubles as the anti-stale-olean control (arm A/B/C).

Content:
  * full printed types of the aggregate / dispatch / main consumers,
  * one `#print axioms` per emitted H module (25),
  * `#print axioms` for the aggregate and dispatch theorems,
  * real negative controls closed by `decide +kernel` (count is exact) and by
    `Valid.beta_sum` (the checker is not vacuous).
"""
from pathlib import Path

here = Path(__file__).resolve().parent
proj = here.parents[1]
lean = proj / "lean"

n_modules = 25
lines = []
lines.append("import N11Formalization")
lines.append("")
lines.append("/-! Stage-1 probe for the `next505` energy emission. Run ONLY after the root")
lines.append("build that imports `EnergyTerminalBatchB12Main`; the identical file is the")
lines.append("stale-olean control (it must FAIL when the root import is reverted). -/")
lines.append("")
lines.append("namespace ProbeEnergyNext505")
lines.append("")
lines.append("-- 1. types of the aggregate, the dispatch and the conditional main consumer")
for name in [
    "Paid16GeneralNext505.new_count",
    "Paid16GeneralNext505.new_radius",
    "EnergyTerminalBatchB12.paid_count",
    "EnergyTerminalBatchB12.paid_radius",
    "EnergyTerminalBatchB12.chart_radius_of_remaining",
    "EnergyTerminalBatchB12.remaining_of_b12",
    "EnergyTerminalBatchB12Main.main_of_energy_b12_and_seven_classes",
    "EnergyTerminalBatchB12Main.full_disk_bound_of_energy_and_b12_placeholder",
]:
    if "placeholder" in name:
        continue
    lines.append(f"#check @N11Formalization.{name}")
lines.append("")
lines.append("-- 2. per-module axiom sweep (25 emitted packet modules)")
for k in range(1, n_modules + 1):
    lines.append(f"#print axioms N11Formalization.Paid16GeneralH{k:02}.all_valid")
lines.append("")
lines.append("-- 3. aggregate / dispatch / main axiom reports")
for name in [
    "Paid16GeneralNext505.new_count",
    "Paid16GeneralNext505.new_radius",
    "EnergyTerminalBatchB12.paid_radius",
    "EnergyTerminalBatchB12.remaining_of_b12",
    "EnergyTerminalBatchB12Main.main_of_energy_b12_and_seven_classes",
]:
    lines.append(f"#print axioms N11Formalization.{name}")
lines.append("")
lines.append("-- 4. negative controls: the paid count is EXACT, and `Valid` is not vacuous")
lines.append("example : N11Formalization.EnergyTerminalBatchB12.paidIDs.card = 815 := by")
lines.append("  decide +kernel")
lines.append("example : ¬ (N11Formalization.EnergyTerminalBatchB12.paidIDs.card = 814) := by")
lines.append("  decide +kernel")
lines.append("example : ¬ (N11Formalization.Paid16GeneralNext505.newIDs.card = 504) := by")
lines.append("  decide +kernel")
lines.append("example : ¬ (N11Formalization.EnergyTerminalBatchB11.paidIDs.card =")
lines.append("    N11Formalization.EnergyTerminalBatchB12.paidIDs.card) := by")
lines.append("  decide +kernel")
lines.append("/-- A packet with all weights zero violates `Valid.beta_sum`, so the checker")
lines.append("rejects it: `Valid` is not a vacuous predicate. -/")
lines.append("example : ¬ N11Formalization.Paid16CellCertificate.Valid")
lines.append("    { N11Formalization.Paid16GeneralH01.packet 0 with beta := fun _ => 0 } := by")
lines.append("  intro h")
lines.append("  have hs := h.beta_sum")
lines.append("  simp only [Finset.sum_const_zero] at hs")
lines.append("  norm_num at hs")
lines.append("")
lines.append("end ProbeEnergyNext505")

text = "\n".join(lines) + "\n"
path = lean / "ProbeEnergyNext505.lean"
if path.exists():
    assert path.read_text(encoding="utf-8") == text, "probe differs"
    print("reused", path.name)
else:
    with path.open("x", encoding="utf-8", newline="\n") as f:
        f.write(text)
    print("wrote", path.name, len(text), "bytes")
