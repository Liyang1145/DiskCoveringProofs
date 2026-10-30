#!/usr/bin/env python3
"""Emit the checked B13 descent-bound source from its finite block layout.

The B09 correction is explicit: 27 legacy ids are at or above the Next1182
lower bound, so they cannot be discarded by a false `< 2565` theorem.  The
generated proof excludes each such id from all 57 literal Next1182 blocks.
"""
from pathlib import Path

root = Path("n11-work/lean/N11Formalization")
high_ids = (2661, 2675, 2880, 2888, 2962, 2971, 2973, 3121, 3134, 3436,
            3591, 3601, 3619, 3833, 3834, 3842, 3852, 3874, 3950, 3965,
            4058, 4179, 4265, 4266, 4267, 4348, 4485)
blocks = [(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7),
          (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 15),
          (3, 16), (3, 17), (3, 18), (3, 19), (3, 20), (3, 21), (3, 22), (3, 23),
          (4, 24), (4, 25), (4, 26), (4, 27), (4, 28), (4, 29), (4, 30), (4, 31),
          (5, 32), (5, 33), (5, 34), (5, 35), (5, 36), (5, 37), (5, 38), (5, 39),
          (6, 40), (6, 41), (6, 42), (6, 43), (6, 44), (6, 45), (6, 46), (6, 47),
          (7, 48), (7, 49), (7, 50), (7, 51), (7, 52), (7, 53), (7, 54), (7, 55),
          (8, 56)]
assert len(high_ids) == 27 and len(set(high_ids)) == 27
assert len(blocks) == 57 and len({i for _, i in blocks}) == 57

lines = [f"import N11Formalization.Paid16GeneralG{i:02d}" for i in range(1, 13)]
lines += [
    "import N11Formalization.EnergyTerminalBatchB10",
    "import N11Formalization.EnergyTerminalBatchB11",
    "import N11Formalization.Paid16GeneralRemaining210",
    "import N11Formalization.Paid16GeneralNext1182",
    "",
    "/-! Bounded descent facts used by B13. Image-valued blocks are decoded by",
    "`mem_image` and `fin_cases`; B09 is classified through its nine union/insert",
    "layers, and the 210-id remainder is assembled from ten 21-id blocks. -/",
    "set_option autoImplicit false",
    "namespace N11Formalization.EnergyTerminalBatchB13DescentBounds",
    "open Finset",
    "noncomputable section",
    "",
]
for i in range(1, 13):
    name = f"Paid16GeneralG{i:02d}"
    lines += [
        f"private theorem g{i:02d}_lt (n : Fin 5011) (hn : n ∈ {name}.newIDs) :",
        "    n.val < 2565 := by",
        "  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩",
        f"  fin_cases i <;> norm_num [{name}.nodeID]",
        "",
    ]

lines += [
    "/-- B09 is not wholly below 2565: `b09HighIDs` lists its 27 legacy ids at or",
    "above 2565.  This exhaustive classification replaces the false former `b09_lt`",
    "statement. -/",
    "def b09HighIDs : Finset (Fin 5011) := {" + ",".join(map(str, high_ids)) + "}",
    "",
    "private theorem dispatch_bound (n : Fin 5011)",
    "    (hn : n ∈ EnergyTerminalDispatch.paidIDs) :",
    "    n.val < 2565 ∨ n ∈ b09HighIDs := by",
    "  rw [EnergyTerminalDispatch.paidIDs] at hn",
    "  rcases Finset.mem_union.mp hn with hn | hn",
    "  · have h : n = 284 ∨ n = 562 ∨ n = 4348 := by",
    "      simpa only [EnergyCommonChart.paidEnergyIDs, Finset.mem_insert,",
    "        Finset.mem_singleton] using hn",
    "    rcases h with rfl | rfl | rfl <;> simp [b09HighIDs]",
    "  · simp only [Finset.mem_singleton] at hn",
    "    rcases hn with rfl",
    "    simp [b09HighIDs]",
    "",
]

for theorem, module, packet in (
    ("lambda0_bound", "Lambda0Batch7Consumer", "Lambda0Batch7Packet"),
    ("chord_bound", "Lambda0TangentChordC01Consumer", "Lambda0TangentChordC01Packet"),
    ("cutting_bound", "CuttingPlaneBatch7Consumer", "CuttingPlaneBatch7Packet"),
    ("batch22_bound", "Paid16Batch22Consumer", "Paid16Batch22Packet"),
):
    lines += [
        f"private theorem {theorem} (n : Fin 5011)",
        f"    (hn : n ∈ {module}.newIDs) :",
        "    n.val < 2565 ∨ n ∈ b09HighIDs := by",
        "  rcases Finset.mem_image.mp hn with ⟨i, _, rfl⟩",
        f"  fin_cases i <;> simp [{packet}.nodeID, b09HighIDs]",
        "",
    ]

lines += [
    "private theorem b01_bound (n : Fin 5011)",
    "    (hn : n ∈ EnergyTerminalBatchB01.paidIDs) :",
    "    n.val < 2565 ∨ n ∈ b09HighIDs := by",
    "  rw [EnergyTerminalBatchB01.paidIDs] at hn",
    "  rcases Finset.mem_union.mp hn with hn | hn",
    "  · exact dispatch_bound n hn",
    "  · simp only [Finset.mem_insert, Finset.mem_singleton] at hn",
    "    rcases hn with rfl | rfl <;> simp [b09HighIDs]",
    "",
    "private theorem b02_bound (n : Fin 5011)",
    "    (hn : n ∈ EnergyTerminalBatchB02.paidIDs) :",
    "    n.val < 2565 ∨ n ∈ b09HighIDs := by",
    "  rw [EnergyTerminalBatchB02.paidIDs] at hn",
    "  rcases Finset.mem_union.mp hn with hn | hn",
    "  · exact b01_bound n hn",
    "  · simp only [Finset.mem_singleton] at hn",
    "    rcases hn with rfl",
    "    simp [b09HighIDs]",
    "",
    "private theorem b03_bound (n : Fin 5011)",
    "    (hn : n ∈ EnergyTerminalBatchB03.paidIDs) :",
    "    n.val < 2565 ∨ n ∈ b09HighIDs := by",
    "  rw [EnergyTerminalBatchB03.paidIDs] at hn",
    "  rcases Finset.mem_union.mp hn with hn | hn",
    "  · exact b02_bound n hn",
    "  · exact lambda0_bound n hn",
    "",
    "private theorem b04_bound (n : Fin 5011)",
    "    (hn : n ∈ EnergyTerminalBatchB04.paidIDs) :",
    "    n.val < 2565 ∨ n ∈ b09HighIDs := by",
    "  rw [EnergyTerminalBatchB04.paidIDs] at hn",
    "  rcases Finset.mem_union.mp hn with hn | hn",
    "  · exact b03_bound n hn",
    "  · exact chord_bound n hn",
    "",
    "private theorem b05_bound (n : Fin 5011)",
    "    (hn : n ∈ EnergyTerminalBatchB05.paidIDs) :",
    "    n.val < 2565 ∨ n ∈ b09HighIDs := by",
    "  rw [EnergyTerminalBatchB05.paidIDs] at hn",
    "  rcases Finset.mem_union.mp hn with hn | hn",
    "  · exact b04_bound n hn",
    "  · exact cutting_bound n hn",
    "",
    "private theorem b06_bound (n : Fin 5011)",
    "    (hn : n ∈ EnergyTerminalBatchB06.paidIDs) :",
    "    n.val < 2565 ∨ n ∈ b09HighIDs := by",
    "  rw [EnergyTerminalBatchB06.paidIDs] at hn",
    "  rcases Finset.mem_insert.mp hn with rfl | hn",
    "  · simp [b09HighIDs]",
    "  · exact b05_bound n hn",
    "",
    "private theorem b07_bound (n : Fin 5011)",
    "    (hn : n ∈ EnergyTerminalBatchB07.paidIDs) :",
    "    n.val < 2565 ∨ n ∈ b09HighIDs := by",
    "  rw [EnergyTerminalBatchB07.paidIDs] at hn",
    "  rcases Finset.mem_insert.mp hn with rfl | hn",
    "  · simp [b09HighIDs]",
    "  · rcases Finset.mem_insert.mp hn with rfl | hn",
    "    · simp [b09HighIDs]",
    "    · exact b06_bound n hn",
    "",
    "private theorem b08_bound (n : Fin 5011)",
    "    (hn : n ∈ EnergyTerminalBatchB08.paidIDs) :",
    "    n.val < 2565 ∨ n ∈ b09HighIDs := by",
    "  rw [EnergyTerminalBatchB08.paidIDs] at hn",
    "  rcases Finset.mem_insert.mp hn with rfl | hn",
    "  · simp [b09HighIDs]",
    "  · exact b07_bound n hn",
    "",
    "theorem b09_bound (n : Fin 5011) (hn : n ∈ EnergyTerminalBatchB09.paidIDs) :",
    "    n.val < 2565 ∨ n ∈ b09HighIDs := by",
    "  rw [EnergyTerminalBatchB09.paidIDs] at hn",
    "  rcases Finset.mem_union.mp hn with hn | hn",
    "  · exact b08_bound n hn",
    "  · exact batch22_bound n hn",
    "",
    "theorem first42_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralFirst42.newIDs) :",
    "    n.val < 2565 := by",
    "  rw [Paid16GeneralFirst42.newIDs] at hn",
    "  rcases Finset.mem_union.mp hn with hn | hn",
    "  · exact g01_lt n hn",
    "  · exact g02_lt n hn",
    "",
    "theorem b10_bound (n : Fin 5011) (hn : n ∈ EnergyTerminalBatchB10.paidIDs) :",
    "    n.val < 2565 ∨ n ∈ b09HighIDs := by",
    "  rw [EnergyTerminalBatchB10.paidIDs] at hn",
    "  rcases Finset.mem_union.mp hn with hn | hn",
    "  · exact b09_bound n hn",
    "  · exact Or.inl (first42_lt n hn)",
    "",
    "theorem remaining210_lt (n : Fin 5011)",
    "    (hn : n ∈ Paid16GeneralRemaining210.newIDs) : n.val < 2565 := by",
    "  have hm : n ∈ Paid16GeneralG03.newIDs ∨",
]
lines += [f"      n ∈ Paid16GeneralG{i:02d}.newIDs ∨" for i in range(4, 12)]
lines += [
    "      n ∈ Paid16GeneralG12.newIDs := by",
    "    simpa only [Paid16GeneralRemaining210.newIDs, Finset.mem_union] using hn",
    "  rcases hm with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn",
]
lines += [f"  · exact g{i:02d}_lt n hn" for i in range(3, 13)]
lines += [
    "",
    "",
    "theorem b11_bound (n : Fin 5011) (hn : n ∈ EnergyTerminalBatchB11.paidIDs) :",
    "    n.val < 2565 ∨ n ∈ b09HighIDs := by",
    "  rw [EnergyTerminalBatchB11.paidIDs] at hn",
    "  rcases Finset.mem_union.mp hn with hn | hn",
    "  · exact b10_bound n hn",
    "  · exact Or.inl (remaining210_lt n hn)",
    "",
]

group_starts = {1: 0, 2: 8, 3: 16, 4: 24, 5: 32, 6: 40, 7: 48, 8: 56}
for group in range(1, 9):
    count = 8 if group < 8 else 1
    names = [f"Paid16GeneralNext1182S{group:02d}.mem_ids{group_starts[group] + j:02d}"
             for j in range(count)]
    simp = [f"Paid16GeneralNext1182S{group:02d}.new_mem"] + names
    lines += [
        f"private theorem high_not_next_s{group:02d} (n : Fin 5011)",
        f"    (hn : n ∈ b09HighIDs) : n ∉ Paid16GeneralNext1182S{group:02d}.newIDs := by",
        "  simp only [b09HighIDs, Finset.mem_insert, Finset.mem_singleton] at hn",
        "  rcases hn with " + " | ".join("rfl" for _ in high_ids),
    ]
    for _ in high_ids:
        lines += [
            "  · intro h",
            "    simp only [" + ", ".join(simp) + "] at h",
            "    simp only [Fin.ext_iff] at h",
            "    omega",
        ]
    lines.append("")

lines += [
    "/-- Every B09 id above 2565 is absent from the 57 literal Next1182 blocks.",
    "The proof is split by part so no one tactic expands more than 168 literals. -/",
    "theorem high_not_next (n : Fin 5011) (hn : n ∈ b09HighIDs) :",
    "    n ∉ Paid16GeneralNext1182.newIDs := by",
    "  rw [Paid16GeneralNext1182.new_mem]",
    "  rintro (h | h | h | h | h | h | h | h)",
]
lines += [f"  · exact high_not_next_s{group:02d} n hn h" for group in range(1, 9)]

lines += [
    "",
    "end",
    "end N11Formalization.EnergyTerminalBatchB13DescentBounds",
    "#check @N11Formalization.EnergyTerminalBatchB13DescentBounds.b09_bound",
    "#check @N11Formalization.EnergyTerminalBatchB13DescentBounds.b11_bound",
    "#check @N11Formalization.EnergyTerminalBatchB13DescentBounds.remaining210_lt",
    "#print axioms N11Formalization.EnergyTerminalBatchB13DescentBounds.b09_bound",
    "#print axioms N11Formalization.EnergyTerminalBatchB13DescentBounds.b11_bound",
    "#print axioms N11Formalization.EnergyTerminalBatchB13DescentBounds.remaining210_lt",
]
target = root / "EnergyTerminalBatchB13DescentBounds.lean"
target.write_text("\n".join(lines) + "\n", encoding="utf-8")
print("wrote", target)
