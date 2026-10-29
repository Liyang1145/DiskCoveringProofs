#!/usr/bin/env python3
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
src = (ROOT / "n11-work/lean/N11Formalization/Paid16GeneralNext505.lean").read_text()
blocks = []
for name, body in re.findall(r"def (ids\d+) : Finset \(Fin 5011\) := \{([^}]*)\}", src):
    vals = [int(x) for x in body.split(",") if x.strip()]
    assert vals and len(vals) <= 21 and all(v < 2565 for v in vals), (name, len(vals))
    blocks.append((name, vals))
assert [n for n, _ in blocks] == [f"ids{i:02}" for i in range(25)]
assert sum(len(vals) for _, vals in blocks) == 505

out = [
    "import N11Formalization.Paid16GeneralNext505",
    "",
    "/-! Literal bounds for the 505 pre-2565 ids. Each block has at most 21 ids. -/",
    "set_option autoImplicit false",
    "namespace N11Formalization.EnergyTerminalBatchB13Next505Bounds",
    "open Finset",
    "noncomputable section",
    "",
]
for name, vals in blocks:
    out += [
        f"private theorem {name}_lt (n : Fin 5011)",
        f"    (h : n ∈ Paid16GeneralNext505.{name}) : n.val < 2565 := by",
        f"  rcases (Paid16GeneralNext505.mem_{name} n).mp h with "
        + " | ".join("rfl" for _ in vals),
        "  all_goals norm_num",
    ]
out += [
    "",
    "theorem next505_lt (n : Fin 5011) (hn : n ∈ Paid16GeneralNext505.newIDs) :",
    "    n.val < 2565 := by",
    "  rcases (Paid16GeneralNext505.new_mem n).mp hn with "
    + " | ".join(f"h{i}" for i in range(len(blocks))),
]
for i, (name, _) in enumerate(blocks):
    out.append(f"  · exact {name}_lt n h{i}")
out += [
    "",
    "end",
    "end N11Formalization.EnergyTerminalBatchB13Next505Bounds",
    "",
    "#check @N11Formalization.EnergyTerminalBatchB13Next505Bounds.next505_lt",
    "#print axioms N11Formalization.EnergyTerminalBatchB13Next505Bounds.next505_lt",
    "",
]
dst = ROOT / "n11-work/lean/N11Formalization/EnergyTerminalBatchB13Next505Bounds.lean"
dst.write_text("\n".join(out))
print(f"wrote {dst}: {len(blocks)} blocks, 505 ids, max block {max(len(v) for _, v in blocks)}")
