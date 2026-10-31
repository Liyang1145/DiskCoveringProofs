#!/usr/bin/env python3
"""Split the 373-id residual census into ten-index kernel decisions."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PATH = ROOT / "lean/N11Formalization/EnergyTerminalBatchB13RefineSixteenResidualCensus.lean"
text = PATH.read_text()
marker = "private theorem mem_sub_000" if "private theorem mem_sub_000" in text else "private theorem disjoint_chunk0_1"
head = text[:text.index(marker)]
tail = text[text.index("theorem residualIDs_eq_residual373 :"):]
head = head.replace("    chunk0_card, chunk1_card, chunk2_card, chunk3_card]\n  norm_num\n",
                    "    chunk0_card, chunk1_card, chunk2_card, chunk3_card]\n")
assert "  norm_num\n" not in head

P = ("n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔\n"
     "      n ∈ residual373")
R = "EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff"

def sub(j: int) -> str:
    lo = 10 * j
    if j < 501:
        hi = lo + 10
        bounds = f"(hlo : {lo} ≤ n.val) (hhi : n.val < {hi})"
    else:
        bounds = "(hlo : 5010 ≤ n.val) (hhi : n.val < 5011)"
    return f"""private theorem mem_sub_{j:03d} (n : Fin 5011)
    {bounds} :
    {P} := by
  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [{R}] <;> decide +kernel +revert
"""

def block(i: int) -> str:
    if i < 50:
        lo = 100 * i
        bounds = f"(n : Fin 5011)\n    (hlo : {lo} ≤ n.val) (hhi : n.val < {lo + 100})"
        ranges = [f"({10*j} ≤ n.val ∧ n.val < {10*j+10})" for j in range(10*i+1, 10*i+10)]
        cover = f"n.val < {10*i+10} ∨ " + " ∨ ".join(ranges)
        pats = " | ".join(f"h{r}" for r in range(10))
        proof = [f"  · exact mem_sub_{10*i:03d} n hlo h0"]
        proof += [f"  · exact mem_sub_{10*i+r:03d} n h{r}.1 h{r}.2" for r in range(1,10)]
    else:
        bounds = "(n : Fin 5011) (hlo : 5000 ≤ n.val)"
        cover = "n.val < 5010 ∨ n.val = 5010"
        pats = "h0 | h1"
        proof = ["  · exact mem_sub_500 n hlo h0",
                 "  · exact mem_sub_500 n hlo (by omega)"]
        # The second goal must use the dedicated final singleton theorem.
        proof[1] = "  · exact mem_sub_500 n (by omega) n.isLt"
    return f"""theorem mem_iff_block{i:02d}
    {bounds} :
    {P} := by
  have hcases : {cover} := by omega
  rcases hcases with {pats}
""" + "\n".join(proof) + "\n\n"

# The last block needs distinct names: sub 500 is the singleton, sub 501 does not exist.
# Rewrite the generated final block body explicitly.
def block50() -> str:
    return f"""theorem mem_iff_block50 (n : Fin 5011) (hlo : 5000 ≤ n.val) :
    {P} := by
  have hcases : n.val < 5010 ∨ n.val = 5010 := by omega
  rcases hcases with h0 | h1
  · exact mem_sub_500 n hlo h0
  · exact mem_sub_501 n (by omega) n.isLt

"""

chunks = [sub(j) for j in range(502)]
chunks += [block(i) for i in range(50)]
chunks += [block50()]
PATH.write_text(head + "".join(chunks) + tail)
print(f"wrote {PATH}: 502 ten-index/singleton subtheorems, 51 bounded block dispatches")
